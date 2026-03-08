//! Terminator translation for MIR → IR conversion.

use rustc_middle::mir::{self, Operand, TerminatorKind};
use rustc_middle::ty::{self, TypeVisitableExt};

use num_bigint::BigInt;
use tuffy_ir::instruction::Operand as IrOperand;
use tuffy_ir::instruction::{ICmpOp, Origin};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};

use super::ctx::TranslationCtx;
use super::types::*;

const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    pub(super) fn translate_terminator(&mut self, term: &mir::Terminator<'tcx>) {
        match &term.kind {
            TerminatorKind::Return => {
                // SRET: copy the constructed return value from local stack slot
                // to the SRET pointer, then return the pointer.
                if let Some(sret) = self.sret_ptr {
                    let ret_local = mir::Local::from_usize(0);
                    let local_slot = self.locals.get(ret_local).expect("sret local must be set");
                    let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
                    let ret_size = type_size(self.tcx, ret_mir_ty).unwrap_or(0);

                    // Copy from local slot to SRET pointer
                    let size_val = self.builder.iconst(
                        ret_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let align = 8; // TODO: compute proper alignment
                    let sret_annotated = IrOperand::annotated(sret, Annotation::Align(align));
                    let local_annotated =
                        IrOperand::annotated(local_slot, Annotation::Align(align));
                    let new_mem = self.builder.mem_copy(
                        sret_annotated.into(),
                        local_annotated.into(),
                        size_val.into(),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );

                    self.builder
                        .ret(Some(sret.into()), new_mem.into(), Origin::synthetic());
                    return;
                }

                let ret_local = mir::Local::from_usize(0);
                let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);

                if matches!(translate_ty(self.tcx, ret_mir_ty), Some(Type::Unit) | None) {
                    // Unit-returning or untranslatable return type: bare ret, no value.
                    self.builder
                        .ret(None, self.current_mem.into(), Origin::synthetic());
                } else if type_size(self.tcx, ret_mir_ty) == Some(0) {
                    // Zero-sized return type: return a dummy value to satisfy the
                    // function signature (translate_ty maps ADTs to Int).
                    let dummy =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.builder.ret(
                        Some(dummy.into()),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                } else if self.stack_locals.is_stack(ret_local)
                    && matches!(
                        self.locals
                            .get(ret_local)
                            .and_then(|v| self.builder.value_type(v).cloned()),
                        Some(Type::Ptr(_))
                    )
                {
                    // Stack-allocated return (e.g., 16-byte struct built via Aggregate).
                    // Load the actual data from the stack slot instead of returning
                    // the slot address (which would be a dangling pointer).
                    let slot = self
                        .locals
                        .get(ret_local)
                        .expect("return local _0 must be set");
                    let ret_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
                    let size = type_size(self.tcx, ret_ty).unwrap_or(8);

                    // Load the first word from the stack slot.
                    // Use the actual type size (clamped to 8) so that sub-word
                    // types (u8, u16, etc.) emit a correctly-sized load instead
                    // of reading garbage bytes beyond the stored value.
                    let load_size = size.min(8) as u32;
                    let load_ty = translate_ty(self.tcx, ret_mir_ty).unwrap_or(default_int_type());
                    let ann = translate_annotation(ret_mir_ty);
                    let word0 = self.builder.load(
                        slot.into(),
                        load_size,
                        load_ty,
                        self.current_mem.into(),
                        ann,
                        Origin::synthetic(),
                    );

                    // Coerce to match declared return type (e.g., Ptr for &T returns).
                    let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty);
                    let coerced_word0 = match ret_ir_ty {
                        Some(Type::Ptr(_)) => self.coerce_to_ptr(word0),
                        _ => word0,
                    };

                    if size > 8 {
                        // Two-register return (9-16 bytes): load second word
                        // and mark it for RDX via ABI metadata.
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let hi_addr =
                            self.builder
                                .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                        let word1 = self.builder.load(
                            hi_addr.into(),
                            8,
                            default_int_type(),
                            self.current_mem.into(),
                            int_annotation_for_bytes(8),
                            Origin::synthetic(),
                        );
                        let ret_inst = self.builder.ret(
                            Some(coerced_word0.into()),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        self.abi_metadata
                            .mark_secondary_return_move(ret_inst.index(), word1.index());
                    } else {
                        self.builder.ret(
                            Some(coerced_word0.into()),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }
                } else {
                    // Normal scalar return.
                    let val = self.locals.values[ret_local.as_usize()];
                    if let Some(v) = val {
                        // Coerce to match the declared return type.
                        let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty);
                        let coerced = match (ret_ir_ty, self.builder.value_type(v).cloned()) {
                            (Some(Type::Int), Some(Type::Ptr(_)))
                                if self.builder.is_memory_address(v) =>
                            {
                                // v is a pointer to data (e.g. symbol_addr for an
                                // indirect constant).  Load the actual value instead
                                // of converting the address to an integer.
                                let ret_size =
                                    type_size(self.tcx, ret_mir_ty).unwrap_or(8).min(8) as u32;

                                self.builder.load(
                                    v.into(),
                                    ret_size,
                                    default_int_type(),
                                    self.current_mem.into(),
                                    int_annotation_for_bytes(ret_size),
                                    Origin::synthetic(),
                                )
                            }
                            (Some(Type::Int), _) => self.coerce_to_int(v),
                            (Some(Type::Ptr(_)), _) => self.coerce_to_ptr(v),
                            (Some(Type::Bool), Some(Type::Int)) => {
                                let zero = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .icmp(ICmpOp::Ne, v.into(), zero.into(), Origin::synthetic())
                                    .raw()
                            }
                            (Some(Type::Float(ft)), Some(Type::Int)) => {
                                // Float value was carried as Int bits — reinterpret.
                                self.builder.bitcast(
                                    v.into(),
                                    Type::Float(ft),
                                    None,
                                    Origin::synthetic(),
                                )
                            }
                            _ => v,
                        };
                        self.builder.ret(
                            Some(coerced.into()),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    } else {
                        // Return local was never assigned — return a dummy
                        // value.  This can happen in custom MIR where the
                        // return place is left uninitialised (the value is
                        // garbage but the function must still return).
                        let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty);
                        let dummy = if matches!(ret_ir_ty, Some(Type::Ptr(_))) {
                            let zero = self.builder.iconst(
                                0,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .inttoptr(zero.into(), 0, Origin::synthetic())
                                .raw()
                        } else if let Some(Type::Float(ft)) = ret_ir_ty {
                            let zero = self.builder.iconst(
                                0,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder.bitcast(
                                zero.into(),
                                Type::Float(ft),
                                None,
                                Origin::synthetic(),
                            )
                        } else if matches!(ret_ir_ty, Some(Type::Bool)) {
                            self.builder.bconst(false, Origin::synthetic()).raw()
                        } else {
                            self.builder
                                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                                .raw()
                        };
                        self.builder.ret(
                            Some(dummy.into()),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }
                }
            }
            TerminatorKind::Goto { target } => {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.translate_switch_int(discr, targets);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // Assert: if cond != expected, trap. Otherwise branch to target.
                let cond_val = self.translate_operand(cond);
                let target_block = self.block_map.get(*target);
                if let Some(cond_v) = cond_val {
                    let cond_v = self.coerce_to_int(cond_v);
                    let expected_val = self.builder.iconst(
                        if *expected { 1 } else { 0 },
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let cmp = self.builder.icmp(
                        ICmpOp::Eq,
                        cond_v.into(),
                        expected_val.into(),
                        Origin::synthetic(),
                    );
                    // Create a trap block for the failure path.
                    let trap_block = self.builder.create_block();
                    let _trap_mem = self.builder.add_block_arg(trap_block, Type::Mem, None);
                    self.builder.brif(
                        cmp.into(),
                        target_block,
                        vec![self.current_mem.into()],
                        trap_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                    self.builder.switch_to_block(trap_block);
                    self.builder.trap(Origin::synthetic());
                } else {
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                }
            }
            TerminatorKind::Unreachable => {
                self.builder.unreachable(Origin::synthetic());
            }
            TerminatorKind::Drop { place, target, .. } => {
                let drop_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                let drop_ty = self.monomorphize(drop_ty);
                let target_block = self.block_map.get(*target);

                // Only emit drop glue when the type actually needs dropping.
                if drop_ty.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) {
                    // Trait object drops: dispatch through vtable[0] instead of
                    // calling drop_in_place directly (which would recurse).
                    if matches!(drop_ty.kind(), ty::Dynamic(..)) {
                        // The place is `*local` where local is a fat pointer
                        // (data ptr + vtable ptr). Get both components.
                        let base_local = place.local;
                        let data_ptr = self.locals.get(base_local);
                        let vtable_ptr = self.fat_locals.get(base_local);
                        if let (Some(data), Some(vtable)) = (data_ptr, vtable_ptr) {
                            // Load drop function pointer from vtable[0].
                            let drop_fn = self.builder.load(
                                vtable.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let (call_mem, _) = self.builder.call(
                                drop_fn.into(),
                                vec![data.into()],
                                Type::Unit,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            self.current_mem = call_mem;
                        }
                    } else {
                        let drop_instance = ty::Instance::resolve_drop_in_place(self.tcx, drop_ty);
                        self.referenced_instances.push(drop_instance);
                        if !drop_instance.args.has_non_region_param() {
                            let sym_name = self.tcx.symbol_name(drop_instance).name.to_string();
                            let sym_id = self.symbols.intern(&sym_name);
                            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());

                            // Get a pointer to the place being dropped.
                            let drop_ptr = if place.projection.is_empty() {
                                if self.stack_locals.is_stack(place.local) {
                                    self.locals.get(place.local)
                                } else if let Some(v) = self.locals.get(place.local) {
                                    // Non-stack local: the value IS the pointer
                                    // (e.g. a Box or reference).  For types that
                                    // need dropping and are stored as a register
                                    // value, we need to spill to a stack slot so
                                    // drop_in_place gets a valid &mut T.
                                    let ty_size = type_size(self.tcx, drop_ty).unwrap_or(8);
                                    if let Some(fat_val) = self.fat_locals.get(place.local) {
                                        // Fat pointer (Box<dyn Trait>, &[T], etc.):
                                        // spill both data ptr and metadata to a
                                        // 16-byte stack slot so drop_in_place
                                        // receives a valid &mut FatPtr.
                                        let slot = self.builder.stack_slot(16, Origin::synthetic());
                                        self.current_mem = self
                                            .builder
                                            .store(
                                                v.into(),
                                                slot.into(),
                                                8,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            )
                                            .raw();
                                        let off8 = self.builder.iconst(
                                            8,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        );
                                        let hi = self.builder.ptradd(
                                            slot.into(),
                                            off8.into(),
                                            0,
                                            Origin::synthetic(),
                                        );
                                        self.current_mem = self
                                            .builder
                                            .store(
                                                fat_val.into(),
                                                hi.into(),
                                                8,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            )
                                            .raw();
                                        Some(slot)
                                    } else if ty_size > 8
                                        || matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                                    {
                                        Some(v)
                                    } else {
                                        let slot = self
                                            .builder
                                            .stack_slot(ty_size as u32, Origin::synthetic());
                                        self.current_mem = self
                                            .builder
                                            .store(
                                                v.into(),
                                                slot.into(),
                                                ty_size as u32,
                                                self.current_mem.into(),
                                                Origin::synthetic(),
                                            )
                                            .raw();
                                        Some(slot)
                                    }
                                } else {
                                    // ZST with no stored value — use a
                                    // dangling aligned pointer so
                                    // drop_in_place is still called.
                                    let align = self
                                        .tcx
                                        .layout_of(
                                            ty::TypingEnv::fully_monomorphized()
                                                .as_query_input(drop_ty),
                                        )
                                        .map(|l| l.align.abi.bytes())
                                        .unwrap_or(1);
                                    Some(
                                        self.builder
                                            .iconst(
                                                align as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    )
                                }
                            } else {
                                self.translate_place_to_addr(place)
                                    .map(|(a, _)| self.coerce_to_ptr(a))
                            };

                            if let Some(ptr) = drop_ptr {
                                let (call_mem, _) = self.builder.call(
                                    callee.into(),
                                    vec![ptr.into()],
                                    Type::Unit,
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                self.current_mem = call_mem;
                            }
                        }
                    }
                }

                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_block = self.block_map.get(*real_target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                self.translate_call(func, args, destination, target, term.source_info);
            }
            TerminatorKind::InlineAsm { targets, .. } => {
                // Inline assembly is not supported — treat as a no-op and
                // branch to the first target block (the normal destination).
                // This is enough for identity functions like `black_box` that
                // use asm only as an optimisation barrier.
                if let Some(&target) = targets.first() {
                    let target_block = self.block_map.get(target);
                    self.builder.br(
                        target_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                } else {
                    self.builder.trap(Origin::synthetic());
                }
            }
            _ => {
                // For any unhandled terminator (including Resume, Yield, etc.),
                // treat as a trap since we don't support exception handling
                // or async/generator constructs yet.
                self.builder.trap(Origin::synthetic());
            }
        }
    }

    pub(super) fn translate_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
    ) {
        // Get the discriminant type's byte size so we can truncate switch
        // target values to the correct bit width.  MIR stores switch values
        // as u128, but the runtime discriminant is stored in a sized slot
        // (e.g. 32-bit for i32) and zero-extended on load.
        let discr_ty = self.operand_ty_mono(discr);
        let discr_bits = discr_ty
            .and_then(|t| type_size(self.tcx, t))
            .map(|sz| sz * 8)
            .unwrap_or(64);

        let mut discr_val = match self.translate_operand(discr) {
            Some(v) => v,
            None => {
                // The discriminant local has no value yet (e.g. defined in a
                // later MIR block that hasn't been translated).  Use zero as
                // a conservative default — this is correct for the common
                // case of `is_val_statically_known` (always false/0).
                // TODO: process blocks in reverse post-order to avoid this.
                self.builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw()
            }
        };

        // If the discriminant is a pointer, it may be:
        // (a) an integer type > 8 bytes whose address was returned by
        //     translate_place_to_value — load the actual integer value, or
        // (b) a nullable-pointer-optimised discriminant — convert to integer.
        // Bool discriminants need BoolToInt for icmp.
        if matches!(self.builder.value_type(discr_val), Some(Type::Ptr(_))) {
            let is_integer_discr = discr_ty.is_some_and(|t| t.is_integral());
            if is_integer_discr {
                let byte_size = discr_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(8) as u32;
                discr_val = self.builder.load(
                    discr_val.into(),
                    byte_size,
                    default_int_type(),
                    self.current_mem.into(),
                    int_annotation_for_bytes(byte_size),
                    Origin::synthetic(),
                );
            } else {
                discr_val = self
                    .builder
                    .ptrtoaddr(discr_val.into(), 64, Origin::synthetic())
                    .raw();
            }
        } else if matches!(self.builder.value_type(discr_val), Some(Type::Bool)) {
            let one = self
                .builder
                .iconst(1, 64, IntSignedness::Unsigned, Origin::synthetic());
            let zero = self
                .builder
                .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic());
            discr_val = self.builder.select(
                discr_val.into(),
                one.into(),
                zero.into(),
                Type::Int,
                Some(Annotation::Int(IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                })),
                Origin::synthetic(),
            );
        }

        // Mask the discriminant to its type's bit width so that a sign-extended
        // 64-bit register value matches the zero-extended switch target constants.
        if discr_bits < 64 {
            let mask_val = self.builder.iconst(
                (1i64 << discr_bits) - 1,
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            discr_val = self
                .builder
                .and(discr_val.into(), mask_val.into(), I64, Origin::synthetic())
                .raw();
        }

        let all_targets: Vec<_> = targets.iter().collect();
        let otherwise = targets.otherwise();

        if all_targets.is_empty() {
            // No explicit value-target pairs — unconditionally jump to otherwise.
            // This happens for single-variant enums where the discriminant check
            // is optimised away.
            let otherwise_block = self.block_map.get(otherwise);
            self.builder.br(
                otherwise_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else if all_targets.len() == 1 {
            // Two-way branch: compare discriminant with the single value.
            let (test_val, target_bb) = all_targets[0];
            // Truncate u128 switch value to discriminant bit width so it
            // matches the zero-extended runtime value loaded from a sized slot.
            let truncated = if discr_bits < 128 {
                test_val & ((1u128 << discr_bits) - 1)
            } else {
                test_val
            };
            let const_val = self.builder.iconst(
                BigInt::from(truncated),
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            let cmp = self.builder.icmp(
                ICmpOp::Eq,
                discr_val.into(),
                const_val.into(),
                Origin::synthetic(),
            );
            let then_block = self.block_map.get(target_bb);
            let else_block = self.block_map.get(otherwise);
            self.builder.brif(
                cmp.into(),
                then_block,
                vec![self.current_mem.into()],
                else_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        } else {
            // Multi-way: chain of brif comparisons with fallthrough blocks.
            let otherwise_block = self.block_map.get(otherwise);
            for (i, (test_val, target_bb)) in all_targets.iter().enumerate() {
                let truncated = if discr_bits < 128 {
                    *test_val & ((1u128 << discr_bits) - 1)
                } else {
                    *test_val
                };
                let const_val = self.builder.iconst(
                    BigInt::from(truncated),
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let cmp = self.builder.icmp(
                    ICmpOp::Eq,
                    discr_val.into(),
                    const_val.into(),
                    Origin::synthetic(),
                );
                let then_block = self.block_map.get(*target_bb);

                if i == all_targets.len() - 1 {
                    // Last comparison: else goes to otherwise.
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        otherwise_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                } else {
                    // Not last: else falls through to a new comparison block.
                    let next_block = self.builder.create_block();
                    let next_mem = self.builder.add_block_arg(next_block, Type::Mem, None);
                    self.builder.brif(
                        cmp.into(),
                        then_block,
                        vec![self.current_mem.into()],
                        next_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );
                    self.builder.switch_to_block(next_block);
                    self.current_mem = next_mem;
                }
            }
        }
    }
}
