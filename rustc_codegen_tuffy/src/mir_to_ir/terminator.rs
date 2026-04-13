//! Terminator translation for MIR → IR conversion.

use rustc_hir::LangItem;
use rustc_middle::mir::{self, AssertKind, InlineAsmOperand, Operand, TerminatorKind};
use rustc_middle::ty::{self, Instance, TypeVisitableExt, TypingEnv};

use num_bigint::BigInt;
use tuffy_ir::instruction::{ICmpOp, Origin};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::*;

/// Shared 64-bit unsigned annotation used for synthesized integer terminator values.
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers one MIR terminator into Tuffy IR control flow.
    pub(super) fn translate_terminator(&mut self, term: &mir::Terminator<'tcx>) {
        match &term.kind {
            TerminatorKind::Return => {
                self.translate_return();
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
                msg,
                target,
                ..
            } => {
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
                    let panic_block = self.builder.create_block();
                    let panic_mem = self.builder.add_block_arg(panic_block, Type::Mem, None);
                    self.builder.brif(
                        cmp.into(),
                        target_block,
                        vec![self.current_mem.into()],
                        panic_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );

                    // Build the panic call in the failure block.
                    self.builder.switch_to_block(panic_block);
                    self.current_mem = panic_mem;
                    self.emit_assert_panic(msg, term.source_info);
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
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => {
                self.translate_drop(place, *target, unwind);
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
                unwind,
                ..
            } => {
                let cleanup_bb = match unwind {
                    mir::UnwindAction::Cleanup(cleanup_bb) => Some(*cleanup_bb),
                    _ => None,
                };
                self.translate_call(
                    func,
                    args,
                    destination,
                    target,
                    cleanup_bb,
                    term.source_info,
                );
            }
            TerminatorKind::InlineAsm {
                template,
                operands,
                targets,
                ..
            } => {
                self.translate_inline_asm(template, operands, targets);
            }
            TerminatorKind::UnwindResume => {
                // Resume unwinding: load the exception pointer from the
                // stack slot (stored by the landing-pad wrapper) and call
                // `_Unwind_Resume(exc_ptr)` to continue stack unwinding.
                if let Some(exc_slot) = self.exc_ptr_slot {
                    let exc_ptr = self.builder.load(
                        exc_slot.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    let resume_sym = self.symbols.intern("_Unwind_Resume");
                    let resume_addr = self.builder.symbol_addr(resume_sym, Origin::synthetic());
                    let (_, _) = self.builder.call(
                        resume_addr.into(),
                        vec![exc_ptr.into()],
                        Type::Unit,
                        self.current_mem.into(),
                        None,
                        None,
                        Origin::synthetic(),
                    );
                }
                self.builder.unreachable(Origin::synthetic());
            }
            TerminatorKind::UnwindTerminate(_) => {
                // Terminate on double-panic: call core::panicking::panic_cannot_unwind.
                let def_id = self
                    .tcx
                    .require_lang_item(LangItem::PanicCannotUnwind, term.source_info.span);
                if let Some(instance) = Instance::try_resolve(
                    self.tcx,
                    TypingEnv::fully_monomorphized(),
                    def_id,
                    ty::List::empty(),
                )
                .ok()
                .flatten()
                {
                    let sym_name = self.tcx.symbol_name(instance).name.to_string();
                    let sym_id = self.symbols.intern(&sym_name);
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic()).raw();
                    let (_, _) = self.builder.call(
                        callee.into(),
                        vec![],
                        Type::Unit,
                        self.current_mem.into(),
                        None,
                        None,
                        Origin::synthetic(),
                    );
                }
                self.builder.trap(Origin::synthetic());
            }
            _ => {
                // For any unhandled terminator (including Resume, Yield, etc.),
                // treat as a trap since we don't support exception handling
                // or async/generator constructs yet.
                self.builder.trap(Origin::synthetic());
            }
        }
    }

    /// Create a landing-pad wrapper block for a call with unwind cleanup.
    ///
    /// The wrapper captures the exception pointer from the unwinder,
    /// stores it to the shared `exc_ptr_slot`, and branches to the
    /// actual MIR cleanup block.
    pub(super) fn setup_cleanup_landing_pad(&mut self, cleanup_bb: mir::BasicBlock) -> u32 {
        // Create the wrapper IR block (no block args — entered by unwinder).
        let wrapper_block = self.builder.create_block();

        // Defer wrapper block population to after the main translation loop.
        self.landing_pad_wrappers.push((wrapper_block, cleanup_bb));
        wrapper_block.index()
    }

    /// Handle an InlineAsm terminator.
    ///
    /// Tuffy cannot execute arbitrary inline assembly. Instead, we recognise
    /// well-known patterns from the standard library and emit equivalent IR:
    ///
    /// * **select_unpredictable** (`test` + `cmovnz`/`cmovz`): emit a
    ///   conditional `select`.
    /// * **black_box** / identity (`InOut` with same place): the existing
    ///   value is already in place — nothing to do.
    /// * **InOut with distinct output**: copy input value to output place.
    ///
    /// For any remaining `Out`-only operands with no recognised semantics,
    /// we store zero to avoid leaving the destination uninitialised.
    fn translate_inline_asm(
        &mut self,
        template: &[rustc_ast::InlineAsmTemplatePiece],
        operands: &[InlineAsmOperand<'tcx>],
        targets: &[mir::BasicBlock],
    ) {
        // Concatenate template strings for pattern matching.
        let template_str: String = template
            .iter()
            .filter_map(|piece| match piece {
                rustc_ast::InlineAsmTemplatePiece::String(s) => Some(s.as_ref()),
                _ => None,
            })
            .collect();

        // Collect In values and Out places by operand index.
        let mut in_vals: Vec<ValueRef> = Vec::new();
        let mut out_places: Vec<Option<&mir::Place<'tcx>>> = Vec::new();
        let mut inout_pairs: Vec<(ValueRef, Option<&mir::Place<'tcx>>)> = Vec::new();

        for op in operands {
            match op {
                InlineAsmOperand::In { value, .. } => {
                    if let Some(v) = self.translate_operand(value) {
                        in_vals.push(v);
                    }
                }
                InlineAsmOperand::Out { place, .. } => {
                    out_places.push(place.as_ref());
                }
                InlineAsmOperand::InOut {
                    in_value,
                    out_place,
                    ..
                } => {
                    let v = self.translate_operand(in_value);
                    if let Some(v) = v {
                        inout_pairs.push((v, out_place.as_ref()));
                    }
                }
                // Const, SymFn, SymStatic, Label — not relevant here.
                _ => {}
            }
        }

        // Pattern: select_unpredictable — "test" + "cmovnz" + "cmovz"
        // Operands: In(cond), In(true_val), In(false_val), Out(result)
        let is_select = (template_str.contains("cmovnz") || template_str.contains("cmovne"))
            && (template_str.contains("cmovz") || template_str.contains("cmove"))
            && in_vals.len() >= 3
            && !out_places.is_empty();

        if is_select {
            let cond = in_vals[0];
            let true_val = in_vals[1];
            let false_val = in_vals[2];

            // cond is a byte — compare != 0 to get a Bool.
            let cond_int = self.coerce_to_int(cond);
            let zero = self
                .builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
            let cond_bool = self.builder.icmp(
                ICmpOp::Ne,
                cond_int.into(),
                zero.into(),
                Origin::synthetic(),
            );

            // select(cond, true_val, false_val)
            let result_ty = self
                .builder
                .value_type(true_val)
                .cloned()
                .unwrap_or(Type::Ptr(0));
            let result = self.builder.select(
                cond_bool.into(),
                true_val.into(),
                false_val.into(),
                result_ty.clone(),
                None,
                Origin::synthetic(),
            );

            // Store result to each Out place.
            for place in out_places.iter().flatten() {
                self.store_val_to_place(result, place, &result_ty);
            }
        } else {
            // Handle InOut operands: copy input to output.
            for (in_val, out_place) in &inout_pairs {
                if let Some(place) = out_place {
                    let ty = self
                        .builder
                        .value_type(*in_val)
                        .cloned()
                        .unwrap_or(Type::Int);
                    self.store_val_to_place(*in_val, place, &ty);
                }
            }

            // For unrecognised Out-only operands, store zero to prevent UB.
            for place in out_places.iter().flatten() {
                let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
                let _sz = type_size(self.tcx, place_ty).unwrap_or(8);
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                self.store_val_to_place(zero.raw(), place, &Type::Int);
            }
        }

        // Branch to the normal destination (first target).
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

    /// Store an IR value to a MIR place (handles both register and stack locals).
    fn store_val_to_place(&mut self, val: ValueRef, place: &mir::Place<'tcx>, _ir_ty: &Type) {
        if place.projection.is_empty() {
            // Simple local — either set the register or store to the stack slot.
            if self.stack_locals.is_stack(place.local) {
                if let Some(slot) = self.locals.get(place.local) {
                    let place_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                    let bytes = type_size(self.tcx, place_ty).unwrap_or(8) as u32;
                    if bytes > 0 {
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                bytes.min(8),
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }
            } else {
                self.locals.set(place.local, val);
            }
        } else if let Some((addr, projected_ty)) = self.translate_place_to_addr(place) {
            let addr = self.coerce_to_ptr(addr);
            let dest_ty = self.monomorphize(projected_ty);
            let bytes = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
            if bytes > 0 {
                self.current_mem = self
                    .builder
                    .store(
                        val.into(),
                        addr.into(),
                        bytes.min(8),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
        }
    }

    /// Lowers MIR `Return`, including SRET and fat-pointer return conventions.
    fn translate_return(&mut self) {
        // SRET: copy the constructed return value from local stack slot
        // to the SRET pointer, then return the pointer.
        if let Some(sret) = self.sret_ptr {
            let ret_local = mir::Local::from_usize(0);
            let local_slot = self.locals.get(ret_local).expect("sret local must be set");

            // Safety check: if _0 already IS sret, skip the copy.
            if local_slot == sret {
                self.builder.ret(
                    Some(sret.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                return;
            }

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
            let sret_annotated =
                tuffy_ir::instruction::Operand::annotated(sret, Annotation::Align(align));
            let local_annotated =
                tuffy_ir::instruction::Operand::annotated(local_slot, Annotation::Align(align));
            let new_mem = self.builder.mem_copy(
                sret_annotated.into(),
                local_annotated.into(),
                size_val.into(),
                self.current_mem.into(),
                Origin::synthetic(),
            );

            self.builder
                .ret(Some(sret.into()), None, new_mem.into(), Origin::synthetic());
            return;
        }

        let ret_local = mir::Local::from_usize(0);
        let ret_mir_ty = self.monomorphize(self.mir.local_decls[ret_local].ty);
        let ret_size = type_size(self.tcx, ret_mir_ty).unwrap_or(0);

        if matches!(translate_ty(self.tcx, ret_mir_ty), Some(Type::Unit))
            || (translate_ty(self.tcx, ret_mir_ty).is_none() && ret_size == 0)
        {
            // Unit-returning or zero-sized untranslatable return type: bare ret, no value.
            self.builder
                .ret(None, None, self.current_mem.into(), Origin::synthetic());
        } else if ret_size == 0 {
            // Zero-sized return type: return a dummy value to satisfy the
            // function signature (translate_ty maps ADTs to Int).
            let dummy = self
                .builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
            self.builder.ret(
                Some(dummy.into()),
                None,
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
            let ret_repr = repr_kind(self.tcx, ret_ty);
            let is_scalar_pair = matches!(ret_repr, ReprKind::ScalarPair);

            // Load size: for Scalar returns load the full type width
            // (legalizer splits wide loads); for ScalarPair load only
            // the first scalar.
            let sp_info = if is_scalar_pair {
                scalar_pair_info(self.tcx, ret_ty)
            } else {
                None
            };
            let load_size = if let Some((a_sz, _, _)) = sp_info {
                a_sz as u32
            } else {
                size as u32
            };
            let load_ty = translate_ty(self.tcx, ret_mir_ty).unwrap_or(Type::Int);
            // For ScalarPair returns (e.g. fat pointers), use a
            // register-width annotation for the low-half load — but
            // only when the type is Int (not Ptr).
            let ann = if is_scalar_pair {
                if matches!(load_ty, Type::Ptr(_)) {
                    None
                } else {
                    int_annotation_for_bytes(load_size)
                }
            } else {
                translate_annotation(ret_mir_ty).or_else(|| {
                    if matches!(load_ty, Type::Int) {
                        int_annotation_for_bytes(load_size)
                    } else {
                        None
                    }
                })
            };
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

            if is_scalar_pair {
                // Two-register return (ScalarPair): load second scalar
                // and mark it for RDX via ABI metadata.
                let (_, b_sz, b_off) = sp_info.unwrap_or((size.min(8), size.saturating_sub(8), 8));
                let off_val = self.builder.iconst(
                    b_off as i64,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let hi_addr =
                    self.builder
                        .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic());
                let word1 = self.builder.load(
                    hi_addr.into(),
                    b_sz as u32,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(b_sz as u32),
                    Origin::synthetic(),
                );
                self.builder.ret(
                    Some(coerced_word0.into()),
                    Some(word1.into()),
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            } else {
                self.builder.ret(
                    Some(coerced_word0.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            }
        } else if let Some(fat_meta) = self.fat_locals.get(ret_local)
            && is_fat_ptr(self.tcx, ret_mir_ty)
        {
            // Non-stack fat pointer return (e.g. from an intrinsic
            // that set both locals and fat_locals directly).  Return
            // the data pointer in RAX and the metadata in RDX.
            let v = self
                .locals
                .get(ret_local)
                .expect("fat pointer return must have data_ptr");
            let coerced = self.coerce_to_ptr(v);
            self.builder.ret(
                Some(coerced.into()),
                Some(fat_meta.into()),
                self.current_mem.into(),
                Origin::synthetic(),
            );
        } else {
            // Normal scalar return.
            let val = self.locals.values[ret_local.as_usize()];
            if let Some(v) = val {
                // Coerce to match the declared return type.
                // Fall back to Type::Int for small aggregates (e.g.
                // [i8; 1]) that translate_ty maps to None — this
                // matches the function-signature logic in mod.rs.
                let part_bytes = self.target_part_bytes();
                let ret_ir_ty = translate_ty(self.tcx, ret_mir_ty).or(
                    if ret_size > 0 && ret_size <= part_bytes {
                        Some(Type::Int)
                    } else {
                        None
                    },
                );
                let coerced = match (ret_ir_ty, self.builder.value_type(v).cloned()) {
                    (Some(Type::Int), Some(Type::Ptr(_))) if self.builder.is_memory_address(v) => {
                        // v is a pointer to data (e.g. symbol_addr for an
                        // indirect constant).  Load the actual value instead
                        // of converting the address to an integer.
                        let ret_size = type_size(self.tcx, ret_mir_ty)
                            .unwrap_or(part_bytes)
                            .min(part_bytes) as u32;

                        self.builder.load(
                            v.into(),
                            ret_size,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(ret_size),
                            Origin::synthetic(),
                        )
                    }
                    // Aggregate type (tuple/struct) that translate_ty
                    // maps to None but fits in one ABI part. The function
                    // signature declares Int return; load the value from
                    // the constant/stack pointer.
                    (None, Some(Type::Ptr(_)))
                        if self.builder.is_memory_address(v)
                            && ret_size > 0
                            && ret_size <= part_bytes =>
                    {
                        let sz = ret_size.min(part_bytes) as u32;
                        self.builder.load(
                            v.into(),
                            sz,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(sz),
                            Origin::synthetic(),
                        )
                    }
                    (Some(Type::Int), Some(Type::Float(_))) => {
                        // Float returned as integer bits (e.g. to_le_bytes).
                        let sz = ret_size.min(8) as u32;
                        self.builder.bitcast(
                            v.into(),
                            Type::Int,
                            int_annotation_for_bytes(sz),
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
                        self.builder
                            .bitcast(v.into(), Type::Float(ft), None, Origin::synthetic())
                    }
                    _ => v,
                };
                self.builder.ret(
                    Some(coerced.into()),
                    None,
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
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.builder
                        .inttoptr(zero.into(), 0, Origin::synthetic())
                        .raw()
                } else if let Some(Type::Float(ft)) = ret_ir_ty {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    self.builder
                        .bitcast(zero.into(), Type::Float(ft), None, Origin::synthetic())
                } else if matches!(ret_ir_ty, Some(Type::Bool)) {
                    self.builder.bconst(false, Origin::synthetic()).raw()
                } else {
                    self.builder
                        .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw()
                };
                self.builder.ret(
                    Some(dummy.into()),
                    None,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            }
        }
    }

    /// Lowers a drop terminator into a call to the resolved drop glue.
    fn translate_drop(
        &mut self,
        place: &mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: &mir::UnwindAction,
    ) {
        let drop_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
        let drop_ty = self.monomorphize(drop_ty);
        let target_block = self.block_map.get(target);
        let cleanup_label = match unwind {
            mir::UnwindAction::Cleanup(cleanup_bb) => {
                Some(self.setup_cleanup_landing_pad(*cleanup_bb))
            }
            _ => None,
        };

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
                    // It may be NULL for types with no drop glue.
                    let drop_fn = self.builder.load(
                        vtable.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    // Null check: vtable drop can be null for
                    // trivially-droppable concrete types.
                    let drop_as_int =
                        self.builder
                            .ptrtoint(drop_fn.into(), 64, Origin::synthetic());
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic());
                    let is_nonnull = self.builder.icmp(
                        ICmpOp::Ne,
                        drop_as_int.into(),
                        zero.into(),
                        Origin::synthetic(),
                    );
                    let call_block = self.builder.create_block();
                    let call_mem_arg = self.builder.add_block_arg(call_block, Type::Mem, None);
                    let merge_block = self.builder.create_block();
                    let merge_mem_arg = self.builder.add_block_arg(merge_block, Type::Mem, None);

                    self.builder.brif(
                        is_nonnull.into(),
                        call_block,
                        vec![self.current_mem.into()],
                        merge_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );

                    // call_block: invoke the drop function
                    self.builder.switch_to_block(call_block);
                    let (call_mem, _) = self.builder.call(
                        drop_fn.into(),
                        vec![data.into()],
                        Type::Unit,
                        call_mem_arg.into(),
                        cleanup_label,
                        None,
                        Origin::synthetic(),
                    );
                    self.builder
                        .br(merge_block, vec![call_mem.into()], Origin::synthetic());

                    // Continue from merge_block
                    self.builder.switch_to_block(merge_block);
                    self.current_mem = merge_mem_arg;
                }
            } else {
                let drop_instance = ty::Instance::resolve_drop_in_place(self.tcx, drop_ty);
                self.referenced_instances.push(drop_instance);
                if !drop_instance.args.has_non_region_param() {
                    let sym_name = self.tcx.symbol_name(drop_instance).name.to_string();
                    let sym_id = self.symbols.intern(&sym_name);
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());

                    // Get a pointer to the place being dropped, plus
                    // optional metadata for unsized drops (*mut [T] etc.).
                    let (drop_ptr, drop_meta): (Option<ValueRef>, Option<ValueRef>) = if place
                        .projection
                        .is_empty()
                    {
                        if self.stack_locals.is_stack(place.local) {
                            (self.locals.get(place.local), None)
                        } else if let Some(v) = self.locals.get(place.local) {
                            // Non-stack local: the value IS the pointer
                            // (e.g. a Box or reference).  For types that
                            // need dropping and are stored as a register
                            // value, we need to spill to a stack slot so
                            // drop_in_place gets a valid &mut T.
                            let ty_size = type_size(self.tcx, drop_ty).unwrap_or(8);
                            if ty_size == 0 {
                                // ZST with a dummy register value —
                                // use a dangling aligned pointer so
                                // drop_in_place receives a well-aligned &mut T.
                                let align = self
                                    .tcx
                                    .layout_of(
                                        ty::TypingEnv::fully_monomorphized()
                                            .as_query_input(drop_ty),
                                    )
                                    .map(|l| l.align.abi.bytes())
                                    .unwrap_or(1);
                                (
                                    Some(
                                        self.builder
                                            .iconst(
                                                align as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    ),
                                    None,
                                )
                            } else if let Some(fat_val) = self.fat_locals.get(place.local) {
                                // Fat pointer: drop_in_place<[T]> / drop_in_place<dyn Trait>
                                // takes the fat pointer components as separate register
                                // arguments (data_ptr in rdi, metadata in rsi).
                                (Some(v), Some(fat_val))
                            } else if ty_size > self.target_part_bytes()
                                || matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                            {
                                (Some(v), None)
                            } else {
                                let slot =
                                    self.builder
                                        .stack_slot(ty_size as u32, 0, Origin::synthetic());
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
                                (Some(slot), None)
                            }
                        } else {
                            // ZST with no stored value — use a
                            // dangling aligned pointer so
                            // drop_in_place is still called.
                            let align = self
                                .tcx
                                .layout_of(
                                    ty::TypingEnv::fully_monomorphized().as_query_input(drop_ty),
                                )
                                .map(|l| l.align.abi.bytes())
                                .unwrap_or(1);
                            (
                                Some(
                                    self.builder
                                        .iconst(
                                            align as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        )
                                        .raw(),
                                ),
                                None,
                            )
                        }
                    } else {
                        let addr = self
                            .translate_place_to_addr(place)
                            .map(|(a, _)| self.coerce_to_ptr(a));
                        // For unsized drops through a Deref of a fat pointer
                        // (e.g. `(*_6)` where `_6: *const [T]`), the metadata
                        // (slice length / vtable ptr) lives in fat_locals and
                        // must be passed as the second register argument.
                        let meta = if !place.projection.is_empty()
                            && matches!(place.projection[0], mir::PlaceElem::Deref)
                        {
                            self.fat_locals.get(place.local)
                        } else {
                            None
                        };
                        (addr, meta)
                    };

                    if let Some(ptr) = drop_ptr {
                        let mut args = vec![ptr.into()];
                        if let Some(meta) = drop_meta {
                            args.push(meta.into());
                        }
                        let (call_mem, _) = self.builder.call(
                            callee.into(),
                            args,
                            Type::Unit,
                            self.current_mem.into(),
                            cleanup_label,
                            None,
                            Origin::synthetic(),
                        );
                        self.current_mem = call_mem.raw();
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

    /// Lowers a `SwitchInt` terminator into IR branch structure.
    pub(super) fn translate_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
    ) {
        // Get the discriminant type's byte size so we can truncate switch
        // target values to the correct bit width.  MIR stores switch values
        // as u128, but the runtime discriminant is stored in a sized slot
        // (e.g. 32-bit for i32) and zero-extended on load.
        // Use projected type so that e.g. `_x.1` where `_x: (u64, u128)`
        // yields `u128` rather than the whole tuple type.
        let discr_ty =
            operand_ty_projected(discr, self.mir, self.tcx).map(|t| self.monomorphize(t));
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
                    Type::Int,
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
                (discr_bits as u32).min(128),
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
                    (discr_bits as u32).min(128),
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

    /// Emit a call to the appropriate panic function for a failed Assert.
    fn emit_assert_panic(&mut self, msg: &AssertKind<Operand<'tcx>>, source_info: mir::SourceInfo) {
        let tcx = self.tcx;
        let location = self.make_caller_location(source_info);

        // Determine the lang item and build arguments.
        let (lang_item, args) = match msg {
            AssertKind::BoundsCheck { len, index } => {
                let mut call_args: Vec<tuffy_ir::instruction::Operand> = Vec::with_capacity(3);
                if let Some(idx) = self.translate_operand(index) {
                    let idx = self.coerce_to_int(idx);
                    call_args.push(idx.into());
                }
                if let Some(len_v) = self.translate_operand(len) {
                    let len_v = self.coerce_to_int(len_v);
                    call_args.push(len_v.into());
                }
                call_args.push(location.into());
                (LangItem::PanicBoundsCheck, call_args)
            }
            AssertKind::MisalignedPointerDereference { required, found } => {
                let mut call_args: Vec<tuffy_ir::instruction::Operand> = Vec::with_capacity(3);
                if let Some(req) = self.translate_operand(required) {
                    let req = self.coerce_to_int(req);
                    call_args.push(req.into());
                }
                if let Some(fnd) = self.translate_operand(found) {
                    let fnd = self.coerce_to_int(fnd);
                    call_args.push(fnd.into());
                }
                call_args.push(location.into());
                (LangItem::PanicMisalignedPointerDereference, call_args)
            }
            _ => {
                // All other assert kinds use panic_const_* functions
                // which take only the implicit #[track_caller] location.
                (msg.panic_function(), vec![location.into()])
            }
        };

        // Resolve the lang item to a function Instance and get its symbol.
        let def_id = tcx.require_lang_item(lang_item, source_info.span);
        if let Some(instance) = Instance::try_resolve(
            tcx,
            TypingEnv::fully_monomorphized(),
            def_id,
            ty::List::empty(),
        )
        .ok()
        .flatten()
        {
            let sym_name = tcx.symbol_name(instance).name.to_string();
            let sym_id = self.symbols.intern(&sym_name);
            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic()).raw();

            let (call_mem, _call_data) = self.builder.call(
                callee.into(),
                args,
                Type::Unit,
                self.current_mem.into(),
                None,
                None,
                Origin::synthetic(),
            );
            self.current_mem = call_mem.raw();
        }

        // The panic function diverges, so terminate with unreachable.
        self.builder.trap(Origin::synthetic());
    }
}
