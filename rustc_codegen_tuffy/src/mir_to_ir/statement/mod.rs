use super::ctx::{OptionScalarLocal, TranslationCtx};
use super::types::*;
use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, Rvalue, StatementKind};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

/// Shared 64-bit unsigned annotation used for synthesized integer temporaries.
const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

/// Assignment storage paths for deref, stack, register, and projected writes.
mod assign;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Try to keep a simple scalar `Option<T>` assignment in SSA.
    fn try_assign_simple_option_scalar(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> bool {
        let dest_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
        if !place.projection.is_empty()
            || !self.local_only_used_as_option_discriminant_and_payload(place.local)
        {
            return false;
        }
        let Some(payload_ty) = self.simple_option_scalar_payload_ty(dest_ty) else {
            return false;
        };

        let (is_some, payload) = match rvalue {
            Rvalue::Aggregate(
                box mir::AggregateKind::Adt(def_id, variant_idx, args, _, _),
                operands,
            ) => {
                let adt_def = self.tcx.adt_def(*def_id);
                if !adt_def.is_enum() || operands.len() > 1 {
                    return false;
                }
                let variant = adt_def.variant(*variant_idx);
                if variant.fields.len() == 1 && operands.len() == 1 {
                    let Some(field) = variant.fields.iter().next() else {
                        return false;
                    };
                    let field_ty = self.monomorphize(field.ty(self.tcx, args));
                    if field_ty != payload_ty {
                        return false;
                    }
                    let Some(operand) = operands.iter().next() else {
                        return false;
                    };
                    let Some(payload) = self.translate_operand(operand) else {
                        return false;
                    };
                    (
                        self.builder.bconst(true, Origin::synthetic()).raw(),
                        payload,
                    )
                } else if variant.fields.is_empty() && operands.is_empty() {
                    let zero = self
                        .builder
                        .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic())
                        .raw();
                    (self.builder.bconst(false, Origin::synthetic()).raw(), zero)
                } else {
                    return false;
                }
            }
            _ => return false,
        };

        self.option_scalar_locals.clear(place.local);
        self.option_scalar_locals
            .set(place.local, OptionScalarLocal { is_some, payload });
        true
    }

    /// Returns whether `rvalue` is a scalar constant that can stay in registers.
    fn rvalue_is_scalar_const(&self, rvalue: &Rvalue<'tcx>, dest_ty: ty::Ty<'tcx>) -> bool {
        matches!(
            rvalue,
            Rvalue::Use(Operand::Constant(_)) | Rvalue::Cast(_, Operand::Constant(_), _)
        ) && matches!(repr_kind(self.tcx, dest_ty), ReprKind::Scalar)
    }

    /// Lowers one MIR statement into Tuffy IR state updates and instructions.
    pub(super) fn translate_statement(&mut self, stmt: &mir::Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                if self.try_assign_simple_option_scalar(place, rvalue) {
                    return;
                }
                let rval_result = self.translate_rvalue(rvalue, place);
                if let Some(val) = rval_result {
                    // Handle stores through pointer dereference (e.g. *ptr = val).
                    // Other non-empty projections (Field, Index) on non-stack
                    // locals were previously no-ops; keep them that way to avoid
                    // generating ill-formed IR for patterns handled elsewhere.
                    let has_deref = !place.projection.is_empty()
                        && place
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, rustc_middle::mir::PlaceElem::Deref));
                    if has_deref {
                        self.assign_through_deref(val, place, rvalue);
                    } else if place.projection.is_empty() {
                        if self.stack_locals.is_stack(place.local) {
                            self.assign_to_stack_local(val, place, rvalue);
                        } else {
                            self.assign_to_register_local(val, place, rvalue);
                        }
                    } else {
                        self.assign_to_projected(val, place, rvalue);
                    }
                }
                if place.projection.is_empty() {
                    self.split_pair_locals.clear(place.local);
                    self.option_scalar_locals.clear(place.local);
                }
                // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
                // Only propagate fat metadata for direct local assignments (no
                // projection).  For deref / field stores we are writing THROUGH
                // the local, not TO it, so the rvalue's metadata must not be
                // associated with the base local (that would clobber unrelated
                // stack slots).
                if place.projection.is_empty()
                    && let Some(fat_val) = self.extract_fat_component(rvalue)
                {
                    self.fat_locals.set(place.local, fat_val);
                    // For stack-allocated locals, also store the metadata to
                    // the stack slot at offset `target_part_bytes()` so that
                    // code loading the full
                    // fat pointer from the slot (e.g. the Return terminator's
                    // stack-allocated path) sees both words.
                    if self.stack_locals.is_stack(place.local)
                        && let Some(slot) = self.locals.get(place.local)
                    {
                        let off = self.builder.iconst(
                            self.target_part_bytes() as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let addr =
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                fat_val.into(),
                                addr.into(),
                                self.target_part_bytes() as u32,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }
                // Cast from a projected non-fat type to a fat pointer
                // (e.g. `NonNull<[T]> as *const [T]` in into_vec):
                // load the metadata from the source address + 8 and
                // store it in cast_fat_meta so PtrMetadata can find it.
                // This is kept separate from fat_locals to avoid
                // propagation through Use/Copy chains.
                if let Rvalue::Cast(_, op, target_ty) = rvalue {
                    let target_ty_mono = self.monomorphize(*target_ty);
                    if is_fat_ptr(self.tcx, target_ty_mono)
                        && let Operand::Copy(src) | Operand::Move(src) = op
                        && !src.projection.is_empty()
                    {
                        let src_ty = src.ty(&self.mir.local_decls, self.tcx).ty;
                        let src_ty = self.monomorphize(src_ty);
                        let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                        if src_size >= 16
                            && !is_fat_ptr(self.tcx, src_ty)
                            && let Some((addr, _)) = self.translate_place_to_addr(src)
                        {
                            let addr = self.coerce_to_ptr(addr);
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let meta_addr = self.builder.ptradd(
                                addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let meta = self.builder.load(
                                meta_addr.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            self.cast_fat_meta.set(place.local, meta);
                        }
                    }
                }
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            StatementKind::SetDiscriminant {
                box place,
                variant_index,
            } => {
                self.translate_set_discriminant(place, *variant_index);
            }
            StatementKind::Intrinsic(intrinsic) => {
                use rustc_middle::mir::NonDivergingIntrinsic;
                match &**intrinsic {
                    NonDivergingIntrinsic::CopyNonOverlapping(copy_info) => {
                        // copy_nonoverlapping(src, dst, count) → memcpy(dst, src, count * sizeof(T))
                        // count is in elements; we must multiply by the pointee size.
                        let src = self.translate_operand(&copy_info.src);
                        let dst = self.translate_operand(&copy_info.dst);
                        let count = self.translate_operand(&copy_info.count);
                        if let (Some(src_v), Some(dst_v), Some(count_v)) = (src, dst, count) {
                            let src_ty = self
                                .monomorphize(copy_info.src.ty(&self.mir.local_decls, self.tcx));
                            let pointee_size = src_ty
                                .builtin_deref(true)
                                .and_then(|t| type_size(self.tcx, t))
                                .unwrap_or(1);
                            let byte_count = if pointee_size == 0 {
                                // ZST: no bytes to copy regardless of count.
                                self.builder
                                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                                    .raw()
                            } else if pointee_size == 1 {
                                count_v
                            } else {
                                let sz = self.builder.iconst(
                                    pointee_size as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .mul(count_v.into(), sz.into(), I64, Origin::synthetic())
                                    .raw()
                            };
                            let sym_id = self.symbols.intern("memcpy");
                            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());
                            let (mem_out, _) = self.builder.call(
                                callee.into(),
                                vec![dst_v.into(), src_v.into(), byte_count.into()],
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Some(Annotation::Int(I64)),
                                Origin::synthetic(),
                            );
                            self.current_mem = mem_out.raw();
                        }
                    }
                    NonDivergingIntrinsic::Assume(_) => {
                        // Runtime assumption — no codegen needed.
                    }
                }
            }
            _ => {
                unimplemented!("MIR statement: {:?}", stmt.kind);
            }
        }
    }
}
