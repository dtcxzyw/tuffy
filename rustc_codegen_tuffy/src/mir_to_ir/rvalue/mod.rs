use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, Rvalue};
use rustc_middle::ty::{self, Instance};
use tuffy_ir::instruction::{FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use rustc_middle::ty::TyCtxt;

use super::constant::*;
use super::ctx::TranslationCtx;
use super::types::*;

/// Aggregate lowering and operand-to-memory helpers.
mod aggregate;
/// Arithmetic, comparison, and pointer-offset rvalue lowering.
mod binary;
/// Cast and pointer-coercion lowering.
mod cast;

/// Recursively peel through ADT wrapper layers (Rc, Arc, NonNull, etc.) to
/// find the inner pointer pointees for an unsizing coercion.
///
/// For example, `Rc<[u8; 3]>` → `Rc<[u8]>` peels through:
///   Rc → NonNull<RcBox<T>> → *const RcBox<T> → pointees RcBox<[u8;3]>, RcBox<[u8]>
///
/// This matches codegen_ssa::base::unsize_ptr's recursive ADT field walking.
pub(super) fn peel_adt_to_pointees<'tcx>(
    tcx: TyCtxt<'tcx>,
    src: ty::Ty<'tcx>,
    dst: ty::Ty<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
) -> (ty::Ty<'tcx>, ty::Ty<'tcx>) {
    match (src.kind(), dst.kind()) {
        (ty::Ref(_, a, _), ty::Ref(_, b, _))
        | (ty::Ref(_, a, _), ty::RawPtr(b, _))
        | (ty::RawPtr(a, _), ty::Ref(_, b, _))
        | (ty::RawPtr(a, _), ty::RawPtr(b, _)) => (*a, *b),
        _ if src.is_box() && dst.is_box() => {
            let a = src.boxed_ty().unwrap();
            let b = dst.boxed_ty().unwrap();
            (a, b)
        }
        (ty::Adt(def_a, args_a), ty::Adt(def_b, args_b)) if def_a == def_b => {
            // Find the first field whose type differs between source and target.
            for field in def_a.non_enum_variant().fields.iter() {
                let fa = tcx.normalize_erasing_regions(typing_env, field.ty(tcx, args_a));
                let fb = tcx.normalize_erasing_regions(typing_env, field.ty(tcx, args_b));
                if fa != fb {
                    return peel_adt_to_pointees(tcx, fa, fb, typing_env);
                }
            }
            // No differing field found; fall back to the types themselves.
            (src, dst)
        }
        _ => (src, dst),
    }
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Extract bit width from result annotation.
    fn extract_result_bits(&self, res_ann: Option<IntAnn>) -> u32 {
        match res_ann.unwrap() {
            IntAnn::Signed(n) | IntAnn::Unsigned(n) => n,
            IntAnn::DontCare(_) => unreachable!("DontCare annotation in extract_result_bits"),
        }
    }

    /// Apply sign/zero extension based on result annotation signedness.
    /// For wide results the operation already produces a full-width value,
    /// so we skip the redundant zext/sext to avoid legalization overhead.
    fn apply_int_extension(
        &mut self,
        value: ValueRef,
        res_ann: Option<IntAnn>,
        bits: u32,
    ) -> ValueRef {
        if bits >= 128 {
            return value;
        }
        match res_ann.unwrap() {
            IntAnn::Signed(_) => self
                .builder
                .sext(value.into(), bits, Origin::synthetic())
                .raw(),
            IntAnn::Unsigned(_) => self
                .builder
                .zext(value.into(), bits, Origin::synthetic())
                .raw(),
            IntAnn::DontCare(_) => unreachable!("DontCare annotation in apply_int_extension"),
        }
    }

    /// Lowers one MIR rvalue and returns its primary IR value when one exists.
    pub(super) fn translate_rvalue(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        match rvalue {
            Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                self.translate_binary_op(op, lhs, rhs, dest_place)
            }
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::Cast(kind, operand, target_ty) => {
                self.translate_cast(kind, operand, target_ty, dest_place)
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if !place.projection.is_empty() {
                    let result = self.translate_place_to_addr(place).map(|(addr, _ty)| addr);
                    let dest_ty = if dest_place.projection.is_empty() {
                        self.monomorphize(self.mir.local_decls[dest_place.local].ty)
                    } else {
                        self.monomorphize(dest_place.ty(&self.mir.local_decls, self.tcx).ty)
                    };
                    let source_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                    if is_fat_ptr(self.tcx, dest_ty)
                        && is_fat_ptr(self.tcx, source_ty)
                        && place.projection.len() == 1
                        && matches!(place.projection.first(), Some(mir::PlaceElem::Deref))
                        && self.find_fat_metadata_for_place(place).is_some()
                    {
                        return result;
                    }
                    // When taking a Ref/RawPtr of a dereferenced fat pointer
                    // (e.g. `&raw const (*_3)` where `_3: &[u8]`), the result
                    // is itself a fat pointer that must preserve the metadata
                    // (length for slices, vtable for dyn).  translate_place_to_addr
                    // only returns the data pointer; reconstruct the full fat
                    // pointer in a 16-byte stack slot.
                    if let Some(data_ptr) = result
                        && is_fat_ptr(self.tcx, dest_ty)
                    {
                        // Find the metadata from the source fat pointer.
                        let meta = self.find_fat_metadata_for_place(place);
                        if let Some(meta_val) = meta {
                            let slot = self.builder.stack_slot(16, 0, Origin::synthetic());
                            self.current_mem = self
                                .builder
                                .store(
                                    data_ptr.into(),
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
                            let meta_addr = self.builder.ptradd(
                                slot.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            self.current_mem = self
                                .builder
                                .store(
                                    meta_val.into(),
                                    meta_addr.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            return Some(slot);
                        }
                    }
                    result
                } else if self.stack_locals.is_stack(place.local) {
                    self.locals.get(place.local)
                } else {
                    if let Some(val) = self.locals.get(place.local) {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, local_ty).unwrap_or(8) as u32;
                        let slot = self.builder.stack_slot(size.max(8), 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        if let Some(meta) = self.fat_locals.get(place.local) {
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let meta_addr = self.builder.ptradd(
                                slot.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            self.current_mem = self
                                .builder
                                .store(
                                    meta.into(),
                                    meta_addr.into(),
                                    8,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                        }
                        self.locals.set(place.local, slot);
                        self.stack_locals.mark(place.local);
                        Some(slot)
                    } else {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, local_ty).unwrap_or(1) as u32;
                        let slot = self.builder.stack_slot(size.max(1), 0, Origin::synthetic());
                        self.locals.set(place.local, slot);
                        self.stack_locals.mark(place.local);
                        Some(slot)
                    }
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                self.translate_aggregate(kind, operands.raw.as_slice(), dest_place)
            }
            Rvalue::UnaryOp(
                mir::UnOp::PtrMetadata,
                Operand::Copy(place) | Operand::Move(place),
            ) => {
                // Extract metadata (e.g., slice length) from a fat pointer.
                // Stack locals first: metadata lives in the slot and may
                // have been updated by assignments (e.g. _1 = copy _15
                // where _15 is a subslice).  fat_locals would still hold
                // the original stale value.
                // 1. Stack local: load length from slot + 8.
                if place.projection.is_empty()
                    && self.stack_locals.is_stack(place.local)
                    && let Some(slot) = self.locals.get(place.local)
                {
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let len_addr =
                        self.builder
                            .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                    let data = self.builder.load(
                        len_addr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(8),
                        Origin::synthetic(),
                    );
                    return Some(data);
                }
                // 2. Non-stack local with fat component tracked in fat_locals.
                if place.projection.is_empty()
                    && let Some(len) = self.fat_locals.get(place.local)
                {
                    return Some(len);
                }
                // 2b. Cast-to-fat metadata (e.g. NonNull<[T]> as *const [T]).
                if place.projection.is_empty()
                    && let Some(len) = self.cast_fat_meta.get(place.local)
                {
                    return Some(len);
                }
                // 3. Projected place (e.g. _s.field): compute the fat
                //    pointer's address and load length from offset +8.
                if !place.projection.is_empty()
                    && let Some((addr, _)) = self.translate_place_to_addr(place)
                {
                    let addr = self.coerce_to_ptr(addr);
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let len_addr =
                        self.builder
                            .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                    let data = self.builder.load(
                        len_addr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(8),
                        Origin::synthetic(),
                    );
                    return Some(data);
                }
                None
            }
            Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _) => {
                unimplemented!("MIR rvalue: UnaryOp::PtrMetadata")
            }
            Rvalue::UnaryOp(mir::UnOp::Neg, operand) => {
                let v = self.translate_operand(operand)?;
                let op_ty = operand_ty_projected(operand, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty));
                // Float negation: use FNeg IR op, which keeps the result Float-typed.
                if let Some(ty) = op_ty
                    && ty.is_floating_point()
                {
                    let ft = match ty.kind() {
                        ty::Float(ty::FloatTy::F32) => FloatType::F32,
                        ty::Float(ty::FloatTy::F64) => FloatType::F64,
                        _ => return Some(v),
                    };
                    return Some(
                        self.builder
                            .fneg(v.into(), Type::Float(ft), Origin::synthetic())
                            .raw(),
                    );
                }
                let neg_ann = op_ty
                    .and_then(translate_annotation)
                    .and_then(|a| IntAnn::from_annotation(&a));
                // Coerce Bool/Ptr to Int for integer negation.
                let v = self.coerce_to_int(v);
                if !matches!(self.builder.value_type(v), Some(Type::Int)) {
                    return Some(
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw(),
                    );
                }
                let bits = match neg_ann {
                    Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => n,
                    None => 64,
                };
                let sub_ann = IntAnnotation {
                    bit_width: bits,
                    signedness: IntSignedness::DontCare,
                };
                let zero = self
                    .builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                let result = self
                    .builder
                    .sub(zero.into(), v.into(), sub_ann, Origin::synthetic());
                Some(match neg_ann {
                    Some(IntAnn::Signed(_)) => self
                        .builder
                        .sext(result.into(), bits, Origin::synthetic())
                        .raw(),
                    Some(IntAnn::Unsigned(_)) => self
                        .builder
                        .zext(result.into(), bits, Origin::synthetic())
                        .raw(),
                    _ => result.raw(),
                })
            }
            Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
                let v = self.translate_operand(operand)?;
                let mir_ty = operand_ty_projected(operand, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty));
                let not_ann = mir_ty
                    .and_then(|t| translate_annotation(t))
                    .and_then(|a| IntAnn::from_annotation(&a));
                let is_bool = mir_ty.is_some_and(|t| t.is_bool());
                if is_bool {
                    // Boolean NOT: XOR 1.
                    let int_v = self.coerce_to_int(v);
                    let one =
                        self.builder
                            .iconst(1, 64, IntSignedness::DontCare, Origin::synthetic());
                    return Some(
                        self.builder
                            .xor(
                                int_v.into(),
                                one.into(),
                                IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw(),
                    );
                }
                let bits = match not_ann {
                    Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => n,
                    None => 64,
                };
                let xor_ann = IntAnnotation {
                    bit_width: bits,
                    signedness: IntSignedness::DontCare,
                };
                let result = match self.builder.value_type(v) {
                    Some(Type::Bool) => {
                        let true_val = self.builder.bconst(true, Origin::synthetic());
                        self.builder
                            .bxor(v.into(), true_val.into(), Origin::synthetic())
                            .raw()
                    }
                    _ => {
                        let ones = self.builder.iconst(
                            -1,
                            bits,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .xor(v.into(), ones.into(), xor_ann, Origin::synthetic())
                            .raw()
                    }
                };
                Some(match not_ann {
                    Some(IntAnn::Signed(_)) => self
                        .builder
                        .sext(result.into(), bits, Origin::synthetic())
                        .raw(),
                    Some(IntAnn::Unsigned(_)) => self
                        .builder
                        .zext(result.into(), bits, Origin::synthetic())
                        .raw(),
                    _ => result,
                })
            }
            Rvalue::Discriminant(place) => self.translate_discriminant(place),
            Rvalue::Repeat(operand, count) => {
                let elem_val = self.translate_operand(operand)?;
                let dest_ty = if dest_place.projection.is_empty() {
                    self.monomorphize(self.mir.local_decls[dest_place.local].ty)
                } else {
                    self.monomorphize(dest_place.ty(&self.mir.local_decls, self.tcx).ty)
                };
                let (elem_size, n) = match dest_ty.kind() {
                    ty::Array(elem_ty, _) => {
                        let es = type_size(self.tcx, *elem_ty).unwrap_or(8);
                        // Const-generic array lengths can remain unevaluated here even after
                        // monomorphization. Derive the instantiated length from the array layout
                        // instead of silently treating it as zero.
                        let cnt = array_len(self.tcx, dest_ty)
                            .or_else(|| count.try_to_target_usize(self.tcx))
                            .unwrap_or(0);
                        (es, cnt)
                    }
                    _ => return None,
                };
                if n == 0 || elem_size == 0 {
                    return Some(
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw(),
                    );
                }
                let total = (elem_size * n) as u32;
                let slot = if dest_place.projection.is_empty() {
                    if let Some(existing) = self.locals.get(dest_place.local) {
                        if matches!(self.builder.value_type(existing), Some(Type::Ptr(_))) {
                            existing
                        } else {
                            self.builder.stack_slot(total, 0, Origin::synthetic())
                        }
                    } else {
                        self.builder.stack_slot(total, 0, Origin::synthetic())
                    }
                } else {
                    self.builder.stack_slot(total, 0, Origin::synthetic())
                };
                let store_size = elem_size as u32;
                for i in 0..n {
                    let offset = (i * elem_size) as i64;
                    let dst = if offset == 0 {
                        slot
                    } else {
                        let off = self.builder.iconst(
                            offset,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    self.store_operand_value(operand, elem_val, dst, store_size);
                }
                // Only mark the local as stack when writing directly to it
                // (no projection). For projected assignments like `(*ptr) = [v; n]`
                // the local is a pointer whose VALUE should not be treated as a
                // stack-slot address – marking it would corrupt later loads.
                if dest_place.projection.is_empty() {
                    self.stack_locals.mark(dest_place.local);
                }
                Some(slot)
            }
            Rvalue::ThreadLocalRef(def_id) => {
                let instance = Instance::mono(self.tcx, *def_id);
                let sym_name = self.tcx.symbol_name(instance).name.to_string();
                let sym_id = self.symbols.intern(&sym_name);
                Some(
                    self.builder
                        .tls_symbol_addr(sym_id, Origin::synthetic())
                        .raw(),
                )
            }
            _ => None,
        }
    }
}
