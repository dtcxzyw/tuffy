use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, PlaceElem, Rvalue};
use rustc_middle::ty::{self, Instance, TypeVisitableExt, adjustment::PointerCoercion};
use tuffy_ir::instruction::{FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use rustc_middle::ty::TyCtxt;

use super::constant::*;
use super::ctx::TranslationCtx;
use super::types::*;

/// Recursively peel through ADT wrapper layers (Rc, Arc, NonNull, etc.) to
/// find the inner pointer pointees for an unsizing coercion.
///
/// For example, `Rc<[u8; 3]>` → `Rc<[u8]>` peels through:
///   Rc → NonNull<RcBox<T>> → *const RcBox<T> → pointees RcBox<[u8;3]>, RcBox<[u8]>
///
/// This matches codegen_ssa::base::unsize_ptr's recursive ADT field walking.
fn peel_adt_to_pointees<'tcx>(
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
    /// Compute the discriminant of an enum at `place`.
    ///
    /// Handles three layout cases:
    /// - `Variants::Single`: return the constant discriminant value.
    /// - `Variants::Multiple` with `TagEncoding::Direct`: load the tag field.
    /// - `Variants::Multiple` with `TagEncoding::Niche`: load the niche field
    pub(super) fn translate_discriminant(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = self
            .tcx
            .layout_of(typing_env.as_query_input(place_ty))
            .ok()?;

        match layout.variants {
            rustc_abi::Variants::Empty => Some(
                self.builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            ),
            rustc_abi::Variants::Single { index } => {
                let discr_val = match place_ty.kind() {
                    ty::Adt(adt_def, _) if adt_def.is_enum() => {
                        adt_def.discriminant_for_variant(self.tcx, index).val as i64
                    }
                    _ => index.as_u32() as i64,
                };
                Some(
                    self.builder
                        .iconst(discr_val, 64, IntSignedness::DontCare, Origin::synthetic())
                        .raw(),
                )
            }
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => {
                // Get the address of the enum value.
                let base_addr = if place.projection.is_empty() {
                    if self.stack_locals.is_stack(place.local) {
                        self.locals.get(place.local)?
                    } else {
                        // Scalar local — spill to a temporary stack slot.
                        let val = self.locals.get(place.local)?;
                        let size = layout.size.bytes() as u32;
                        let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                slot.into(),
                                size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        slot
                    }
                } else {
                    let (addr, _) = self.translate_place_to_addr(place)?;
                    self.coerce_to_ptr(addr)
                };

                // Tag field offset and load size.
                let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
                let tag_size = match tag.primitive() {
                    rustc_abi::Primitive::Int(int, _) => int.size().bytes() as u32,
                    rustc_abi::Primitive::Pointer(_) => 8,
                    _ => 8,
                };

                let tag_addr = if tag_offset != 0 {
                    let off = self.builder.iconst(
                        tag_offset as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .ptradd(base_addr.into(), off.into(), 0, Origin::synthetic())
                        .raw()
                } else {
                    base_addr
                };
                let tag_val = self.builder.load(
                    tag_addr.into(),
                    tag_size,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(tag_size),
                    Origin::synthetic(),
                );

                match tag_encoding {
                    rustc_abi::TagEncoding::Direct => Some(tag_val),
                    rustc_abi::TagEncoding::Niche {
                        untagged_variant,
                        niche_variants,
                        niche_start,
                    } => {
                        let variants_start = niche_variants.start().as_u32();
                        let variants_end = niche_variants.end().as_u32();
                        let num_niche = variants_end - variants_start + 1;
                        let untagged_discr = untagged_variant.as_u32() as i64;

                        if num_niche == 1 && *niche_start == 0 && variants_start == 0 {
                            // Common case: Option-like niche (tag == 0 → None).
                            let zero = self.builder.iconst(
                                0,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let is_niche = self.builder.icmp(
                                ICmpOp::Eq,
                                tag_val.into(),
                                zero.into(),
                                Origin::synthetic(),
                            );
                            let niche_discr = self.builder.iconst(
                                variants_start as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let untag_discr = self.builder.iconst(
                                untagged_discr,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            Some(self.builder.select(
                                is_niche.into(),
                                niche_discr.into(),
                                untag_discr.into(),
                                Type::Int,
                                default_int_annotation(),
                                Origin::synthetic(),
                            ))
                        } else {
                            // General niche: i = tag.wrapping_sub(niche_start) + start
                            let ns = self.builder.iconst(
                                *niche_start as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let relative = self.builder.sub(
                                tag_val.into(),
                                ns.into(),
                                IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            );
                            let start_c = self.builder.iconst(
                                variants_start as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let variant_idx = self.builder.add(
                                relative.into(),
                                start_c.into(),
                                IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            );
                            // Check relative < num_niche (unsigned).
                            let num_c = self.builder.iconst(
                                num_niche as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let in_range = self.builder.icmp(
                                ICmpOp::Lt,
                                relative.into(),
                                num_c.into(),
                                Origin::synthetic(),
                            );
                            let untag_discr = self.builder.iconst(
                                untagged_discr,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            Some(self.builder.select(
                                in_range.into(),
                                variant_idx.into(),
                                untag_discr.into(),
                                Type::Int,
                                default_int_annotation(),
                                Origin::synthetic(),
                            ))
                        }
                    }
                }
            }
        }
    }

    pub(super) fn extract_fat_component(&mut self, rvalue: &Rvalue<'tcx>) -> Option<ValueRef> {
        match rvalue {
            // Constant slice: extract the length metadata.
            Rvalue::Use(Operand::Constant(c)) => {
                // Resolve the constant (may be Unevaluated) to a ConstValue.
                let mono_const = self.tcx.instantiate_and_normalize_erasing_regions(
                    self.instance.args,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(c.const_),
                );
                let const_ty = mono_const.ty();
                let resolved = match mono_const {
                    mir::Const::Val(v, _) => Some(v),
                    _ => {
                        let typing_env = ty::TypingEnv::fully_monomorphized();
                        mono_const.eval(self.tcx, typing_env, c.span).ok()
                    }
                };
                if let Some(mir::ConstValue::Slice { meta, .. }) = resolved {
                    return Some(
                        self.builder
                            .iconst(
                                meta as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            )
                            .raw(),
                    );
                }
                // Indirect constant for fat pointer types (e.g. &[T]):
                // the allocation contains [data_ptr (8 bytes) | len (8 bytes)].
                // Extract the length from bytes 8..16.
                if let Some(mir::ConstValue::Indirect { alloc_id, offset }) = resolved
                    && is_fat_ptr(self.tcx, const_ty)
                {
                    let alloc = self.tcx.global_alloc(alloc_id);
                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) = alloc {
                        let inner = mem_alloc.inner();
                        let byte_offset = offset.bytes() as usize + 8; // skip data_ptr
                        let len_bytes = inner.inspect_with_uninit_and_ptr_outside_interpreter(
                            byte_offset..byte_offset + 8,
                        );
                        let len = u64::from_le_bytes(len_bytes.try_into().unwrap_or([0u8; 8]));
                        return Some(
                            self.builder
                                .iconst(
                                    len as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                )
                                .raw(),
                        );
                    }
                }
                None
            }
            // Use of a fat local: propagate the fat component.
            // If the source local already has a fat component AND the place
            // has no projections, propagate it directly.  When projections
            // are present (e.g. _struct.field), the local's fat component
            // belongs to the struct itself (set by Aggregate), not to the
            // projected field — fall through to the projected-place path.
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                if place.projection.is_empty() {
                    // For stack locals, always reload metadata from memory
                    // (the stack slot at offset 8).  The cached fat_locals
                    // value may be an SSA value defined in a non-dominating
                    // block (e.g. a branch that adjusted the slice length),
                    // which would be invalid on control-flow paths that
                    // bypassed that block.
                    if self.stack_locals.is_stack(place.local)
                        && self.fat_locals.get(place.local).is_some()
                        && let Some(slot) = self.locals.get(place.local)
                    {
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let meta_addr =
                            self.builder
                                .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                        let meta = self.builder.load(
                            meta_addr.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            Some(Annotation::Int(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            })),
                            Origin::synthetic(),
                        );
                        return Some(meta);
                    }
                    if let Some(fat) = self.fat_locals.get(place.local) {
                        return Some(fat);
                    }
                }
                // Check if the place resolves to a fat pointer type via projections.
                if !place.projection.is_empty() {
                    let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                    let projected_ty = self.monomorphize(projected_ty);
                    if is_fat_ptr(self.tcx, projected_ty)
                        && let Some((addr, _)) = self.translate_place_to_addr(place)
                    {
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let meta_addr =
                            self.builder
                                .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                        let meta = self.builder.load(
                            meta_addr.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(8),
                            Origin::synthetic(),
                        );
                        return Some(meta);
                    }
                }
                None
            }
            // Cast of a fat local: propagate, or generate vtable for Unsize coercion.
            Rvalue::Cast(cast_kind, op, target_ty) => {
                // Only propagate existing fat component when the target
                // type is itself a fat pointer.  Casts like *const [T] →
                // *const T strip metadata and must NOT propagate.
                let target_ty_mono = self.monomorphize(*target_ty);
                if is_fat_ptr(self.tcx, target_ty_mono) {
                    // From a local with existing fat component.
                    if let Operand::Copy(place) | Operand::Move(place) = op {
                        // For stack locals, always reload metadata from memory
                        // (the stack slot at offset 8).  The cached fat_locals
                        // value may be an SSA value defined in a non-dominating
                        // block, which would be invalid on control-flow paths
                        // that bypassed that block.
                        if place.projection.is_empty()
                            && self.stack_locals.is_stack(place.local)
                            && self.fat_locals.get(place.local).is_some()
                            && let Some(slot) = self.locals.get(place.local)
                        {
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
                            let meta = self.builder.load(
                                meta_addr.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            return Some(meta);
                        }
                        // Non-stack local with cached fat component.
                        if place.projection.is_empty()
                            && !self.stack_locals.is_stack(place.local)
                            && let Some(fat) = self.fat_locals.get(place.local)
                        {
                            return Some(fat);
                        }
                        // Projected place (e.g. _3.0.0 where the inner
                        // type is a fat-pointer-sized ADT wrapper like
                        // NonNull<[T]>): load metadata from offset +8.
                        if !place.projection.is_empty() {
                            let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                            let projected_ty = self.monomorphize(projected_ty);
                            let proj_size = type_size(self.tcx, projected_ty).unwrap_or(0);
                            if proj_size > 8
                                && let Some((addr, _)) = self.translate_place_to_addr(place)
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
                                // Dyn trait metadata is a vtable pointer;
                                // slice/str metadata is an integer length.
                                let pointee = match target_ty_mono.kind() {
                                    ty::RawPtr(inner, _) | ty::Ref(_, inner, _) => Some(*inner),
                                    _ => None,
                                };
                                let is_vtable =
                                    pointee.is_some_and(|p| matches!(p.kind(), ty::Dynamic(..)));
                                let (meta_ty, meta_ann) = if is_vtable {
                                    (Type::Ptr(0), None)
                                } else {
                                    (Type::Int, int_annotation_for_bytes(8))
                                };
                                let meta = self.builder.load(
                                    meta_addr.into(),
                                    8,
                                    meta_ty,
                                    self.current_mem.into(),
                                    meta_ann,
                                    Origin::synthetic(),
                                );
                                return Some(meta);
                            }
                        }
                    }
                    // From a constant fat pointer (e.g. `const "hello" as &[u8]`).
                    if let Operand::Constant(c) = op {
                        let mono_const = self.tcx.instantiate_and_normalize_erasing_regions(
                            self.instance.args,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(c.const_),
                        );
                        let const_ty = mono_const.ty();
                        let resolved = match mono_const {
                            mir::Const::Val(v, _) => Some(v),
                            _ => {
                                let typing_env = ty::TypingEnv::fully_monomorphized();
                                mono_const.eval(self.tcx, typing_env, c.span).ok()
                            }
                        };
                        if let Some(mir::ConstValue::Slice { meta, .. }) = resolved {
                            return Some(
                                self.builder
                                    .iconst(
                                        meta as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    )
                                    .raw(),
                            );
                        }
                        if let Some(mir::ConstValue::Indirect { alloc_id, offset }) = resolved
                            && is_fat_ptr(self.tcx, const_ty)
                        {
                            let alloc = self.tcx.global_alloc(alloc_id);
                            if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) =
                                alloc
                            {
                                let inner = mem_alloc.inner();
                                let byte_offset = offset.bytes() as usize + 8;
                                let len_bytes = inner
                                    .inspect_with_uninit_and_ptr_outside_interpreter(
                                        byte_offset..byte_offset + 8,
                                    );
                                let len =
                                    u64::from_le_bytes(len_bytes.try_into().unwrap_or([0u8; 8]));
                                return Some(
                                    self.builder
                                        .iconst(
                                            len as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        )
                                        .raw(),
                                );
                            }
                        }
                    }
                }
                // For Unsize coercions from [T; N] to [T], emit the
                // array length as slice metadata.
                if let CastKind::PointerCoercion(PointerCoercion::Unsize, _) = cast_kind {
                    // Check whether the target is a trait object — if so, skip
                    // the array-length path and fall through to vtable generation.
                    let target_ty_m = self.monomorphize(*target_ty);
                    let target_inner = match target_ty_m.kind() {
                        ty::Ref(_, inner, _) => Some(*inner),
                        ty::RawPtr(inner, _) => Some(*inner),
                        _ if target_ty_m.is_box() => target_ty_m.boxed_ty(),
                        _ => None,
                    };
                    let is_trait_target =
                        target_inner.is_some_and(|t| matches!(t.kind(), ty::Dynamic(..)));

                    if !is_trait_target {
                        let src_ty = self.operand_ty_mono(op);
                        if let Some(src_ty) = src_ty {
                            let src_inner = match src_ty.kind() {
                                ty::Ref(_, inner, _) => Some(*inner),
                                ty::RawPtr(inner, _) => Some(*inner),
                                _ if src_ty.is_box() => src_ty.boxed_ty(),
                                _ => None,
                            };
                            if let Some(inner) = src_inner {
                                // Use struct_tail_for_codegen to handle both direct
                                // array unsizing (&[T; N] → &[T]) and struct unsizing
                                // (&Wrapper<[T; N]> → &Wrapper<[T]>) where the array
                                // is nested inside one or more wrapper structs.
                                let typing_env = ty::TypingEnv::fully_monomorphized();
                                let src_tail = self.tcx.struct_tail_for_codegen(inner, typing_env);
                                if let ty::Array(_, len_const) = src_tail.kind() {
                                    let len = len_const.try_to_target_usize(self.tcx).unwrap_or(0);
                                    return Some(
                                        self.builder
                                            .iconst(
                                                len as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    );
                                }
                            }
                        }
                    }
                }
                // For Unsize coercions to trait objects, generate the vtable pointer.
                if let CastKind::PointerCoercion(PointerCoercion::Unsize, _) = cast_kind {
                    // Check if this is an Unsize coercion by examining the target type.
                    let target_ty = self.monomorphize(*target_ty);
                    let target_inner = match target_ty.kind() {
                        ty::Ref(_, inner, _) => Some(*inner),
                        ty::RawPtr(inner, _) => Some(*inner),
                        _ if target_ty.is_box() => target_ty.boxed_ty(),
                        _ => None,
                    };
                    if let Some(inner) = target_inner
                        && let ty::Dynamic(predicates, _) = inner.kind()
                    {
                        // Direct unsizing to a trait object (e.g. &Concrete → &dyn Trait).
                        // Use the source type directly (NOT struct_tail) since the
                        // concrete type IS the one implementing the trait.
                        let src_ty = self.operand_ty_mono(op)?;
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ if src_ty.is_box() => src_ty.boxed_ty().unwrap(),
                            _ => src_ty,
                        };
                        // Skip vtable generation for types with escaping
                        // bound vars (e.g. closures with unresolved generics).
                        if src_inner.has_escaping_bound_vars() {
                            return None;
                        }
                        // Skip trait upcasting: source is already a dyn trait,
                        // vtable_allocation panics on unsized types.
                        if src_inner.is_trait() {
                            return None;
                        }
                        let principal = predicates
                            .principal()
                            .map(|p| self.tcx.instantiate_bound_regions_with_erased(p));
                        let vtable_alloc_id = self.tcx.vtable_allocation((src_inner, principal));
                        if let Some(vtable_val) = self.emit_vtable(vtable_alloc_id) {
                            return Some(vtable_val);
                        }
                    }
                    // Handle array-to-slice unsizing: &[T; N] → &[T].
                    // The fat component is the array length N.
                    if let Some(inner) = target_inner
                        && let ty::Slice(_) = inner.kind()
                    {
                        let src_ty = self.operand_ty_mono(op)?;
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ if src_ty.is_box() => src_ty.boxed_ty().unwrap(),
                            _ => src_ty,
                        };
                        if let ty::Array(_, len) = src_inner.kind()
                            && let Some(n) = len.try_to_target_usize(self.tcx)
                        {
                            return Some(
                                self.builder
                                    .iconst(
                                        n as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    )
                                    .raw(),
                            );
                        }
                    }

                    // Handle struct unsizing: the target inner type is
                    // a struct whose unsized tail is a slice or trait
                    // object (e.g. Box<Node<[isize; 0]>> → Box<Node<[isize]>>).
                    // Use struct_lockstep_tails_for_codegen to walk source
                    // and target in lockstep, stopping at the unsizing
                    // boundary (matching codegen_ssa::base::unsized_info).
                    if let Some(inner) = target_inner {
                        let typing_env = ty::TypingEnv::fully_monomorphized();
                        let src_ty = self.operand_ty_mono(op)?;
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ if src_ty.is_box() => src_ty.boxed_ty().unwrap(),
                            _ => src_ty,
                        };
                        // Skip if source == target (no actual unsizing needed,
                        // e.g. non-Unsize PointerCoercion that slipped through).
                        if src_inner == inner {
                            // No unsizing, nothing to do.
                        } else {
                            let (src_tail, dst_tail) = self
                                .tcx
                                .struct_lockstep_tails_for_codegen(src_inner, inner, typing_env);
                            match dst_tail.kind() {
                                ty::Slice(_) => {
                                    if let ty::Array(_, len) = src_tail.kind()
                                        && let Some(n) = len.try_to_target_usize(self.tcx)
                                    {
                                        return Some(
                                            self.builder
                                                .iconst(
                                                    n as i64,
                                                    64,
                                                    IntSignedness::DontCare,
                                                    Origin::synthetic(),
                                                )
                                                .raw(),
                                        );
                                    }
                                }
                                ty::Dynamic(predicates, _)
                                    if !src_tail.has_escaping_bound_vars()
                                        && !src_tail.is_trait()
                                        && src_tail.is_sized(
                                            self.tcx,
                                            ty::TypingEnv::fully_monomorphized(),
                                        ) =>
                                {
                                    let principal = predicates
                                        .principal()
                                        .map(|p| self.tcx.instantiate_bound_regions_with_erased(p));
                                    let vtable_alloc_id =
                                        self.tcx.vtable_allocation((src_tail, principal));
                                    if let Some(vtable_val) = self.emit_vtable(vtable_alloc_id) {
                                        return Some(vtable_val);
                                    }
                                }
                                _ => {}
                            }
                        } // end else (src_inner != inner)
                    }

                    // Fallback for ADT types (Rc, Arc, etc.) where target_inner
                    // is None because the type is not Ref/RawPtr/Box.
                    // Recursively peel through ADT fields to find the inner
                    // pointer types, then use struct_lockstep_tails_for_codegen
                    // on the pointees (matching codegen_ssa::base::unsize_ptr).
                    if target_inner.is_none() {
                        let src_ty = self.operand_ty_mono(op)?;
                        let typing_env = ty::TypingEnv::fully_monomorphized();
                        let (src_pointee, dst_pointee) =
                            peel_adt_to_pointees(self.tcx, src_ty, target_ty, typing_env);
                        let (src_tail, dst_tail) = self.tcx.struct_lockstep_tails_for_codegen(
                            src_pointee,
                            dst_pointee,
                            typing_env,
                        );
                        match dst_tail.kind() {
                            ty::Slice(_) => {
                                if let ty::Array(_, len) = src_tail.kind()
                                    && let Some(n) = len.try_to_target_usize(self.tcx)
                                {
                                    return Some(
                                        self.builder
                                            .iconst(
                                                n as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    );
                                }
                            }
                            ty::Dynamic(predicates, _)
                                if !src_tail.has_escaping_bound_vars()
                                    && !src_tail.is_trait()
                                    && src_tail.is_sized(
                                        self.tcx,
                                        ty::TypingEnv::fully_monomorphized(),
                                    ) =>
                            {
                                let principal = predicates
                                    .principal()
                                    .map(|p| self.tcx.instantiate_bound_regions_with_erased(p));
                                let vtable_alloc_id =
                                    self.tcx.vtable_allocation((src_tail, principal));
                                if let Some(vtable_val) = self.emit_vtable(vtable_alloc_id) {
                                    return Some(vtable_val);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                None
            }
            // &raw const (*place) / &(*place): propagate fat component from
            // the base local through the re-borrow, but only when the
            // result is itself a fat pointer (pointee is unsized).
            Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                let pointee_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                let pointee_ty = self.monomorphize(pointee_ty);
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let tail = self.tcx.struct_tail_for_codegen(pointee_ty, typing_env);
                if matches!(tail.kind(), ty::Slice(..) | ty::Str | ty::Dynamic(..)) {
                    // Use find_fat_metadata_for_place which adjusts for
                    // Subslice projections (new_len = old_len - from - to),
                    // instead of raw fat_locals.get which returns the
                    // unadjusted original length.
                    self.find_fat_metadata_for_place(place)
                        .or_else(|| self.cast_fat_meta.get(place.local))
                } else {
                    None
                }
            }
            // Multi-field Aggregate: second field becomes the fat component,
            // but ONLY when the aggregate type is a fat pointer (e.g.
            // NonNull<[T]>, &str wrapper struct).  Plain tuples and
            // non-fat-pointer structs must not have their second field
            // treated as metadata — doing so causes a spurious store at
            // slot+8 that overflows the stack slot.
            Rvalue::Aggregate(box kind, operands)
                if operands.len() >= 2 && !matches!(kind, mir::AggregateKind::Array(_)) =>
            {
                // Determine the aggregate's result type to check if it's
                // actually a fat pointer.
                let agg_ty = match kind {
                    mir::AggregateKind::Adt(def_id, _, args, _, _) => {
                        let adt_def = self.tcx.adt_def(*def_id);
                        Some(self.monomorphize(ty::Ty::new_adt(self.tcx, adt_def, args)))
                    }
                    // RawPtr aggregates: *const [T], *mut [T], etc.
                    mir::AggregateKind::RawPtr(pointee_ty, mutbl) => {
                        let pointee_ty = self.monomorphize(*pointee_ty);
                        Some(ty::Ty::new_ptr(self.tcx, pointee_ty, *mutbl))
                    }
                    // Tuples are never fat pointers.
                    mir::AggregateKind::Tuple => None,
                    _ => None,
                };
                if agg_ty.is_some_and(|t| is_fat_ptr(self.tcx, t)) {
                    let second_op = operands.iter().nth(1).unwrap();
                    self.translate_operand(second_op)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract bit width from result annotation.
    fn extract_result_bits(&self, res_ann: Option<IntAnn>) -> u32 {
        match res_ann.unwrap() {
            IntAnn::Signed(n) | IntAnn::Unsigned(n) => n,
            IntAnn::DontCare(_) => unreachable!("DontCare annotation in extract_result_bits"),
        }
    }

    /// Apply sign/zero extension based on result annotation signedness.
    /// For 128-bit results the operation already produces a full-width value,
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

    /// Extract fat pointer metadata from a MIR operand.
    /// For place operands, delegates to `find_fat_metadata_for_place`.
    /// Returns `None` for non-fat operands and constants.
    fn find_fat_metadata_for_operand(&mut self, operand: &Operand<'tcx>) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.find_fat_metadata_for_place(place),
            _ => None,
        }
    }

    /// Load the data pointer from a fat pointer operand.
    /// `translate_operand` returns the stack slot address for fat pointer
    /// stack locals; this helper loads the first 8 bytes (the data pointer)
    /// so that comparisons operate on values rather than addresses.
    fn load_fat_data_for_operand(&mut self, operand: &Operand<'tcx>, raw: ValueRef) -> ValueRef {
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && place.projection.is_empty()
            && self.stack_locals.is_stack(place.local)
            && matches!(self.builder.value_type(raw), Some(Type::Ptr(_)))
        {
            let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
            if is_fat_ptr(self.tcx, ty) {
                return self.builder.load(
                    raw.into(),
                    8,
                    Type::Ptr(0),
                    self.current_mem.into(),
                    None,
                    Origin::synthetic(),
                );
            }
        }
        raw
    }

    /// Extract fat pointer metadata (length for slices, vtable for dyn)
    /// from the base local of a place.  Checks stack locals first (they
    /// may have been updated by assignments), then falls back to fat_locals.
    /// When the place has a Subslice projection, adjusts the metadata
    /// by subtracting the `from` and `to` indices.
    pub(super) fn find_fat_metadata_for_place(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        let base_local = place.local;
        let base_ty = self.monomorphize(self.mir.local_decls[base_local].ty);
        if !is_fat_ptr(self.tcx, base_ty) {
            return None;
        }
        // Prefer stack local (metadata may have been updated by assignment).
        let meta = if self.stack_locals.is_stack(base_local) {
            if let Some(slot) = self.locals.get(base_local) {
                let off8 = self
                    .builder
                    .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                let meta_addr =
                    self.builder
                        .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                let loaded = self.builder.load(
                    meta_addr.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(8),
                    Origin::synthetic(),
                );
                Some(loaded)
            } else {
                self.fat_locals.get(base_local)
            }
        } else {
            self.fat_locals.get(base_local)
        };
        let meta = meta?;
        // If the place has a Subslice projection, adjust the metadata.
        // For from_end=true (slices): new_len = old_len - from - to.
        for proj in place.projection.iter() {
            if let PlaceElem::Subslice {
                from,
                to,
                from_end: true,
            } = proj
            {
                let adjust = from + to;
                if adjust > 0 {
                    let adj_val = self.builder.iconst(
                        adjust as i64,
                        64,
                        IntSignedness::Unsigned,
                        Origin::synthetic(),
                    );
                    let new_meta = self.builder.sub(
                        meta.into(),
                        adj_val.into(),
                        IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::Unsigned,
                        },
                        Origin::synthetic(),
                    );
                    return Some(new_meta.raw());
                }
            }
        }
        Some(meta)
    }

    pub(super) fn translate_rvalue(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        match rvalue {
            Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                let l_raw = self.translate_operand(lhs)?;
                let r_raw = self.translate_operand(rhs)?;
                let l_ann = operand_annotation(lhs, self.mir);
                let r_ann = operand_annotation(rhs, self.mir);

                // Detect float operands for arithmetic dispatch.
                let float_ty = {
                    let mir_ty = operand_ty_projected(lhs, self.mir, self.tcx)
                        .map(|ty| self.monomorphize(ty))
                        .unwrap_or(self.tcx.types.i32);
                    match mir_ty.kind() {
                        ty::Float(ty::FloatTy::F16) => Some(Type::Float(FloatType::F16)),
                        ty::Float(ty::FloatTy::F32) => Some(Type::Float(FloatType::F32)),
                        ty::Float(ty::FloatTy::F64) => Some(Type::Float(FloatType::F64)),
                        ty::Float(ty::FloatTy::F128) => Some(Type::Float(FloatType::F128)),
                        _ => None,
                    }
                };

                // Float arithmetic: dispatch directly to fadd/fsub/fmul/fdiv.
                // Operands are always Float-typed at this point.
                // Floats have no "unchecked" variants — only the plain ops.
                if let Some(ref fty) = float_ty
                    && matches!(
                        op,
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
                    )
                {
                    let flags = FpRewriteFlags::default();
                    let l_f = l_raw;
                    let r_f = r_raw;
                    let res = match op {
                        BinOp::Add => self.builder.fadd(
                            l_f.into(),
                            r_f.into(),
                            flags,
                            fty.clone(),
                            Origin::synthetic(),
                        ),
                        BinOp::Sub => self.builder.fsub(
                            l_f.into(),
                            r_f.into(),
                            flags,
                            fty.clone(),
                            Origin::synthetic(),
                        ),
                        BinOp::Mul => self.builder.fmul(
                            l_f.into(),
                            r_f.into(),
                            flags,
                            fty.clone(),
                            Origin::synthetic(),
                        ),
                        BinOp::Rem => self.builder.frem(
                            l_f.into(),
                            r_f.into(),
                            flags,
                            fty.clone(),
                            Origin::synthetic(),
                        ),
                        _ => self.builder.fdiv(
                            l_f.into(),
                            r_f.into(),
                            flags,
                            fty.clone(),
                            Origin::synthetic(),
                        ),
                    };
                    return Some(res.raw());
                }

                // Unsupported operand types produce Unit or
                // typeless values — emit a dummy zero so the IR stays well-typed.
                // Float operands are allowed here because float comparisons
                // (Ge, Le, etc.) are handled further below via fcmp.
                if !matches!(
                    self.builder.value_type(l_raw),
                    Some(Type::Int | Type::Ptr(_) | Type::Bool | Type::Float(_))
                ) || !matches!(
                    self.builder.value_type(r_raw),
                    Some(Type::Int | Type::Ptr(_) | Type::Bool | Type::Float(_))
                ) {
                    return Some(
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw(),
                    );
                }

                // Resolve projected MIR types for accurate annotations.
                let lhs_mir_ty = operand_ty_projected(lhs, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                    .unwrap_or(self.tcx.types.i32);
                let rhs_mir_ty = operand_ty_projected(rhs, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                    .unwrap_or(self.tcx.types.i32);

                // Recompute annotations from the fully-resolved MIR types.
                // `operand_annotation` uses the local's type which misses
                // projections (e.g. `RET.fld1` where RET is a struct but
                // fld1 is i128).  The MIR types computed above resolve
                // through projections correctly.
                let l_ann = translate_annotation(lhs_mir_ty).or(l_ann);
                let r_ann = translate_annotation(rhs_mir_ty).or(r_ann);

                // Coerce pointer operands to integers — needed for both
                // arithmetic/bitwise ops and comparisons.
                let l = self.coerce_to_int(l_raw);
                let r = self.coerce_to_int(r_raw);
                let l_op = IrOperand {
                    value: l,
                    annotation: l_ann,
                };
                let r_op = IrOperand {
                    value: r,
                    annotation: r_ann,
                };
                let res_ann = Some(
                    l_ann
                        .and_then(|a| IntAnn::from_annotation(&a))
                        .or_else(|| r_ann.and_then(|a| IntAnn::from_annotation(&a)))
                        .or_else(|| {
                            // Fallback: use destination type
                            let dest_ty = dest_place.ty(&self.mir.local_decls, self.tcx).ty;
                            translate_annotation(dest_ty).and_then(|a| IntAnn::from_annotation(&a))
                        })
                        .unwrap_or(IntAnn::Unsigned(64)),
                );

                // Detect float operands for comparison fixup.
                let is_float_cmp = matches!(
                    op,
                    BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                        | BinOp::Eq
                        | BinOp::Ne
                        | BinOp::Cmp
                ) && float_ty.is_some();

                let val = match op {
                    // Wrapping integer arithmetic: use DontCare signedness at target bit width,
                    // then extend to proper signedness.
                    BinOp::Add => {
                        let bits = self.extract_result_bits(res_ann);
                        let sum = self
                            .builder
                            .add(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(sum, res_ann, bits)
                    }
                    BinOp::Sub => {
                        let bits = self.extract_result_bits(res_ann);
                        let diff = self
                            .builder
                            .sub(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(diff, res_ann, bits)
                    }
                    BinOp::Mul => {
                        let bits = self.extract_result_bits(res_ann);
                        let prod = self
                            .builder
                            .mul(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(prod, res_ann, bits)
                    }
                    // Unchecked variants: the caller guarantees no overflow so the
                    // result can carry a full Signed/Unsigned annotation directly.
                    BinOp::AddUnchecked => {
                        let ann = res_ann
                            .map(|a| match a {
                                IntAnn::Signed(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Signed,
                                },
                                IntAnn::Unsigned(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Unsigned,
                                },
                                IntAnn::DontCare(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::DontCare,
                                },
                            })
                            .unwrap_or(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            });
                        self.builder
                            .add(l_op.into(), r_op.into(), ann, Origin::synthetic())
                            .raw()
                    }
                    BinOp::SubUnchecked => {
                        let ann = res_ann
                            .map(|a| match a {
                                IntAnn::Signed(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Signed,
                                },
                                IntAnn::Unsigned(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Unsigned,
                                },
                                IntAnn::DontCare(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::DontCare,
                                },
                            })
                            .unwrap_or(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            });
                        self.builder
                            .sub(l_op.into(), r_op.into(), ann, Origin::synthetic())
                            .raw()
                    }
                    BinOp::MulUnchecked => {
                        let ann = res_ann
                            .map(|a| match a {
                                IntAnn::Signed(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Signed,
                                },
                                IntAnn::Unsigned(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Unsigned,
                                },
                                IntAnn::DontCare(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::DontCare,
                                },
                            })
                            .unwrap_or(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            });
                        self.builder
                            .mul(l_op.into(), r_op.into(), ann, Origin::synthetic())
                            .raw()
                    }
                    // Checked arithmetic: emit a multi-result IR intrinsic that
                    // produces (wrapping_result: Int, overflow: Bool).  The primary
                    // result is returned here and stored in `locals`; the secondary
                    // overflow flag is saved in `overflow_locals` for Field(1) access.
                    BinOp::AddWithOverflow => {
                        let bits = match res_ann {
                            Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => {
                                n
                            }
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                            self.builder.sadd_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        } else {
                            self.builder.uadd_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        };
                        self.overflow_locals.set(dest_place.local, overflow.raw());
                        primary.raw()
                    }
                    BinOp::SubWithOverflow => {
                        let bits = match res_ann {
                            Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => {
                                n
                            }
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                            self.builder.ssub_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        } else {
                            self.builder.usub_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        };
                        self.overflow_locals.set(dest_place.local, overflow.raw());
                        primary.raw()
                    }
                    BinOp::MulWithOverflow => {
                        let bits = match res_ann {
                            Some(IntAnn::Signed(n) | IntAnn::Unsigned(n) | IntAnn::DontCare(n)) => {
                                n
                            }
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(IntAnn::Signed(_))) {
                            self.builder.smul_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        } else {
                            self.builder.umul_with_overflow(
                                l_op.into(),
                                r_op.into(),
                                bits,
                                Origin::synthetic(),
                            )
                        };
                        self.overflow_locals.set(dest_place.local, overflow.raw());
                        primary.raw()
                    }
                    BinOp::Eq => {
                        if is_float_cmp {
                            self.builder
                                .fcmp(FCmpOp::OEq, l_raw.into(), r_raw.into(), Origin::synthetic())
                                .raw()
                        } else if is_fat_ptr(self.tcx, lhs_mir_ty) {
                            // Fat pointer equality: compare data AND metadata.
                            // For stack-local fat pointers, l_raw/r_raw hold
                            // slot addresses — load the actual data pointers.
                            let l_data = self.load_fat_data_for_operand(lhs, l_raw);
                            let l_data = self.coerce_to_int(l_data);
                            let r_data = self.load_fat_data_for_operand(rhs, r_raw);
                            let r_data = self.coerce_to_int(r_data);
                            let data_eq = self.builder.icmp(
                                ICmpOp::Eq,
                                IrOperand {
                                    value: l_data,
                                    annotation: int_annotation_for_bytes(8),
                                }
                                .into(),
                                IrOperand {
                                    value: r_data,
                                    annotation: int_annotation_for_bytes(8),
                                }
                                .into(),
                                Origin::synthetic(),
                            );
                            let l_meta = self.find_fat_metadata_for_operand(lhs);
                            let r_meta = self.find_fat_metadata_for_operand(rhs);
                            if let (Some(lm), Some(rm)) = (l_meta, r_meta) {
                                let lm_int = self.coerce_to_int(lm);
                                let rm_int = self.coerce_to_int(rm);
                                let meta_eq = self.builder.icmp(
                                    ICmpOp::Eq,
                                    IrOperand {
                                        value: lm_int,
                                        annotation: int_annotation_for_bytes(8),
                                    }
                                    .into(),
                                    IrOperand {
                                        value: rm_int,
                                        annotation: int_annotation_for_bytes(8),
                                    }
                                    .into(),
                                    Origin::synthetic(),
                                );
                                let d = self.coerce_to_int(data_eq.raw());
                                let m = self.coerce_to_int(meta_eq.raw());
                                self.builder
                                    .and(
                                        d.into(),
                                        m.into(),
                                        IntAnnotation {
                                            bit_width: 64,
                                            signedness: IntSignedness::Unsigned,
                                        },
                                        Origin::synthetic(),
                                    )
                                    .raw()
                            } else {
                                data_eq.raw()
                            }
                        } else {
                            self.builder
                                .icmp(ICmpOp::Eq, l_op.into(), r_op.into(), Origin::synthetic())
                                .raw()
                        }
                    }
                    BinOp::Ne => {
                        if is_float_cmp {
                            self.builder
                                .fcmp(FCmpOp::UNe, l_raw.into(), r_raw.into(), Origin::synthetic())
                                .raw()
                        } else if is_fat_ptr(self.tcx, lhs_mir_ty) {
                            // Fat pointer inequality: data OR metadata differs.
                            let l_data = self.load_fat_data_for_operand(lhs, l_raw);
                            let l_data = self.coerce_to_int(l_data);
                            let r_data = self.load_fat_data_for_operand(rhs, r_raw);
                            let r_data = self.coerce_to_int(r_data);
                            let data_ne = self.builder.icmp(
                                ICmpOp::Ne,
                                IrOperand {
                                    value: l_data,
                                    annotation: int_annotation_for_bytes(8),
                                }
                                .into(),
                                IrOperand {
                                    value: r_data,
                                    annotation: int_annotation_for_bytes(8),
                                }
                                .into(),
                                Origin::synthetic(),
                            );
                            let l_meta = self.find_fat_metadata_for_operand(lhs);
                            let r_meta = self.find_fat_metadata_for_operand(rhs);
                            if let (Some(lm), Some(rm)) = (l_meta, r_meta) {
                                let lm_int = self.coerce_to_int(lm);
                                let rm_int = self.coerce_to_int(rm);
                                let meta_ne = self.builder.icmp(
                                    ICmpOp::Ne,
                                    IrOperand {
                                        value: lm_int,
                                        annotation: int_annotation_for_bytes(8),
                                    }
                                    .into(),
                                    IrOperand {
                                        value: rm_int,
                                        annotation: int_annotation_for_bytes(8),
                                    }
                                    .into(),
                                    Origin::synthetic(),
                                );
                                let d = self.coerce_to_int(data_ne.raw());
                                let m = self.coerce_to_int(meta_ne.raw());
                                self.builder
                                    .or(
                                        d.into(),
                                        m.into(),
                                        IntAnnotation {
                                            bit_width: 64,
                                            signedness: IntSignedness::Unsigned,
                                        },
                                        Origin::synthetic(),
                                    )
                                    .raw()
                            } else {
                                data_ne.raw()
                            }
                        } else {
                            self.builder
                                .icmp(ICmpOp::Ne, l_op.into(), r_op.into(), Origin::synthetic())
                                .raw()
                        }
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        if is_float_cmp {
                            let fcmp_op = match op {
                                BinOp::Lt => FCmpOp::OLt,
                                BinOp::Le => FCmpOp::OLe,
                                BinOp::Gt => FCmpOp::OGt,
                                _ => FCmpOp::OGe,
                            };
                            self.builder
                                .fcmp(fcmp_op, l_raw.into(), r_raw.into(), Origin::synthetic())
                                .raw()
                        } else {
                            let icmp_op = match op {
                                BinOp::Lt => ICmpOp::Lt,
                                BinOp::Le => ICmpOp::Le,
                                BinOp::Gt => ICmpOp::Gt,
                                _ => ICmpOp::Ge,
                            };
                            self.builder
                                .icmp(icmp_op, l_op.into(), r_op.into(), Origin::synthetic())
                                .raw()
                        }
                    }
                    BinOp::Cmp => {
                        // Three-way comparison returning Ordering (-1/0/1).
                        // Result = (l > r) as i8 - (l < r) as i8
                        if is_float_cmp {
                            let fty = float_ty.unwrap();
                            let l_f = self.builder.bitcast(
                                l.into(),
                                fty.clone(),
                                None,
                                Origin::synthetic(),
                            );
                            let r_f =
                                self.builder
                                    .bitcast(r.into(), fty, None, Origin::synthetic());
                            let lt = self.builder.fcmp(
                                FCmpOp::OLt,
                                l_f.into(),
                                r_f.into(),
                                Origin::synthetic(),
                            );
                            let one = self.builder.iconst(
                                1,
                                8,
                                IntSignedness::Signed,
                                Origin::synthetic(),
                            );
                            let zero = self.builder.iconst(
                                0,
                                8,
                                IntSignedness::Signed,
                                Origin::synthetic(),
                            );
                            let lt_int = self.builder.select(
                                lt.into(),
                                one.into(),
                                zero.into(),
                                Type::Int,
                                Some(Annotation::Int(IntAnnotation {
                                    bit_width: 8,
                                    signedness: IntSignedness::Signed,
                                })),
                                Origin::synthetic(),
                            );
                            let gt = self.builder.fcmp(
                                FCmpOp::OGt,
                                l_f.into(),
                                r_f.into(),
                                Origin::synthetic(),
                            );
                            let gt_int = self.builder.select(
                                gt.into(),
                                one.into(),
                                zero.into(),
                                Type::Int,
                                Some(Annotation::Int(IntAnnotation {
                                    bit_width: 8,
                                    signedness: IntSignedness::Signed,
                                })),
                                Origin::synthetic(),
                            );
                            self.builder
                                .sub(
                                    gt_int.into(),
                                    lt_int.into(),
                                    IntAnnotation {
                                        bit_width: 8,
                                        signedness: IntSignedness::Signed,
                                    },
                                    Origin::synthetic(),
                                )
                                .raw()
                        } else {
                            let lt = self.builder.icmp(
                                ICmpOp::Lt,
                                l_op.clone().into(),
                                r_op.clone().into(),
                                Origin::synthetic(),
                            );
                            let one = self.builder.iconst(
                                1,
                                8,
                                IntSignedness::Signed,
                                Origin::synthetic(),
                            );
                            let zero = self.builder.iconst(
                                0,
                                8,
                                IntSignedness::Signed,
                                Origin::synthetic(),
                            );
                            let lt_int = self.builder.select(
                                lt.into(),
                                one.into(),
                                zero.into(),
                                Type::Int,
                                Some(Annotation::Int(IntAnnotation {
                                    bit_width: 8,
                                    signedness: IntSignedness::Signed,
                                })),
                                Origin::synthetic(),
                            );
                            let gt = self.builder.icmp(
                                ICmpOp::Gt,
                                l_op.into(),
                                r_op.into(),
                                Origin::synthetic(),
                            );
                            let gt_int = self.builder.select(
                                gt.into(),
                                one.into(),
                                zero.into(),
                                Type::Int,
                                Some(Annotation::Int(IntAnnotation {
                                    bit_width: 8,
                                    signedness: IntSignedness::Signed,
                                })),
                                Origin::synthetic(),
                            );
                            self.builder
                                .sub(
                                    gt_int.into(),
                                    lt_int.into(),
                                    IntAnnotation {
                                        bit_width: 8,
                                        signedness: IntSignedness::Signed,
                                    },
                                    Origin::synthetic(),
                                )
                                .raw()
                        }
                    }
                    BinOp::Shl | BinOp::ShlUnchecked => {
                        let bits = self.extract_result_bits(res_ann);
                        let shift_val = r_op.value;
                        let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                        let mask_val = self.builder.iconst(
                            lhs_bits - 1,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let masked = self.builder.and(
                            shift_val.into(),
                            mask_val.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            },
                            Origin::synthetic(),
                        );
                        let masked_op = IrOperand {
                            value: masked.raw(),
                            annotation: None,
                        };
                        let shifted = self
                            .builder
                            .shl(
                                l_op.into(),
                                masked_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(shifted, res_ann, bits)
                    }
                    BinOp::BitOr => {
                        let bits = self.extract_result_bits(res_ann);
                        let result = self
                            .builder
                            .or(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(result, res_ann, bits)
                    }
                    BinOp::BitAnd => {
                        let bits = self.extract_result_bits(res_ann);
                        let result = self
                            .builder
                            .and(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(result, res_ann, bits)
                    }
                    BinOp::BitXor => {
                        let bits = self.extract_result_bits(res_ann);
                        let result = self
                            .builder
                            .xor(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness: IntSignedness::DontCare,
                                },
                                Origin::synthetic(),
                            )
                            .raw();
                        self.apply_int_extension(result, res_ann, bits)
                    }
                    BinOp::Shr | BinOp::ShrUnchecked => {
                        let shift_val = r_op.value;
                        let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                        let mask_val = self.builder.iconst(
                            lhs_bits - 1,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let masked = self.builder.and(
                            shift_val.into(),
                            mask_val.into(),
                            IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            },
                            Origin::synthetic(),
                        );
                        let masked_op = IrOperand {
                            value: masked.raw(),
                            annotation: None,
                        };
                        let int_ann = res_ann
                            .map(|ia| match ia {
                                IntAnn::Signed(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Signed,
                                },
                                IntAnn::Unsigned(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::Unsigned,
                                },
                                IntAnn::DontCare(n) => IntAnnotation {
                                    bit_width: n,
                                    signedness: IntSignedness::DontCare,
                                },
                            })
                            .unwrap_or(IntAnnotation {
                                bit_width: 64,
                                signedness: IntSignedness::DontCare,
                            });
                        self.builder
                            .shr(l_op.into(), masked_op.into(), int_ann, Origin::synthetic())
                            .raw()
                    }
                    BinOp::Div => {
                        let bits = self.extract_result_bits(res_ann);
                        let signedness = match res_ann {
                            Some(IntAnn::Signed(_)) => IntSignedness::Signed,
                            Some(IntAnn::Unsigned(_)) => IntSignedness::Unsigned,
                            _ => IntSignedness::DontCare,
                        };
                        self.builder
                            .div(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness,
                                },
                                Origin::synthetic(),
                            )
                            .raw()
                    }
                    BinOp::Rem => {
                        let bits = self.extract_result_bits(res_ann);
                        let signedness = match res_ann {
                            Some(IntAnn::Signed(_)) => IntSignedness::Signed,
                            Some(IntAnn::Unsigned(_)) => IntSignedness::Unsigned,
                            _ => IntSignedness::DontCare,
                        };
                        self.builder
                            .rem(
                                l_op.into(),
                                r_op.into(),
                                IntAnnotation {
                                    bit_width: bits,
                                    signedness,
                                },
                                Origin::synthetic(),
                            )
                            .raw()
                    }
                    BinOp::Offset => {
                        // ptr.wrapping_offset(count) = ptr + count * sizeof(T).
                        let l_raw = self.translate_operand(lhs)?;
                        let r = self.translate_operand(rhs)?;
                        let pointee_ty = operand_ty_projected(lhs, self.mir, self.tcx)
                            .map(|ty| self.monomorphize(ty))
                            .and_then(|ty| match ty.kind() {
                                ty::RawPtr(inner, _) => Some(*inner),
                                _ => None,
                            });
                        let elem_size =
                            pointee_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(1);
                        let byte_offset = if elem_size == 1 {
                            r
                        } else {
                            let size_val = self.builder.iconst(
                                elem_size as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .mul(
                                    r.into(),
                                    size_val.into(),
                                    IntAnnotation {
                                        bit_width: 64,
                                        signedness: IntSignedness::DontCare,
                                    },
                                    Origin::synthetic(),
                                )
                                .raw()
                        };
                        let ptr = self.coerce_to_ptr(l_raw);
                        self.builder
                            .ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic())
                            .raw()
                    }
                };
                Some(val)
            }
            // PLACEHOLDER_REMAINING_RVALUE_ARMS
            Rvalue::Use(operand) => self.translate_operand(operand),
            Rvalue::Cast(kind, operand, target_ty) => {
                let val = self.translate_operand(operand)?;
                match kind {
                    CastKind::IntToInt => {
                        // Use projected type so field accesses like
                        // _struct.field resolve to the field type, not
                        // the struct type.
                        let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx) else {
                            return Some(val);
                        };
                        let src_ty = self.monomorphize(src_ty);
                        // `translate_place_to_value` returns the *address* of the
                        // field (as a Ptr) for >8-byte types so the assignment
                        // handler can do a word-by-word copy.  When this address
                        // is used as the source of an IntToInt cast we must load
                        // the actual integer value from memory first; otherwise
                        // `coerce_to_int` below would convert the address itself
                        // to an integer (ptrtoaddr), producing the wrong result.
                        // This only applies when the target type fits in 64 bits;
                        // 128-bit → 128-bit casts go through the wide_pair path.
                        let target_ty_m = self.monomorphize(*target_ty);
                        let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                        let dst_size = type_size(self.tcx, target_ty_m).unwrap_or(0);
                        if src_size > 8
                            && dst_size > 8
                            && src_ty.is_integral()
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                        {
                            // Both source and target are >8-byte integers (e.g.
                            // i128 → u128).  Load the full value now to capture
                            // the correct memory state.  Returning the Ptr would
                            // defer the load to use-time, reading stale data if
                            // the source memory is overwritten in between.
                            let ann = translate_annotation(src_ty)
                                .or_else(|| int_annotation_for_bytes(src_size as u32));
                            let loaded = self.builder.load(
                                val.into(),
                                src_size as u32,
                                Type::Int,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                        let val = if src_size > 8
                            && src_ty.is_integral()
                            && dst_size <= 8
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                        {
                            // Load the low 8 bytes (little-endian) which hold
                            // bits [0..63] of the 128-bit integer — sufficient
                            // for any narrowing cast to ≤64-bit targets.
                            self.builder.load(
                                val.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            )
                        } else {
                            val
                        };
                        // Bool is Type::Bool in IR but IntToInt casts need Int operands.
                        let val = self.coerce_to_int(val);
                        translate_int_to_int_cast(src_ty, *target_ty, val, &mut self.builder)
                    }
                    CastKind::PointerCoercion(..) => {
                        // Convert a zero-sized function item / closure to a function pointer.
                        let Some(src_ty) = operand_ty(operand, self.mir) else {
                            return Some(val);
                        };
                        let src_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                            self.instance.args,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(src_ty),
                        );
                        let resolved = match src_ty.kind() {
                            ty::FnDef(def_id, args) => ty::Instance::try_resolve(
                                self.tcx,
                                ty::TypingEnv::fully_monomorphized(),
                                *def_id,
                                args,
                            )
                            .ok()
                            .flatten(),
                            ty::Closure(def_id, args) => Some(Instance::resolve_closure(
                                self.tcx,
                                *def_id,
                                args,
                                ty::ClosureKind::FnOnce,
                            )),
                            _ => None,
                        };
                        if let Some(resolved) = resolved {
                            let sym_name = self.tcx.symbol_name(resolved).name.to_string();
                            self.referenced_instances.push(resolved);
                            let sym_id = self.symbols.intern(&sym_name);
                            Some(self.builder.symbol_addr(sym_id, Origin::synthetic()).raw())
                        } else {
                            Some(val)
                        }
                    }
                    CastKind::FloatToInt => {
                        let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                            .map(|ty| self.monomorphize(ty))
                        else {
                            return Some(val);
                        };
                        let ft = match src_ty.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(val),
                        };
                        let target_ty_m = self.monomorphize(*target_ty);
                        let signed = matches!(target_ty_m.kind(), ty::Int(_));
                        let bit_width = type_size(self.tcx, target_ty_m)
                            .map(|s| s * 8)
                            .unwrap_or(64);

                        // `val` may be Float (when loaded from a struct field) or Int
                        // (the bit-pattern convention used for scalars). Normalise to
                        // both forms so we can use the right one below.
                        let val_is_float =
                            matches!(self.builder.value_type(val), Some(Type::Float(_)));
                        let float_val = if val_is_float {
                            val
                        } else {
                            self.builder.bitcast(
                                val.into(),
                                Type::Float(ft),
                                None,
                                Origin::synthetic(),
                            )
                        };
                        let int_bits_val = if val_is_float {
                            let bits = match ft {
                                FloatType::F16 | FloatType::BF16 => 16,
                                FloatType::F32 => 32,
                                FloatType::F64 => 64,
                                FloatType::F128 => 128,
                            };
                            self.builder.bitcast(
                                val.into(),
                                Type::Int,
                                int_annotation_for_bytes(bits / 8),
                                Origin::synthetic(),
                            )
                        } else {
                            val
                        };
                        // For 128-bit targets, fp_to_ui/fp_to_si only produce 64-bit results.
                        // Convert to 64-bit first, then extend.
                        let needs_extend = bit_width > 64;
                        let raw = if signed {
                            self.builder
                                .fp_to_si(float_val.into(), 64, Origin::synthetic())
                        } else {
                            self.builder
                                .fp_to_ui(float_val.into(), 64, Origin::synthetic())
                        };

                        // Float constants for saturation checks.
                        // cvttss2si returns INT64_MIN for out-of-range and NaN, so we must
                        // detect these cases using float comparisons and apply correct Rust
                        // saturating semantics:
                        //   NaN → 0, positive overflow → MAX, negative overflow → MIN (or 0 for unsigned)
                        let (two63_bits, two64_bits) = match ft {
                            FloatType::F32 => (0x5F00_0000_i64, 0x5F80_0000_i64),
                            // F64/others: 2^63 and 2^64 as f64 bit patterns
                            _ => (0x43E0_0000_0000_0000_i64, 0x43F0_0000_0000_0000_i64),
                        };
                        let two63_int = self.builder.iconst(
                            two63_bits,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let two63_float = self.builder.bitcast(
                            two63_int.into(),
                            Type::Float(ft),
                            None,
                            Origin::synthetic(),
                        );

                        // Rust's FloatToInt is saturating: clamp to target range.
                        let result = if needs_extend {
                            // For 128-bit types, fp_to_ui/fp_to_si produce 64-bit results.
                            // Explicitly extend to 128 bits.
                            if signed {
                                self.builder
                                    .sext(raw.into(), 128, Origin::synthetic())
                                    .raw()
                            } else {
                                self.builder
                                    .zext(raw.into(), 128, Origin::synthetic())
                                    .raw()
                            }
                        } else if signed {
                            // Signed: fix cvttss2si sentinel for NaN and positive overflow.
                            // For negative overflow, cvttss2si returns i64::MIN which is correct.
                            let is_nan = self.builder.fcmp(
                                FCmpOp::Uno,
                                float_val.into(),
                                float_val.into(),
                                Origin::synthetic(),
                            );
                            let is_large = self.builder.fcmp(
                                FCmpOp::OGe,
                                float_val.into(),
                                two63_float.into(),
                                Origin::synthetic(),
                            );
                            let zero = self.builder.iconst(
                                0,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let i64_max = self.builder.iconst(
                                i64::MAX,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            // Apply corrections: NaN → 0, then positive overflow → i64::MAX
                            let corrected = self.builder.select(
                                is_nan.into(),
                                zero.into(),
                                raw.into(),
                                Type::Int,
                                default_int_annotation(),
                                Origin::synthetic(),
                            );
                            let corrected = self.builder.select(
                                is_large.into(),
                                i64_max.into(),
                                corrected.into(),
                                Type::Int,
                                default_int_annotation(),
                                Origin::synthetic(),
                            );
                            if bit_width < 64 {
                                // Clamp to [INT_MIN_of_width, INT_MAX_of_width].
                                // After corrections, corrected ∈ {0, i64::MAX, or cvttss2si result
                                // which is in [-2^63, 2^63-1]}.  Signed min/max works correctly.
                                let lo = -(1i64 << (bit_width - 1));
                                let hi = (1i64 << (bit_width - 1)) - 1;
                                let lo_c = self.builder.iconst(
                                    lo,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let hi_c = self.builder.iconst(
                                    hi,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let clamped_hi = self.builder.min(
                                    corrected.into(),
                                    hi_c.into(),
                                    signed_int_ann_for_bytes(8),
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .max(
                                        clamped_hi.into(),
                                        lo_c.into(),
                                        signed_int_ann_for_bytes(8),
                                        Origin::synthetic(),
                                    )
                                    .raw()
                            } else {
                                corrected
                            }
                        } else {
                            // Unsigned: full saturating conversion.
                            // NaN → 0, negative → 0, [0, 2^63) → direct, [2^63, 2^64) → two-range,
                            // >= 2^64 → UINT64_MAX (for 64-bit) or UINT_MAX_of_width (for narrower).
                            let is_nan = self.builder.fcmp(
                                FCmpOp::Uno,
                                float_val.into(),
                                float_val.into(),
                                Origin::synthetic(),
                            );
                            // Detect float >= 2^63 (overflow for u32/u16/u8 and start of large range
                            // for u64).
                            let is_large = self.builder.fcmp(
                                FCmpOp::OGe,
                                float_val.into(),
                                two63_float.into(),
                                Origin::synthetic(),
                            );
                            let zero = self.builder.iconst(
                                0,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            if bit_width < 64 {
                                // For u32/u16/u8: float >= 2^63 is always an overflow (> UINT_MAX).
                                // cvttss2si is correct for float in [-2^63, 2^63): negative → negative
                                // i64, clamped to 0; in-range → correct; overflow beyond hi → large
                                // positive i64, clamped to hi.
                                let hi = (1i64 << bit_width) - 1;
                                let hi_c = self.builder.iconst(
                                    hi,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let clamped = self.builder.min(
                                    raw.into(),
                                    hi_c.into(),
                                    signed_int_ann_for_bytes(8),
                                    Origin::synthetic(),
                                );
                                let clamped = self.builder.max(
                                    clamped.into(),
                                    zero.into(),
                                    signed_int_ann_for_bytes(8),
                                    Origin::synthetic(),
                                );
                                // Override: float >= 2^63 → hi (overflow), NaN → 0.
                                let clamped = self.builder.select(
                                    is_large.into(),
                                    hi_c.into(),
                                    clamped.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                );
                                self.builder.select(
                                    is_nan.into(),
                                    zero.into(),
                                    clamped.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                )
                            } else {
                                // u64: two-range implementation.
                                // [0, 2^63):   cvttss2si gives correct result.
                                // [2^63, 2^64): subtract 2^63, convert, add 2^63 via bitwise OR.
                                // >= 2^64:      saturate to UINT64_MAX.
                                let two64_int = self.builder.iconst(
                                    two64_bits,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let two64_float = self.builder.bitcast(
                                    two64_int.into(),
                                    Type::Float(ft),
                                    None,
                                    Origin::synthetic(),
                                );
                                let is_huge = self.builder.fcmp(
                                    FCmpOp::OGe,
                                    float_val.into(),
                                    two64_float.into(),
                                    Origin::synthetic(),
                                );
                                // Large range [2^63, 2^64): shift float down, convert, shift back.
                                let flags = FpRewriteFlags::default();
                                let float_shifted = self.builder.fsub(
                                    float_val.into(),
                                    two63_float.into(),
                                    flags,
                                    Type::Float(ft),
                                    Origin::synthetic(),
                                );
                                let raw_shifted = self.builder.fp_to_ui(
                                    float_shifted.into(),
                                    64,
                                    Origin::synthetic(),
                                );
                                let sign_bit = self.builder.iconst(
                                    i64::MIN,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let result_large = self.builder.or(
                                    raw_shifted.into(),
                                    sign_bit.into(),
                                    IntAnnotation {
                                        bit_width: 64,
                                        signedness: IntSignedness::DontCare,
                                    },
                                    Origin::synthetic(),
                                );
                                let max_u64 = self.builder.iconst(
                                    -1_i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                // Select in order: normal → large → huge → nan_or_neg
                                let tentative = self.builder.select(
                                    is_large.into(),
                                    result_large.into(),
                                    raw.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                );
                                let tentative = self.builder.select(
                                    is_huge.into(),
                                    max_u64.into(),
                                    tentative.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                );
                                // NaN or negative → 0 (NaN check must come after is_huge
                                // so that positive NaN doesn't get UINT64_MAX).
                                let sign_bit_pos: u32 = match ft {
                                    FloatType::F32 => 31,
                                    _ => 63,
                                };
                                let shift_c = self.builder.iconst(
                                    sign_bit_pos as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let sign = self.builder.shr(
                                    int_bits_val.into(),
                                    shift_c.into(),
                                    int_ann_for_bytes(8),
                                    Origin::synthetic(),
                                );
                                let one = self.builder.iconst(
                                    1,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let sign_masked = self.builder.and(
                                    sign.into(),
                                    one.into(),
                                    IntAnnotation {
                                        bit_width: 64,
                                        signedness: IntSignedness::DontCare,
                                    },
                                    Origin::synthetic(),
                                );
                                let zero_cmp = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let is_neg = self.builder.icmp(
                                    ICmpOp::Ne,
                                    sign_masked.into(),
                                    zero_cmp.into(),
                                    Origin::synthetic(),
                                );
                                let tentative = self.builder.select(
                                    is_neg.into(),
                                    zero.into(),
                                    tentative.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                );
                                self.builder.select(
                                    is_nan.into(),
                                    zero.into(),
                                    tentative.into(),
                                    Type::Int,
                                    default_int_annotation(),
                                    Origin::synthetic(),
                                )
                            }
                        };
                        Some(result)
                    }
                    CastKind::IntToFloat => {
                        let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                            .map(|ty| self.monomorphize(ty))
                        else {
                            return Some(val);
                        };
                        let signed = matches!(src_ty.kind(), ty::Int(_));
                        let target_ty_m = self.monomorphize(*target_ty);
                        let ft = match target_ty_m.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(val),
                        };

                        let src_size = type_size(self.tcx, src_ty).unwrap_or(8);
                        // When val is a Ptr (address of a >8-byte int like
                        // i128/u128), load the full value so the legalizer can
                        // split it.  Without this, coerce_to_int would convert
                        // the address itself into an integer via ptrtoaddr.
                        let int_val = if src_size > 8
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                        {
                            let ann = if signed {
                                signed_int_annotation_for_bytes(src_size as u32)
                            } else {
                                int_annotation_for_bytes(src_size as u32)
                            };
                            self.builder.load(
                                val.into(),
                                src_size as u32,
                                Type::Int,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            )
                        } else {
                            self.coerce_to_int(val)
                        };

                        // Set annotation so the isel can sign/zero-extend narrow
                        // integers before cvtsi2ss/cvtsi2sd.  The x86 instruction
                        // operates on a full 64-bit value; without sign-extension
                        // a byte like 0xDA (-38 as i8) would be seen as 218.
                        let annotation = if src_size > 0 {
                            let bits = (src_size * 8) as u32;
                            Some(if signed {
                                IntAnn::Signed(bits)
                            } else {
                                IntAnn::Unsigned(bits)
                            })
                        } else {
                            None
                        };

                        let operand = if let Some(ann) = annotation {
                            tuffy_ir::instruction::Operand::annotated(int_val, ann.to_annotation())
                        } else {
                            int_val.into()
                        };
                        let float_res = if signed {
                            self.builder
                                .si_to_fp(operand.into(), ft, Origin::synthetic())
                        } else {
                            self.builder
                                .ui_to_fp(operand.into(), ft, Origin::synthetic())
                        };
                        Some(float_res.raw())
                    }
                    CastKind::FloatToFloat => {
                        let Some(src_ty) = operand_ty_projected(operand, self.mir, self.tcx)
                            .map(|ty| self.monomorphize(ty))
                        else {
                            return Some(val);
                        };
                        let src_ft = match src_ty.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(val),
                        };
                        let target_ty_m = self.monomorphize(*target_ty);
                        let dst_ft = match target_ty_m.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(val),
                        };
                        if src_ft == dst_ft {
                            return Some(val);
                        }
                        // Convert between float formats; val is already Float(src_ft).
                        let converted =
                            self.builder
                                .fp_convert(val.into(), dst_ft, Origin::synthetic());
                        Some(converted.raw())
                    }
                    // PLACEHOLDER_CATCH_ALL_CAST
                    // Pointer casts and transmutes are bitwise moves.
                    _ => {
                        let target_ty_mono = self.monomorphize(*target_ty);
                        if is_fat_ptr(self.tcx, target_ty_mono)
                            && let Operand::Copy(src) | Operand::Move(src) = operand
                            && !src.projection.is_empty()
                        {
                            let src_ty = src.ty(&self.mir.local_decls, self.tcx).ty;
                            let src_ty = self.monomorphize(src_ty);
                            let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                            if src_size > 8 && !is_fat_ptr(self.tcx, src_ty) {
                                // val is an address; load the data pointer.
                                let ptr_val = self.coerce_to_ptr(val);
                                let data = self.builder.load(
                                    ptr_val.into(),
                                    8,
                                    Type::Ptr(0),
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                return Some(data);
                            }
                        }
                        // PtrToPtr from a large stack local
                        if matches!(kind, CastKind::PtrToPtr) {
                            let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                            if target_size > 0
                                && target_size <= 8
                                && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                                && let Operand::Copy(src) | Operand::Move(src) = operand
                                && src.projection.is_empty()
                                && self.stack_locals.is_stack(src.local)
                            {
                                let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                                let src_size = type_size(self.tcx, src_ty).unwrap_or(0);
                                if src_size > 8 {
                                    let ir_ty =
                                        translate_ty(self.tcx, target_ty_mono).unwrap_or(Type::Int);
                                    let ann = if matches!(ir_ty, Type::Int) {
                                        int_annotation_for_bytes(target_size as u32)
                                    } else {
                                        None
                                    };
                                    let data = self.builder.load(
                                        val.into(),
                                        target_size as u32,
                                        ir_ty,
                                        self.current_mem.into(),
                                        ann,
                                        Origin::synthetic(),
                                    );
                                    return Some(data);
                                }
                            }
                        }
                        // Transmute from a stack local into an integral type.
                        // Load the target-sized value directly from the source slot
                        // instead of returning the pointer.  Returning the pointer
                        // would make the destination alias the source slot, causing
                        // later independent writes to both locals to corrupt each other.
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                            && let Operand::Copy(src) | Operand::Move(src) = operand
                            && src.projection.is_empty()
                            && self.stack_locals.is_stack(src.local)
                        {
                            let src_ty = self.monomorphize(self.mir.local_decls[src.local].ty);
                            // If the source local's MIR type is a pointer,
                            // translate_operand already loaded the pointer
                            // value from the stack slot.  Use ptrtoaddr to
                            // convert the address to an integer instead of
                            // dereferencing through it.
                            if matches!(src_ty.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                                && target_ty_mono.is_integral()
                            {
                                return Some(
                                    self.builder
                                        .ptrtoaddr(val.into(), 64, Origin::synthetic())
                                        .raw(),
                                );
                            }
                            let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                            let target_ir_ty = translate_ty(self.tcx, target_ty_mono);
                            if target_size > 0
                                && matches!(target_ir_ty, Some(Type::Int | Type::Float(_)))
                            {
                                let load_ty = target_ir_ty.unwrap();
                                let ann = if matches!(load_ty, Type::Int) {
                                    int_annotation_for_bytes(target_size as u32)
                                } else {
                                    None
                                };
                                let loaded = self.builder.load(
                                    val.into(),
                                    target_size as u32,
                                    load_ty,
                                    self.current_mem.into(),
                                    ann,
                                    Origin::synthetic(),
                                );
                                return Some(loaded);
                            }
                        }
                        // Transmute from a projected address (e.g. _3.0.0 where
                        // the projected type is a fat-pointer-sized ADT wrapper
                        // like NonNull<[T]>) to a fat raw pointer.  Val is a
                        // memory address; load only the data pointer (first 8
                        // bytes).  The metadata (second 8 bytes) is handled by
                        // extract_fat_component in the statement handler.
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                            && self.builder.is_memory_address(val)
                            && is_fat_ptr(self.tcx, target_ty_mono)
                            && let Operand::Copy(src) | Operand::Move(src) = operand
                            && !src.projection.is_empty()
                        {
                            let data_ptr = self.builder.load(
                                val.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            return Some(data_ptr);
                        }
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Int | Type::Bool))
                            && let Some(Type::Float(ft)) = translate_ty(self.tcx, target_ty_mono)
                        {
                            let size = type_size(self.tcx, target_ty_mono).unwrap_or(0) as u32;
                            if size > 0 && size <= 16 {
                                let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                                self.current_mem = self
                                    .builder
                                    .store(
                                        val.into(),
                                        slot.into(),
                                        size,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                let loaded = self.builder.load(
                                    slot.into(),
                                    size,
                                    Type::Float(ft),
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                return Some(loaded);
                            }
                        }
                        // Transmute from a Float register value to an Int type:
                        // reinterpret via a temporary stack slot.
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Float(_)))
                            && matches!(translate_ty(self.tcx, target_ty_mono), Some(Type::Int))
                        {
                            let size = type_size(self.tcx, target_ty_mono).unwrap_or(0) as u32;
                            if size > 0 && size <= 16 {
                                let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                                self.current_mem = self
                                    .builder
                                    .store(
                                        val.into(),
                                        slot.into(),
                                        size,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                let ann = int_annotation_for_bytes(size);
                                let loaded = self.builder.load(
                                    slot.into(),
                                    size,
                                    Type::Int,
                                    self.current_mem.into(),
                                    ann,
                                    Origin::synthetic(),
                                );
                                return Some(loaded);
                            }
                        }
                        // Transmute / PtrToPtr from a pointer-typed source
                        // to a non-pointer target (integer type only).
                        if matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                            && target_ty_mono.is_integral()
                        {
                            let src_ty = operand_ty_projected(operand, self.mir, self.tcx)
                                .map(|ty| self.monomorphize(ty));
                            if let Some(st) = src_ty
                                && matches!(st.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                            {
                                // If val is still a memory address (e.g. fat
                                // pointer in a stack slot), load the thin
                                // pointer first.  Skip the load for non-stack
                                // simple locals whose value is a stack_slot from
                                // `&raw mut` aliasing — val IS the pointer, not a
                                // location storing a pointer.
                                let is_aliased_ptr = matches!(
                                    operand,
                                    Operand::Copy(src) | Operand::Move(src)
                                        if src.projection.is_empty()
                                            && !self.stack_locals.is_stack(src.local)
                                );
                                let ptr_val =
                                    if self.builder.is_memory_address(val) && !is_aliased_ptr {
                                        self.builder.load(
                                            val.into(),
                                            8,
                                            Type::Ptr(0),
                                            self.current_mem.into(),
                                            None,
                                            Origin::synthetic(),
                                        )
                                    } else {
                                        val
                                    };
                                return Some(
                                    self.builder
                                        .ptrtoaddr(ptr_val.into(), 64, Origin::synthetic())
                                        .raw(),
                                );
                            }
                        }
                        // Transmute from Bool to an integer type: materialize
                        // the 0/1 integer value so downstream integer ops
                        // (bitwise NOT, shifts, etc.) see Type::Int, not Bool.
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Bool))
                            && target_ty_mono.is_integral()
                        {
                            return Some(self.coerce_to_int(val));
                        }
                        // Transmute / cast from a memory address (e.g. projected
                        // field like RET.fld0) into an integral type.  Load the
                        // value now to avoid deferred-load aliasing bugs: if the
                        // source memory is overwritten before the local is used,
                        // the lazy load would read stale data.
                        if matches!(kind, CastKind::Transmute)
                            && matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                            && target_ty_mono.is_integral()
                        {
                            let target_size = type_size(self.tcx, target_ty_mono).unwrap_or(0);
                            if target_size > 0 {
                                let ann = int_annotation_for_bytes(target_size as u32);
                                let loaded = self.builder.load(
                                    val.into(),
                                    target_size as u32,
                                    Type::Int,
                                    self.current_mem.into(),
                                    ann,
                                    Origin::synthetic(),
                                );
                                return Some(loaded);
                            }
                        }
                        Some(val)
                    }
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if !place.projection.is_empty() {
                    let result = self.translate_place_to_addr(place).map(|(addr, _ty)| addr);
                    // When taking a Ref/RawPtr of a dereferenced fat pointer
                    // (e.g. `&raw const (*_3)` where `_3: &[u8]`), the result
                    // is itself a fat pointer that must preserve the metadata
                    // (length for slices, vtable for dyn).  translate_place_to_addr
                    // only returns the data pointer; reconstruct the full fat
                    // pointer in a 16-byte stack slot.
                    if let Some(data_ptr) = result {
                        let dest_ty = if dest_place.projection.is_empty() {
                            self.monomorphize(self.mir.local_decls[dest_place.local].ty)
                        } else {
                            self.monomorphize(dest_place.ty(&self.mir.local_decls, self.tcx).ty)
                        };
                        if is_fat_ptr(self.tcx, dest_ty) {
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
            // PLACEHOLDER_AGGREGATE
            Rvalue::Aggregate(kind, operands) => {
                // Extract enum variant index when constructing an enum.
                let enum_variant_idx = match kind.as_ref() {
                    mir::AggregateKind::Adt(def_id, variant_idx, _, _, _)
                        if self.tcx.adt_def(*def_id).is_enum() =>
                    {
                        Some(*variant_idx)
                    }
                    _ => None,
                };

                // NOTE: do NOT early-return 0 for empty operands — coroutines
                // (async blocks) can be non-ZST even with no captured upvars.
                // The total_size == 0 check below handles true ZSTs.

                // Determine the aggregate type for layout queries.
                let agg_ty = match kind.as_ref() {
                    mir::AggregateKind::Tuple => {
                        let ty = if dest_place.projection.is_empty() {
                            self.mir.local_decls[dest_place.local].ty
                        } else {
                            dest_place.ty(&self.mir.local_decls, self.tcx).ty
                        };
                        self.monomorphize(ty)
                    }
                    mir::AggregateKind::Adt(def_id, _, args, _, _) => {
                        let adt_def = self.tcx.adt_def(*def_id);
                        self.monomorphize(ty::Ty::new_adt(self.tcx, adt_def, args))
                    }
                    _ => {
                        let ty = if dest_place.projection.is_empty() {
                            self.mir.local_decls[dest_place.local].ty
                        } else {
                            dest_place.ty(&self.mir.local_decls, self.tcx).ty
                        };
                        self.monomorphize(ty)
                    }
                };
                let total_size = type_size(self.tcx, agg_ty).unwrap_or(if operands.is_empty() {
                    8
                } else {
                    8 * operands.len() as u64
                });
                if total_size == 0 {
                    return Some(
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw(),
                    );
                }
                // Reuse the destination local's existing stack slot when
                // available (e.g. sret-allocated _0) to avoid an intermediate
                // pointer-vs-data copy.
                let slot = if dest_place.projection.is_empty() {
                    if let Some(existing) = self.locals.get(dest_place.local) {
                        let ety = self.builder.value_type(existing).cloned();
                        if matches!(ety, Some(Type::Ptr(_))) {
                            existing
                        } else {
                            self.builder
                                .stack_slot(total_size as u32, 0, Origin::synthetic())
                        }
                    } else {
                        self.builder
                            .stack_slot(total_size as u32, 0, Origin::synthetic())
                    }
                } else {
                    self.builder
                        .stack_slot(total_size as u32, 0, Origin::synthetic())
                };

                // Zero-initialize the aggregate slot for enum variants,
                // coroutines (whose initial state discriminant must be 0),
                // or non-enum aggregates with no operands.
                let is_coroutine = matches!(kind.as_ref(), mir::AggregateKind::Coroutine(..));
                if (enum_variant_idx.is_some() || operands.is_empty() || is_coroutine)
                    && total_size > 0
                {
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
                    let num_words = total_size.div_ceil(8);
                    for w in 0..num_words {
                        let byte_off = w * 8;
                        let chunk = std::cmp::min(8, total_size - byte_off) as u32;
                        let dst = if byte_off == 0 {
                            slot
                        } else {
                            let off = self.builder.iconst(
                                byte_off as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                                .raw()
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                zero.into(),
                                dst.into(),
                                chunk,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }

                for (i, op) in operands.iter().enumerate() {
                    let field_ty = operand_ty_projected(op, self.mir, self.tcx)
                        .map(|ty| self.monomorphize(ty));
                    let bytes = field_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(8) as u32;
                    if bytes == 0 {
                        continue;
                    }
                    let val = self.translate_operand(op).unwrap_or_else(|| {
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw()
                    });

                    let offset = if let Some(variant_idx) = enum_variant_idx {
                        variant_field_offset(self.tcx, agg_ty, variant_idx, i)
                            .unwrap_or(i as u64 * 8)
                    } else {
                        field_offset(self.tcx, agg_ty, i).unwrap_or(i as u64 * 8)
                    };

                    let is_stack_op = match op {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            self.stack_locals.is_stack(p.local)
                        }
                        _ => false,
                    };

                    let dst_addr = if offset == 0 {
                        slot
                    } else {
                        let off_val = self.builder.iconst(
                            offset as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic())
                            .raw()
                    };

                    let is_ptr_val = matches!(self.builder.value_type(val), Some(Type::Ptr(_)));
                    // PLACEHOLDER_FAT_OP_AND_STORE
                    let fat_op = match op {
                        Operand::Copy(p) | Operand::Move(p)
                            if p.projection.is_empty() && !self.stack_locals.is_stack(p.local) =>
                        {
                            self.fat_locals.get(p.local)
                        }
                        Operand::Constant(c) if is_ptr_val && bytes > 8 => {
                            let mono_const = self.tcx.instantiate_and_normalize_erasing_regions(
                                self.instance.args,
                                ty::TypingEnv::fully_monomorphized(),
                                ty::EarlyBinder::bind(c.const_),
                            );
                            let resolved = match mono_const {
                                mir::Const::Val(v, _) => Some(v),
                                _ => {
                                    let typing_env = ty::TypingEnv::fully_monomorphized();
                                    mono_const.eval(self.tcx, typing_env, c.span).ok()
                                }
                            };
                            if let Some(mir::ConstValue::Slice { meta, .. }) = resolved {
                                Some(
                                    self.builder
                                        .iconst(
                                            meta as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        )
                                        .raw(),
                                )
                            } else if let Some(mir::ConstValue::Indirect { alloc_id, offset }) =
                                resolved
                            {
                                let const_ty = mono_const.ty();
                                if is_fat_ptr(self.tcx, const_ty) {
                                    let alloc = self.tcx.global_alloc(alloc_id);
                                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(
                                        mem_alloc,
                                    ) = alloc
                                    {
                                        let inner = mem_alloc.inner();
                                        let byte_offset = offset.bytes() as usize + 8;
                                        let len_bytes = inner
                                            .inspect_with_uninit_and_ptr_outside_interpreter(
                                                byte_offset..byte_offset + 8,
                                            );
                                        let len = u64::from_le_bytes(
                                            len_bytes.try_into().unwrap_or([0u8; 8]),
                                        );
                                        Some(
                                            self.builder
                                                .iconst(
                                                    len as i64,
                                                    64,
                                                    IntSignedness::DontCare,
                                                    Origin::synthetic(),
                                                )
                                                .raw(),
                                        )
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(fat_val) = fat_op {
                        // Store data pointer into dst[0..8].
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                dst_addr.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        // Store fat component (length/vtable) into dst[8..16].
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let hi = self.builder.ptradd(
                            dst_addr.into(),
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
                    } else if is_ptr_val && bytes > 8 {
                        // val is a pointer to multi-word data — copy word-by-word.
                        let num_words = (bytes as u64).div_ceil(8);
                        for w in 0..num_words {
                            let byte_off = w * 8;
                            let word_size = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                            let src = if byte_off == 0 {
                                val
                            } else {
                                let off = self.builder.iconst(
                                    byte_off as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .ptradd(val.into(), off.into(), 0, Origin::synthetic())
                                    .raw()
                            };
                            let word = self.builder.load(
                                src.into(),
                                word_size,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(word_size),
                                Origin::synthetic(),
                            );
                            let dst = if byte_off == 0 {
                                dst_addr
                            } else {
                                let off = self.builder.iconst(
                                    byte_off as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .ptradd(dst_addr.into(), off.into(), 0, Origin::synthetic())
                                    .raw()
                            };
                            self.current_mem = self
                                .builder
                                .store(
                                    word.into(),
                                    dst.into(),
                                    word_size,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                        }
                    } else if is_stack_op
                        && is_ptr_val
                        && bytes <= 8
                        && self.builder.stack_slot_size(val).is_some()
                    {
                        let loaded = self.builder.load(
                            val.into(),
                            bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(bytes),
                            Origin::synthetic(),
                        );
                        self.current_mem = self
                            .builder
                            .store(
                                loaded.into(),
                                dst_addr.into(),
                                bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    } else if is_ptr_val
                        && bytes <= 8
                        && self.builder.is_symbol_addr(val)
                        && self.is_indirect_nonref_const(op)
                    {
                        // Constant data pointer (e.g. symbol_addr for an
                        // Indirect const like `(TestFlags(0), true)`).
                        // `translate_const` returns `symbol_addr` for Indirect
                        // non-ref constants — the address of the data, not the
                        // data itself.  We need to load the actual value before
                        // storing it into the aggregate field.
                        let loaded = self.builder.load(
                            val.into(),
                            bytes,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(bytes),
                            Origin::synthetic(),
                        );
                        self.current_mem = self
                            .builder
                            .store(
                                loaded.into(),
                                dst_addr.into(),
                                bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    } else {
                        self.current_mem = self
                            .builder
                            .store(
                                val.into(),
                                dst_addr.into(),
                                bytes,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                }

                // Write the discriminant tag for enum aggregates.
                if let Some(variant_idx) = enum_variant_idx {
                    self.write_enum_tag(slot, agg_ty, variant_idx);
                }

                // Mark the destination local as stack-allocated.
                if dest_place.projection.is_empty() {
                    self.stack_locals.mark(dest_place.local);
                }
                Some(slot)
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
                        let cnt = count.try_to_target_usize(self.tcx).unwrap_or(0);
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
                    self.current_mem = self
                        .builder
                        .store(
                            elem_val.into(),
                            dst.into(),
                            store_size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
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
