use rustc_middle::mir::{self, CastKind, Operand, Place, PlaceElem, Rvalue};
use rustc_middle::ty::{self, TypeVisitableExt, adjustment::PointerCoercion};
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::rvalue::peel_adt_to_pointees;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Extracts the metadata word associated with a fat-pointer-producing rvalue.
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
                if let Some(mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(ptr, _))) = resolved
                    && is_fat_ptr(self.tcx, const_ty)
                {
                    let (prov, ptr_offset) = ptr.into_raw_parts();
                    let alloc = self.tcx.global_alloc(prov.alloc_id());
                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(mem_alloc) = alloc {
                        let inner = mem_alloc.inner();
                        let byte_offset = ptr_offset.bytes() as usize + 8;
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
                if let Some((_, meta)) = self.split_pair_field(place) {
                    return Some(meta);
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
            // Fat-pointer aggregates propagate metadata either from an
            // explicit metadata operand (raw pointer scalar-pair construction)
            // or from the one non-ZST field that carries the wrapped fat
            // pointer (e.g. NonNull/Unique/Box wrappers).
            Rvalue::Aggregate(box kind, operands)
                if !operands.is_empty() && !matches!(kind, mir::AggregateKind::Array(_)) =>
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
                    match kind {
                        mir::AggregateKind::RawPtr(..) => operands
                            .iter()
                            .nth(1)
                            .and_then(|op| self.translate_operand(op)),
                        mir::AggregateKind::Adt(def_id, _, args, _, _) => {
                            let adt_def = self.tcx.adt_def(*def_id);
                            let fat_field = adt_def
                                .non_enum_variant()
                                .fields
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, field)| {
                                    let field_ty = self.monomorphize(field.ty(self.tcx, args));
                                    let field_size = type_size(self.tcx, field_ty).unwrap_or(0);
                                    (field_size > 0).then_some((idx, field_ty, field_size))
                                })
                                .collect::<Vec<_>>();
                            let [(field_idx, _, _)] = fat_field.as_slice() else {
                                return None;
                            };
                            operands
                                .iter()
                                .nth(*field_idx)
                                .and_then(|op| self.find_fat_metadata_for_operand(op))
                        }
                        mir::AggregateKind::Tuple => {
                            let tuple_ty = agg_ty.unwrap();
                            let ty::Tuple(fields) = tuple_ty.kind() else {
                                return None;
                            };
                            let fat_field = fields
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, field_ty)| {
                                    let field_ty = self.monomorphize(field_ty);
                                    let field_size = type_size(self.tcx, field_ty).unwrap_or(0);
                                    (field_size > 0).then_some((idx, field_ty, field_size))
                                })
                                .collect::<Vec<_>>();
                            let [(field_idx, _, _)] = fat_field.as_slice() else {
                                return None;
                            };
                            operands
                                .iter()
                                .nth(*field_idx)
                                .and_then(|op| self.find_fat_metadata_for_operand(op))
                        }
                        _ => {
                            let first_op = operands.iter().next().unwrap();
                            self.find_fat_metadata_for_operand(first_op)
                        }
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract fat pointer metadata from a MIR operand.
    /// For place operands, delegates to `find_fat_metadata_for_place`.
    /// Returns `None` for non-fat operands and constants.
    pub(super) fn find_fat_metadata_for_operand(
        &mut self,
        operand: &Operand<'tcx>,
    ) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.find_fat_metadata_for_place(place),
            _ => None,
        }
    }

    /// Load the data pointer from a fat pointer operand.
    /// `translate_operand` returns the stack slot address for fat pointer
    /// stack locals; this helper loads the first 8 bytes (the data pointer)
    /// so that comparisons operate on values rather than addresses.
    pub(super) fn load_fat_data_for_operand(
        &mut self,
        operand: &Operand<'tcx>,
        raw: ValueRef,
    ) -> ValueRef {
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
        // `split_at_mut` results are cached as tuple locals whose MIR type is
        // the pair, not either fat-pointer field, so consult that cache before
        // asking whether the base local itself is a fat pointer.
        if let Some((_, meta)) = self.split_pair_field(place) {
            return Some(meta);
        }
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
}
