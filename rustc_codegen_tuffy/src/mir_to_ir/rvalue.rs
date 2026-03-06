use rustc_middle::mir::{self, BinOp, CastKind, Operand, Place, PlaceElem, Rvalue};
use rustc_middle::ty::{self, Instance, TypeVisitableExt};
use tuffy_ir::instruction::{FCmpOp, ICmpOp, Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, FloatType, FpRewriteFlags, Type};
use tuffy_ir::value::ValueRef;

use super::constant::*;
use super::ctx::TranslationCtx;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    pub(super) fn translate_place_to_addr(
        &mut self,
        place: &Place<'tcx>,
    ) -> Option<(ValueRef, ty::Ty<'tcx>)> {
        self.translate_place_to_addr_inner(place, false)
    }

    /// Like `translate_place_to_addr`, but when `persist_spill` is true,
    /// a register-to-stack spill is made permanent so that subsequent
    /// reads of the local see the mutated value.
    pub(super) fn translate_place_to_addr_inner(
        &mut self,
        place: &Place<'tcx>,
        persist_spill: bool,
    ) -> Option<(ValueRef, ty::Ty<'tcx>)> {
        let mut addr = self.locals.get(place.local)?;
        let mut cur_ty = self.monomorphize(self.mir.local_decls[place.local].ty);

        // If the base local is not stack-allocated and the first projection
        // needs an address (Field, Index, etc.), spill the scalar value to a
        // temporary stack slot so we can compute sub-field addresses.
        if !self.stack_locals.is_stack(place.local)
            && !place.projection.is_empty()
            && !matches!(place.projection[0], PlaceElem::Deref)
        {
            let size = type_size(self.tcx, cur_ty).unwrap_or(8) as u32;
            let slot = self.builder.stack_slot(size, Origin::synthetic());
            // For fat pointer locals (e.g. &[T] parameters), the value in
            // `addr` is just the data pointer (8 bytes) while the metadata
            // (length / vtable) lives in fat_locals.  Reconstruct the full
            // fat pointer in the stack slot instead of doing a wide store
            // that would dereference the data pointer.
            if let Some(fat_val) = self.fat_locals.get(place.local) {
                // Store data pointer into slot[0..8].
                self.current_mem = self.builder.store(
                    addr.into(),
                    slot.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                // Store fat component (length/vtable) into slot[8..16].
                let off8 = self.builder.iconst(8, Origin::synthetic());
                let hi_addr = self
                    .builder
                    .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                self.current_mem = self.builder.store(
                    fat_val.into(),
                    hi_addr.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            } else if matches!(self.builder.value_type(addr), Some(Type::Ptr(_)))
                && self.builder.is_memory_address(addr)
            {
                // addr is a pointer to the data (e.g. symbol_addr for a
                // const array, or ptradd derived from one).  Copy
                // word-by-word from the source address.
                // Non-address Ptr values (e.g. a NonNull<T> loaded from
                // a call result) fall through to the direct-store path
                // below so we don't accidentally dereference them.
                let num_words = (size as u64).div_ceil(8);
                for i in 0..num_words {
                    let byte_off = i * 8;
                    let chunk = std::cmp::min(8, size as u64 - byte_off) as u32;
                    let src = if byte_off == 0 {
                        addr
                    } else {
                        let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                        self.builder
                            .ptradd(addr.into(), off.into(), 0, Origin::synthetic())
                    };
                    let word = self.builder.load(
                        src.into(),
                        chunk,
                        Type::Int,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    let dst = if byte_off == 0 {
                        slot
                    } else {
                        let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                        self.builder
                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                    };
                    self.current_mem = self.builder.store(
                        word.into(),
                        dst.into(),
                        chunk,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                }
            } else {
                self.current_mem = self.builder.store(
                    addr.into(),
                    slot.into(),
                    size,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
            }
            addr = slot;
            if persist_spill {
                self.locals.set(place.local, slot);
                self.stack_locals.mark(place.local);
            }
        }

        let mut downcast_variant: Option<rustc_abi::VariantIdx> = None;
        for (proj_idx, elem) in place.projection.iter().enumerate() {
            match elem {
                PlaceElem::Deref => {
                    // For stack-allocated locals holding a pointer value,
                    // load the pointer from the stack slot first.
                    if proj_idx == 0
                        && self.stack_locals.is_stack(place.local)
                        && matches!(self.builder.value_type(addr), Some(Type::Ptr(_)))
                    {
                        let loaded = self.builder.load(
                            addr.into(),
                            8,
                            Type::Ptr(0),
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        addr = loaded;
                    }
                    // The current value is a pointer; it IS the pointee address.
                    // Coerce Int→Ptr if the value was stored as an integer.
                    addr = self.coerce_to_ptr(addr);
                    // Update cur_ty to the pointee type.
                    cur_ty = match cur_ty.kind() {
                        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => *inner,
                        _ => return None,
                    };
                }
                PlaceElem::Field(field_idx, field_ty) => {
                    let offset = if let Some(variant_idx) = downcast_variant.take() {
                        variant_field_offset(self.tcx, cur_ty, variant_idx, field_idx.as_usize())?
                    } else {
                        field_offset(self.tcx, cur_ty, field_idx.as_usize())?
                    };
                    if offset != 0 {
                        let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                        addr = self.builder.ptradd(
                            addr.into(),
                            off_val.into(),
                            0,
                            Origin::synthetic(),
                        );
                    }
                    cur_ty = self.monomorphize(field_ty);
                }
                PlaceElem::Index(local) => {
                    let mut idx_val = self.locals.get(local)?;
                    // If the index local is stored in a stack slot, load
                    // the integer value — the raw slot is a Ptr, not Int.
                    if self.stack_locals.is_stack(local)
                        && matches!(self.builder.value_type(idx_val), Some(Type::Ptr(_)))
                    {
                        let loaded = self.builder.load(
                            idx_val.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            None,
                            Origin::synthetic(),
                        );
                        idx_val = loaded;
                    }
                    let elem_size = type_size(
                        self.tcx,
                        match cur_ty.kind() {
                            ty::Array(elem_ty, _) => *elem_ty,
                            ty::Slice(elem_ty) => *elem_ty,
                            _ => return None,
                        },
                    )?;
                    let size_val = self.builder.iconst(elem_size as i64, Origin::synthetic());
                    let byte_offset = self.builder.mul(
                        idx_val.into(),
                        size_val.into(),
                        None,
                        Origin::synthetic(),
                    );
                    addr = self.builder.ptradd(
                        addr.into(),
                        byte_offset.into(),
                        0,
                        Origin::synthetic(),
                    );
                    cur_ty = match cur_ty.kind() {
                        ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                        _ => return None,
                    };
                }
                PlaceElem::Downcast(_, variant_idx) => {
                    // Downcast doesn't change the address, only the type interpretation.
                    // Record the variant so the next Field projection uses
                    // variant-specific field offsets.
                    downcast_variant = Some(variant_idx);
                }
                PlaceElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let elem_ty = match cur_ty.kind() {
                        ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                        _ => return None,
                    };
                    let elem_size = type_size(self.tcx, elem_ty)?;
                    if !from_end {
                        let byte_off = offset * elem_size;
                        if byte_off != 0 {
                            let off_val = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            addr = self.builder.ptradd(
                                addr.into(),
                                off_val.into(),
                                0,
                                Origin::synthetic(),
                            );
                        }
                    }
                    // from_end case would need array length; skip for now.
                    cur_ty = elem_ty;
                }
                PlaceElem::Subslice { from, to, from_end } => {
                    let elem_ty = match cur_ty.kind() {
                        ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                        _ => return None,
                    };
                    let elem_size = type_size(self.tcx, elem_ty)?;
                    if from > 0 {
                        let off = self
                            .builder
                            .iconst((from * elem_size) as i64, Origin::synthetic());
                        addr = self
                            .builder
                            .ptradd(addr.into(), off.into(), 0, Origin::synthetic());
                    }
                    cur_ty = if from_end {
                        // Array: [T; N] -> [T; N - from - to]
                        let n = match cur_ty.kind() {
                            ty::Array(_, n) => n.try_to_target_usize(self.tcx).unwrap_or(0),
                            _ => return None,
                        };
                        ty::Ty::new_array(self.tcx, elem_ty, n - from - to)
                    } else {
                        // Slice: result is still a slice
                        cur_ty
                    };
                }
                _ => {
                    unimplemented!("MIR place projection: {:?}", elem);
                }
            }
        }
        Some((addr, cur_ty))
    }

    /// Read the value at a Place (base + projections).
    ///
    /// If the place has no projections, returns the local's value directly.
    pub(super) fn translate_place_to_value(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        if place.projection.is_empty() {
            return self.locals.get(place.local);
        }
        // Non-stack scalar with Field projection for CheckedOp tuples only:
        // AddWithOverflow/SubWithOverflow/MulWithOverflow return (result, bool) but
        // we only emit the arithmetic result as a scalar.  Field(0) returns that
        // scalar directly; Field(1) (the overflow flag) returns constant 0 (false),
        // effectively disabling overflow detection (matches release-mode behaviour).
        //
        // Only apply this shortcut when the local is a (T, bool) tuple — other
        // tuples (e.g. (Flags, Flags) in FnMut shims) must fall through to the
        // spill-to-stack path so field offsets are computed correctly.
        if !self.stack_locals.is_stack(place.local)
            && place.projection.len() == 1
            && matches!(place.projection[0], PlaceElem::Field(idx, _) if idx.as_usize() <= 1)
        {
            let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
            let is_checked_op = matches!(local_ty.kind(), ty::Tuple(fields)
                if fields.len() == 2 && fields[1].is_bool()
                   && !fields[0].is_bool());
            if is_checked_op && let PlaceElem::Field(idx, _) = place.projection[0] {
                if idx.as_usize() == 0 {
                    return self.locals.get(place.local);
                } else {
                    // Overflow flag — from the secondary result of the WithOverflow IR op.
                    if let Some(overflow) = self.overflow_locals.get(place.local) {
                        return Some(overflow);
                    }
                    // Fallback: always false (no overflow).
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }
            }
        }
        let (addr, projected_ty) = self.translate_place_to_addr(place)?;
        let addr = self.coerce_to_ptr(addr);
        let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
        // ZST: no data to load — return a dummy value.
        if bytes == 0 {
            return Some(self.builder.iconst(0, Origin::synthetic()));
        }
        // For fat pointer types (e.g. &mut dyn Write, &[T]), load the
        // first word (data pointer) so that locals[dest] holds the data
        // pointer value.  The second word (vtable/length) is handled
        // separately by the fat component extraction in translate_rvalue.
        if bytes > 8 && is_fat_ptr(self.tcx, projected_ty) {
            let data = self.builder.load(
                addr.into(),
                8,
                Type::Ptr(0),
                self.current_mem.into(),
                None,
                Origin::synthetic(),
            );
            return Some(data);
        }
        // For other types > 8 bytes, return the address directly so the
        // caller (assignment handler) can do word-by-word copy.
        if bytes > 8 {
            return Some(addr);
        }
        let ty = translate_ty(self.tcx, projected_ty).unwrap_or(Type::Int);
        let data = self.builder.load(
            addr.into(),
            bytes,
            ty,
            self.current_mem.into(),
            None,
            Origin::synthetic(),
        );
        Some(data)
    }

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
            rustc_abi::Variants::Empty => Some(self.builder.iconst(0, Origin::synthetic())),
            rustc_abi::Variants::Single { index } => {
                let discr_val = match place_ty.kind() {
                    ty::Adt(adt_def, _) if adt_def.is_enum() => {
                        adt_def.discriminant_for_variant(self.tcx, index).val as i64
                    }
                    _ => index.as_u32() as i64,
                };
                Some(self.builder.iconst(discr_val, Origin::synthetic()))
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
                        let slot = self.builder.stack_slot(size, Origin::synthetic());
                        self.current_mem = self.builder.store(
                            val.into(),
                            slot.into(),
                            size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
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
                    let off = self.builder.iconst(tag_offset as i64, Origin::synthetic());
                    self.builder
                        .ptradd(base_addr.into(), off.into(), 0, Origin::synthetic())
                } else {
                    base_addr
                };
                let tag_val = self.builder.load(
                    tag_addr.into(),
                    tag_size,
                    Type::Int,
                    self.current_mem.into(),
                    None,
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
                            let zero = self.builder.iconst(0, Origin::synthetic());
                            let is_niche = self.builder.icmp(
                                ICmpOp::Eq,
                                tag_val.into(),
                                zero.into(),
                                Origin::synthetic(),
                            );
                            let niche_discr = self
                                .builder
                                .iconst(variants_start as i64, Origin::synthetic());
                            let untag_discr =
                                self.builder.iconst(untagged_discr, Origin::synthetic());
                            Some(self.builder.select(
                                is_niche.into(),
                                niche_discr.into(),
                                untag_discr.into(),
                                Type::Int,
                                Origin::synthetic(),
                            ))
                        } else {
                            // General niche: i = tag.wrapping_sub(niche_start) + start
                            let ns = self
                                .builder
                                .iconst(*niche_start as i64, Origin::synthetic());
                            let relative = self.builder.sub(
                                tag_val.into(),
                                ns.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let start_c = self
                                .builder
                                .iconst(variants_start as i64, Origin::synthetic());
                            let variant_idx = self.builder.add(
                                relative.into(),
                                start_c.into(),
                                None,
                                Origin::synthetic(),
                            );
                            // Check relative < num_niche (unsigned).
                            let num_c = self.builder.iconst(num_niche as i64, Origin::synthetic());
                            let in_range = self.builder.icmp(
                                ICmpOp::Lt,
                                relative.into(),
                                num_c.into(),
                                Origin::synthetic(),
                            );
                            let untag_discr =
                                self.builder.iconst(untagged_discr, Origin::synthetic());
                            Some(self.builder.select(
                                in_range.into(),
                                variant_idx.into(),
                                untag_discr.into(),
                                Type::Int,
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
                    return Some(self.builder.iconst(meta as i64, Origin::synthetic()));
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
                        return Some(self.builder.iconst(len as i64, Origin::synthetic()));
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
                if place.projection.is_empty()
                    && let Some(fat) = self.fat_locals.get(place.local)
                {
                    return Some(fat);
                }
                // Check if the place resolves to a fat pointer type via projections.
                if !place.projection.is_empty() {
                    let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                    let projected_ty = self.monomorphize(projected_ty);
                    if is_fat_ptr(self.tcx, projected_ty)
                        && let Some((addr, _)) = self.translate_place_to_addr(place)
                    {
                        let off8 = self.builder.iconst(8, Origin::synthetic());
                        let meta_addr =
                            self.builder
                                .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                        let meta = self.builder.load(
                            meta_addr.into(),
                            8,
                            Type::Int,
                            self.current_mem.into(),
                            None,
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
                if is_fat_ptr(self.tcx, target_ty_mono)
                    && let Operand::Copy(place) | Operand::Move(place) = op
                    && let Some(fat) = self.fat_locals.get(place.local)
                {
                    return Some(fat);
                }
                // For Unsize coercions to trait objects, generate the vtable pointer.
                if let CastKind::PointerCoercion(pc, _) = cast_kind {
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
                        // This is an unsizing coercion to a trait object.
                        // Get the concrete source type.
                        let src_ty = match op {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(self.mir.local_decls[p.local].ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return None,
                        };
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
                        let vtable_alloc = self.tcx.global_alloc(vtable_alloc_id);
                        if let rustc_middle::mir::interpret::GlobalAlloc::Memory(alloc) =
                            vtable_alloc
                        {
                            let inner_alloc = alloc.inner();
                            let size = inner_alloc.len();
                            let bytes = inner_alloc
                                .inspect_with_uninit_and_ptr_outside_interpreter(0..size)
                                .to_vec();
                            let sym = format!(".Lvtable.{}", self.next_data_id());
                            let sym_id = self.symbols.intern(&sym);
                            let relocs = extract_alloc_relocs(
                                self.tcx,
                                inner_alloc,
                                0,
                                size,
                                &mut self.symbols,
                                &mut self.static_data,
                                &mut self.referenced_instances,
                                self.data_counter,
                            );
                            self.static_data.push((sym_id, bytes, relocs));
                            return Some(self.builder.symbol_addr(sym_id, Origin::synthetic()));
                        }
                    }
                    // Handle array-to-slice unsizing: &[T; N] → &[T].
                    // The fat component is the array length N.
                    if let Some(inner) = target_inner
                        && let ty::Slice(_) = inner.kind()
                    {
                        let src_ty = match op {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(self.mir.local_decls[p.local].ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return None,
                        };
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ if src_ty.is_box() => src_ty.boxed_ty().unwrap(),
                            _ => src_ty,
                        };
                        if let ty::Array(_, len) = src_inner.kind()
                            && let Some(n) = len.try_to_target_usize(self.tcx)
                        {
                            return Some(self.builder.iconst(n as i64, Origin::synthetic()));
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
                        let src_ty = match op {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(self.mir.local_decls[p.local].ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return None,
                        };
                        let src_inner = match src_ty.kind() {
                            ty::Ref(_, inner, _) => *inner,
                            ty::RawPtr(inner, _) => *inner,
                            _ if src_ty.is_box() => src_ty.boxed_ty().unwrap(),
                            _ => src_ty,
                        };
                        let (src_tail, dst_tail) = self
                            .tcx
                            .struct_lockstep_tails_for_codegen(src_inner, inner, typing_env);
                        match dst_tail.kind() {
                            ty::Slice(_) => {
                                if let ty::Array(_, len) = src_tail.kind()
                                    && let Some(n) = len.try_to_target_usize(self.tcx)
                                {
                                    return Some(
                                        self.builder.iconst(n as i64, Origin::synthetic()),
                                    );
                                }
                            }
                            ty::Dynamic(predicates, _) => {
                                if !src_tail.has_escaping_bound_vars() && !src_tail.is_trait() {
                                    let principal = predicates
                                        .principal()
                                        .map(|p| self.tcx.instantiate_bound_regions_with_erased(p));
                                    let vtable_alloc_id =
                                        self.tcx.vtable_allocation((src_tail, principal));
                                    let vtable_alloc = self.tcx.global_alloc(vtable_alloc_id);
                                    if let rustc_middle::mir::interpret::GlobalAlloc::Memory(
                                        alloc,
                                    ) = vtable_alloc
                                    {
                                        let inner_alloc = alloc.inner();
                                        let size = inner_alloc.len();
                                        let bytes = inner_alloc
                                            .inspect_with_uninit_and_ptr_outside_interpreter(
                                                0..size,
                                            )
                                            .to_vec();
                                        let sym = format!(".Lvtable.{}", self.next_data_id());
                                        let sym_id = self.symbols.intern(&sym);
                                        let relocs = extract_alloc_relocs(
                                            self.tcx,
                                            inner_alloc,
                                            0,
                                            size,
                                            &mut self.symbols,
                                            &mut self.static_data,
                                            &mut self.referenced_instances,
                                            self.data_counter,
                                        );
                                        self.static_data.push((sym_id, bytes, relocs));
                                        return Some(
                                            self.builder.symbol_addr(sym_id, Origin::synthetic()),
                                        );
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    let _ = pc; // suppress unused warning
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
                    self.fat_locals
                        .get(place.local)
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
                    let mir_ty = match lhs {
                        Operand::Copy(p) | Operand::Move(p) => {
                            self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                        }
                        Operand::Constant(c) => self.monomorphize(c.ty()),
                        _ => self.tcx.types.i32,
                    };
                    match mir_ty.kind() {
                        ty::Float(ty::FloatTy::F16) => Some(Type::Float(FloatType::F16)),
                        ty::Float(ty::FloatTy::F32) => Some(Type::Float(FloatType::F32)),
                        ty::Float(ty::FloatTy::F64) => Some(Type::Float(FloatType::F64)),
                        _ => None,
                    }
                };

                // Float arithmetic: dispatch directly to fadd/fsub/fmul/fdiv.
                // Operands are always Float-typed at this point.
                // Floats have no "unchecked" variants — only the plain ops.
                if let Some(ref fty) = float_ty {
                    if matches!(
                        op,
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
                    ) {
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
                        return Some(res);
                    }
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
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }

                // Detect 128-bit integer operands early so we can load from
                // stack slot pointers before coercing to int.
                let lhs_mir_ty = match lhs {
                    Operand::Copy(p) | Operand::Move(p) => {
                        self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                    }
                    Operand::Constant(c) => self.monomorphize(c.ty()),
                    _ => self.tcx.types.i32,
                };
                let rhs_mir_ty = match rhs {
                    Operand::Copy(p) | Operand::Move(p) => {
                        self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                    }
                    Operand::Constant(c) => self.monomorphize(c.ty()),
                    _ => self.tcx.types.i32,
                };

                // Recompute annotations from the fully-resolved MIR types.
                // `operand_annotation` uses the local's type which misses
                // projections (e.g. `RET.fld1` where RET is a struct but
                // fld1 is i128).  The MIR types computed above resolve
                // through projections correctly.
                let l_ann = translate_annotation(lhs_mir_ty).or(l_ann);
                let r_ann = translate_annotation(rhs_mir_ty).or(r_ann);

                // For large integral types (>8 bytes, e.g. u128/i128),
                // translate_place_to_value returns a Ptr to the stack slot.
                // Load the integer value before coercing.
                let l_raw = if matches!(self.builder.value_type(l_raw), Some(Type::Ptr(_)))
                    && lhs_mir_ty.is_integral()
                    && let Some(lhs_size) = type_size(self.tcx, lhs_mir_ty)
                    && lhs_size > 8
                {
                    self.builder.load(
                        l_raw.into(),
                        lhs_size as u32,
                        Type::Int,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    )
                } else {
                    l_raw
                };
                let r_raw = if matches!(self.builder.value_type(r_raw), Some(Type::Ptr(_)))
                    && rhs_mir_ty.is_integral()
                    && let Some(rhs_size) = type_size(self.tcx, rhs_mir_ty)
                    && rhs_size > 8
                {
                    self.builder.load(
                        r_raw.into(),
                        rhs_size as u32,
                        Type::Int,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    )
                } else {
                    r_raw
                };

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
                let res_ann = l_ann;

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
                    // Wrapping integer arithmetic: result annotation is DontCare(N),
                    // then Sext (signed types) or Zext (unsigned types) to interpret
                    // the low N bits correctly.  Without the extension, upper bits from
                    // a 64-bit ADD can bleed through for sub-64-bit types.
                    BinOp::Add => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let dont_care = res_ann.map(|_| Annotation::DontCare(bits));
                        let sum = self.builder.add(l_op, r_op, dont_care, Origin::synthetic());
                        match res_ann {
                            Some(Annotation::Signed(_)) => self.builder.sext(
                                IrOperand::annotated(sum, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            Some(Annotation::Unsigned(_)) => self.builder.zext(
                                IrOperand::annotated(sum, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            _ => sum,
                        }
                    }
                    BinOp::Sub => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let dont_care = res_ann.map(|_| Annotation::DontCare(bits));
                        let diff = self.builder.sub(l_op, r_op, dont_care, Origin::synthetic());
                        match res_ann {
                            Some(Annotation::Signed(_)) => self.builder.sext(
                                IrOperand::annotated(diff, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            Some(Annotation::Unsigned(_)) => self.builder.zext(
                                IrOperand::annotated(diff, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            _ => diff,
                        }
                    }
                    BinOp::Mul => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let dont_care = res_ann.map(|_| Annotation::DontCare(bits));
                        let prod = self.builder.mul(l_op, r_op, dont_care, Origin::synthetic());
                        match res_ann {
                            Some(Annotation::Signed(_)) => self.builder.sext(
                                IrOperand::annotated(prod, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            Some(Annotation::Unsigned(_)) => self.builder.zext(
                                IrOperand::annotated(prod, Annotation::DontCare(bits)),
                                bits,
                                Origin::synthetic(),
                            ),
                            _ => prod,
                        }
                    }
                    // Unchecked variants: the caller guarantees no overflow so the
                    // result can carry a full Signed/Unsigned annotation directly.
                    BinOp::AddUnchecked => {
                        self.builder.add(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::SubUnchecked => {
                        self.builder.sub(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    BinOp::MulUnchecked => {
                        self.builder.mul(l_op, r_op, res_ann, Origin::synthetic())
                    }
                    // Checked arithmetic: emit a multi-result IR intrinsic that
                    // produces (wrapping_result: Int, overflow: Bool).  The primary
                    // result is returned here and stored in `locals`; the secondary
                    // overflow flag is saved in `overflow_locals` for Field(1) access.
                    BinOp::AddWithOverflow => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(Annotation::Signed(_)))
                        {
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
                        self.overflow_locals.set(dest_place.local, overflow);
                        primary
                    }
                    BinOp::SubWithOverflow => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(Annotation::Signed(_)))
                        {
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
                        self.overflow_locals.set(dest_place.local, overflow);
                        primary
                    }
                    BinOp::MulWithOverflow => {
                        let bits = match res_ann {
                            Some(
                                Annotation::Signed(n)
                                | Annotation::Unsigned(n)
                                | Annotation::DontCare(n),
                            ) => n,
                            None => 64,
                        };
                        let (primary, overflow) = if matches!(res_ann, Some(Annotation::Signed(_)))
                        {
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
                        self.overflow_locals.set(dest_place.local, overflow);
                        primary
                    }
                    BinOp::Eq => {
                        if is_float_cmp {
                            let cmp = self.builder.fcmp(
                                FCmpOp::OEq,
                                l_raw.into(),
                                r_raw.into(),
                                Origin::synthetic(),
                            );
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                        } else {
                            let cmp =
                                self.builder
                                    .icmp(ICmpOp::Eq, l_op, r_op, Origin::synthetic());
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                        }
                    }
                    BinOp::Ne => {
                        if is_float_cmp {
                            let cmp = self.builder.fcmp(
                                FCmpOp::UNe,
                                l_raw.into(),
                                r_raw.into(),
                                Origin::synthetic(),
                            );
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                        } else {
                            let cmp =
                                self.builder
                                    .icmp(ICmpOp::Ne, l_op, r_op, Origin::synthetic());
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
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
                            let cmp = self.builder.fcmp(
                                fcmp_op,
                                l_raw.into(),
                                r_raw.into(),
                                Origin::synthetic(),
                            );
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
                        } else {
                            let icmp_op = match op {
                                BinOp::Lt => ICmpOp::Lt,
                                BinOp::Le => ICmpOp::Le,
                                BinOp::Gt => ICmpOp::Gt,
                                _ => ICmpOp::Ge,
                            };
                            let cmp = self.builder.icmp(icmp_op, l_op, r_op, Origin::synthetic());
                            self.builder.bool_to_int(cmp.into(), Origin::synthetic())
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
                            let lt_int = self.builder.bool_to_int(lt.into(), Origin::synthetic());
                            let gt = self.builder.fcmp(
                                FCmpOp::OGt,
                                l_f.into(),
                                r_f.into(),
                                Origin::synthetic(),
                            );
                            let gt_int = self.builder.bool_to_int(gt.into(), Origin::synthetic());
                            self.builder.sub(
                                gt_int.into(),
                                lt_int.into(),
                                res_ann,
                                Origin::synthetic(),
                            )
                        } else {
                            let lt = self.builder.icmp(
                                ICmpOp::Lt,
                                l_op.clone(),
                                r_op.clone(),
                                Origin::synthetic(),
                            );
                            let lt_int = self.builder.bool_to_int(lt.into(), Origin::synthetic());
                            let gt = self
                                .builder
                                .icmp(ICmpOp::Gt, l_op, r_op, Origin::synthetic());
                            let gt_int = self.builder.bool_to_int(gt.into(), Origin::synthetic());
                            self.builder.sub(
                                gt_int.into(),
                                lt_int.into(),
                                res_ann,
                                Origin::synthetic(),
                            )
                        }
                    }
                    BinOp::Shl | BinOp::ShlUnchecked => {
                        let shift_val = r_op.value;
                        // Rust masks shift amounts to % bit_width.
                        let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                        let mask_val = self.builder.iconst(lhs_bits - 1, Origin::synthetic());
                        let masked = self.builder.and(
                            shift_val.into(),
                            mask_val.into(),
                            None,
                            Origin::synthetic(),
                        );
                        let masked_op = IrOperand {
                            value: masked,
                            annotation: None,
                        };
                        self.builder
                            .shl(l_op, masked_op, res_ann, Origin::synthetic())
                    }
                    BinOp::BitOr => self.builder.or(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::BitAnd => self.builder.and(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::BitXor => self.builder.xor(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::Shr | BinOp::ShrUnchecked => {
                        let shift_val = r_op.value;
                        let lhs_bits = type_size(self.tcx, lhs_mir_ty).unwrap_or(8) as i64 * 8;
                        let mask_val = self.builder.iconst(lhs_bits - 1, Origin::synthetic());
                        let masked = self.builder.and(
                            shift_val.into(),
                            mask_val.into(),
                            None,
                            Origin::synthetic(),
                        );
                        let masked_op = IrOperand {
                            value: masked,
                            annotation: None,
                        };
                        self.builder
                            .shr(l_op, masked_op, res_ann, Origin::synthetic())
                    }
                    BinOp::Div => self.builder.div(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::Rem => self.builder.rem(l_op, r_op, res_ann, Origin::synthetic()),
                    BinOp::Offset => {
                        // ptr.wrapping_offset(count) = ptr + count * sizeof(T).
                        let pointee_ty = match lhs {
                            Operand::Copy(p) | Operand::Move(p) => {
                                let ty =
                                    self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty);
                                match ty.kind() {
                                    ty::RawPtr(inner, _) => Some(*inner),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        let elem_size =
                            pointee_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(1);
                        if elem_size == 1 {
                            self.builder.add(l_op, r_op, res_ann, Origin::synthetic())
                        } else {
                            let size_val =
                                self.builder.iconst(elem_size as i64, Origin::synthetic());
                            let size_op = IrOperand {
                                value: size_val,
                                annotation: None,
                            };
                            let byte_off =
                                self.builder.mul(r_op, size_op, None, Origin::synthetic());
                            let byte_off_op = IrOperand {
                                value: byte_off,
                                annotation: None,
                            };
                            self.builder
                                .add(l_op, byte_off_op, res_ann, Origin::synthetic())
                        }
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
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => {
                                p.ty(&self.mir.local_decls, self.tcx).ty
                            }
                            Operand::Constant(c) => c.ty(),
                            _ => return Some(val),
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
                        let val = if type_size(self.tcx, src_ty).is_some_and(|s| s > 8)
                            && src_ty.is_integral()
                            && type_size(self.tcx, target_ty_m).is_some_and(|s| s <= 8)
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
                                None,
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
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => self.mir.local_decls[p.local].ty,
                            Operand::Constant(c) => c.ty(),
                            _ => return Some(val),
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
                            Some(self.builder.symbol_addr(sym_id, Origin::synthetic()))
                        } else {
                            Some(val)
                        }
                    }
                    CastKind::FloatToInt => {
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return Some(val),
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
                            self.builder
                                .bitcast(val.into(), Type::Int, None, Origin::synthetic())
                        } else {
                            val
                        };
                        // For 128-bit targets, fp_to_ui/fp_to_si only produce 64-bit results.
                        // Convert to 64-bit first, then extend.
                        let needs_extend = bit_width > 64;
                        let raw = if signed {
                            self.builder.fp_to_si(float_val.into(), Origin::synthetic())
                        } else {
                            self.builder.fp_to_ui(float_val.into(), Origin::synthetic())
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
                        let two63_int = self.builder.iconst(two63_bits, Origin::synthetic());
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
                                self.builder.sext(raw.into(), 128, Origin::synthetic())
                            } else {
                                self.builder.zext(raw.into(), 128, Origin::synthetic())
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
                            let zero = self.builder.iconst(0, Origin::synthetic());
                            let i64_max = self.builder.iconst(i64::MAX, Origin::synthetic());
                            // Apply corrections: NaN → 0, then positive overflow → i64::MAX
                            let corrected = self.builder.select(
                                is_nan.into(),
                                zero.into(),
                                raw.into(),
                                Type::Int,
                                Origin::synthetic(),
                            );
                            let corrected = self.builder.select(
                                is_large.into(),
                                i64_max.into(),
                                corrected.into(),
                                Type::Int,
                                Origin::synthetic(),
                            );
                            if bit_width < 64 {
                                // Clamp to [INT_MIN_of_width, INT_MAX_of_width].
                                // After corrections, corrected ∈ {0, i64::MAX, or cvttss2si result
                                // which is in [-2^63, 2^63-1]}.  Signed min/max works correctly.
                                let lo = -(1i64 << (bit_width - 1));
                                let hi = (1i64 << (bit_width - 1)) - 1;
                                let lo_c = self.builder.iconst(lo, Origin::synthetic());
                                let hi_c = self.builder.iconst(hi, Origin::synthetic());
                                let ann_s = Some(Annotation::Signed(64));
                                let clamped_hi = self.builder.min(
                                    corrected.into(),
                                    hi_c.into(),
                                    ann_s,
                                    Origin::synthetic(),
                                );
                                self.builder.max(
                                    clamped_hi.into(),
                                    lo_c.into(),
                                    ann_s,
                                    Origin::synthetic(),
                                )
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
                            let zero = self.builder.iconst(0, Origin::synthetic());
                            if bit_width < 64 {
                                // For u32/u16/u8: float >= 2^63 is always an overflow (> UINT_MAX).
                                // cvttss2si is correct for float in [-2^63, 2^63): negative → negative
                                // i64, clamped to 0; in-range → correct; overflow beyond hi → large
                                // positive i64, clamped to hi.
                                let hi = (1i64 << bit_width) - 1;
                                let hi_c = self.builder.iconst(hi, Origin::synthetic());
                                let ann_s = Some(Annotation::Signed(64));
                                let clamped = self.builder.min(
                                    raw.into(),
                                    hi_c.into(),
                                    ann_s,
                                    Origin::synthetic(),
                                );
                                let clamped = self.builder.max(
                                    clamped.into(),
                                    zero.into(),
                                    ann_s,
                                    Origin::synthetic(),
                                );
                                // Override: float >= 2^63 → hi (overflow), NaN → 0.
                                let clamped = self.builder.select(
                                    is_large.into(),
                                    hi_c.into(),
                                    clamped.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                );
                                self.builder.select(
                                    is_nan.into(),
                                    zero.into(),
                                    clamped.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                )
                            } else {
                                // u64: two-range implementation.
                                // [0, 2^63):   cvttss2si gives correct result.
                                // [2^63, 2^64): subtract 2^63, convert, add 2^63 via bitwise OR.
                                // >= 2^64:      saturate to UINT64_MAX.
                                let two64_int =
                                    self.builder.iconst(two64_bits, Origin::synthetic());
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
                                let raw_shifted = self
                                    .builder
                                    .fp_to_ui(float_shifted.into(), Origin::synthetic());
                                let sign_bit = self.builder.iconst(i64::MIN, Origin::synthetic());
                                let result_large = self.builder.or(
                                    raw_shifted.into(),
                                    sign_bit.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                let max_u64 = self.builder.iconst(-1_i64, Origin::synthetic());
                                // Select in order: normal → large → huge → nan_or_neg
                                let tentative = self.builder.select(
                                    is_large.into(),
                                    result_large.into(),
                                    raw.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                );
                                let tentative = self.builder.select(
                                    is_huge.into(),
                                    max_u64.into(),
                                    tentative.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                );
                                // NaN or negative → 0 (NaN check must come after is_huge
                                // so that positive NaN doesn't get UINT64_MAX).
                                let sign_bit_pos: u32 = match ft {
                                    FloatType::F32 => 31,
                                    _ => 63,
                                };
                                let shift_c = self
                                    .builder
                                    .iconst(sign_bit_pos as i64, Origin::synthetic());
                                let sign = self.builder.shr(
                                    int_bits_val.into(),
                                    shift_c.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                let one = self.builder.iconst(1, Origin::synthetic());
                                let sign_masked = self.builder.and(
                                    sign.into(),
                                    one.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                let is_neg = self
                                    .builder
                                    .int_to_bool(sign_masked.into(), Origin::synthetic());
                                let tentative = self.builder.select(
                                    is_neg.into(),
                                    zero.into(),
                                    tentative.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                );
                                self.builder.select(
                                    is_nan.into(),
                                    zero.into(),
                                    tentative.into(),
                                    Type::Int,
                                    Origin::synthetic(),
                                )
                            }
                        };
                        Some(result)
                    }
                    CastKind::IntToFloat => {
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return Some(val),
                        };
                        let signed = matches!(src_ty.kind(), ty::Int(_));
                        let target_ty_m = self.monomorphize(*target_ty);
                        let ft = match target_ty_m.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(val),
                        };
                        let int_val = self.coerce_to_int(val);

                        // Set annotation so the isel can sign/zero-extend narrow
                        // integers before cvtsi2ss/cvtsi2sd.  The x86 instruction
                        // operates on a full 64-bit value; without sign-extension
                        // a byte like 0xDA (-38 as i8) would be seen as 218.
                        let annotation = if let Some(size) = type_size(self.tcx, src_ty) {
                            let bits = (size * 8) as u32;
                            Some(if signed {
                                tuffy_ir::types::Annotation::Signed(bits)
                            } else {
                                tuffy_ir::types::Annotation::Unsigned(bits)
                            })
                        } else {
                            None
                        };

                        let operand = if let Some(ann) = annotation {
                            tuffy_ir::instruction::Operand::annotated(int_val, ann)
                        } else {
                            int_val.into()
                        };
                        let float_res = if signed {
                            self.builder.si_to_fp(operand, ft, Origin::synthetic())
                        } else {
                            self.builder.ui_to_fp(operand, ft, Origin::synthetic())
                        };
                        Some(float_res)
                    }
                    CastKind::FloatToFloat => {
                        let src_ty = match operand {
                            Operand::Copy(p) | Operand::Move(p) => {
                                self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty)
                            }
                            Operand::Constant(c) => self.monomorphize(c.ty()),
                            _ => return Some(val),
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
                        Some(converted)
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
                                    let data = self.builder.load(
                                        val.into(),
                                        target_size as u32,
                                        ir_ty,
                                        self.current_mem.into(),
                                        None,
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
                        {
                            if let Operand::Copy(src) | Operand::Move(src) = operand {
                                if src.projection.is_empty()
                                    && self.stack_locals.is_stack(src.local)
                                {
                                    let target_size =
                                        type_size(self.tcx, target_ty_mono).unwrap_or(0);
                                    let target_ir_ty = translate_ty(self.tcx, target_ty_mono);
                                    if target_size > 0
                                        && matches!(
                                            target_ir_ty,
                                            Some(Type::Int | Type::Float(_))
                                        )
                                    {
                                        let load_ty = target_ir_ty.unwrap();
                                        let loaded = self.builder.load(
                                            val.into(),
                                            target_size as u32,
                                            load_ty,
                                            self.current_mem.into(),
                                            None,
                                            Origin::synthetic(),
                                        );
                                        return Some(loaded);
                                    }
                                }
                            }
                        }
                        // Transmute from an Int register value to a Float type: reinterpret
                        // the bit pattern via a temporary stack slot (no bitcast in IR).
                        if matches!(kind, CastKind::Transmute)
                            && matches!(
                                self.builder.value_type(val),
                                Some(Type::Int | Type::Bool)
                            )
                        {
                            if let Some(Type::Float(ft)) =
                                translate_ty(self.tcx, target_ty_mono)
                            {
                                let size =
                                    type_size(self.tcx, target_ty_mono).unwrap_or(0) as u32;
                                if size > 0 && size <= 8 {
                                    let slot =
                                        self.builder.stack_slot(size, Origin::synthetic());
                                    self.current_mem = self.builder.store(
                                        val.into(),
                                        slot.into(),
                                        size,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
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
                        }
                        // Transmute / PtrToPtr from a pointer-typed source
                        // to a non-pointer target
                        if matches!(self.builder.value_type(val), Some(Type::Ptr(_)))
                            && !matches!(
                                target_ty_mono.kind(),
                                ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..)
                            )
                        {
                            let src_ty = match operand {
                                Operand::Copy(p) | Operand::Move(p) => Some(
                                    self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty),
                                ),
                                Operand::Constant(c) => Some(self.monomorphize(c.ty())),
                                _ => None,
                            };
                            if let Some(st) = src_ty {
                                if matches!(st.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                                {
                                    return Some(
                                        self.builder.ptrtoaddr(val.into(), Origin::synthetic()),
                                    );
                                }
                            }
                        }
                        Some(val)
                    }
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if !place.projection.is_empty() {
                    self.translate_place_to_addr(place).map(|(addr, _ty)| addr)
                } else if self.stack_locals.is_stack(place.local) {
                    self.locals.get(place.local)
                } else {
                    if let Some(val) = self.locals.get(place.local) {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, local_ty).unwrap_or(8) as u32;
                        let slot = self.builder.stack_slot(size.max(8), Origin::synthetic());
                        self.current_mem = self.builder.store(
                            val.into(),
                            slot.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        if let Some(meta) = self.fat_locals.get(place.local) {
                            let off8 = self.builder.iconst(8, Origin::synthetic());
                            let meta_addr = self.builder.ptradd(
                                slot.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            self.current_mem = self.builder.store(
                                meta.into(),
                                meta_addr.into(),
                                8,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
                        }
                        self.locals.set(place.local, slot);
                        self.stack_locals.mark(place.local);
                        Some(slot)
                    } else {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, local_ty).unwrap_or(1) as u32;
                        let slot = self.builder.stack_slot(size.max(1), Origin::synthetic());
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

                // For non-enum aggregates with no operands, return zero.
                if operands.is_empty() && enum_variant_idx.is_none() {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }

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
                    return Some(self.builder.iconst(0, Origin::synthetic()));
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
                                .stack_slot(total_size as u32, Origin::synthetic())
                        }
                    } else {
                        self.builder
                            .stack_slot(total_size as u32, Origin::synthetic())
                    }
                } else {
                    self.builder
                        .stack_slot(total_size as u32, Origin::synthetic())
                };

                // Zero-initialize the aggregate slot for enum variants.
                if enum_variant_idx.is_some() && total_size > 0 {
                    let zero = self.builder.iconst(0, Origin::synthetic());
                    let num_words = total_size.div_ceil(8);
                    for w in 0..num_words {
                        let byte_off = w * 8;
                        let chunk = std::cmp::min(8, total_size - byte_off) as u32;
                        let dst = if byte_off == 0 {
                            slot
                        } else {
                            let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                            self.builder
                                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                        };
                        self.current_mem = self.builder.store(
                            zero.into(),
                            dst.into(),
                            chunk,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    }
                }

                for (i, op) in operands.iter().enumerate() {
                    let field_ty = match op {
                        Operand::Copy(p) | Operand::Move(p) => {
                            Some(self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty))
                        }
                        Operand::Constant(c) => Some(self.monomorphize(c.ty())),
                        _ => None,
                    };
                    let bytes = field_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(8) as u32;
                    if bytes == 0 {
                        continue;
                    }
                    let mut val = self
                        .translate_operand(op)
                        .unwrap_or_else(|| self.builder.iconst(0, Origin::synthetic()));

                    // For large i128/u128 constants (>64 bits) in aggregates, iconst creates
                    // a 64-bit value that gets incorrectly stored as 16 bytes. Emit as static
                    // data and return a pointer so the word-by-word copy path handles it.
                    let is_i128_const = bytes == 16
                        && matches!(op, Operand::Constant(_))
                        && matches!(self.builder.value_type(val), Some(Type::Int))
                        && field_ty.map_or(false, |t| {
                            matches!(
                                t.kind(),
                                ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128)
                            )
                        });
                    if is_i128_const {
                        if let Operand::Constant(c) = op {
                            let mono_const = self.tcx.instantiate_and_normalize_erasing_regions(
                                self.instance.args,
                                ty::TypingEnv::fully_monomorphized(),
                                ty::EarlyBinder::bind(c.const_),
                            );
                            let const_val = match mono_const {
                                mir::Const::Val(v, _) => Some(v),
                                _ => {
                                    let typing_env = ty::TypingEnv::fully_monomorphized();
                                    mono_const.eval(self.tcx, typing_env, c.span).ok()
                                }
                            };
                            if let Some(mir::ConstValue::Scalar(mir::interpret::Scalar::Int(int))) =
                                const_val
                            {
                                let bits = int.to_bits(int.size());
                                // Only emit as static data if value doesn't fit in 64 bits
                                let is_signed = field_ty.map_or(false, |t| {
                                    matches!(t.kind(), ty::Int(ty::IntTy::I128))
                                });
                                let needs_static = if is_signed {
                                    // Signed: check if sign-extended 64-bit value differs
                                    let as_i64 = bits as i64;
                                    let sign_ext = as_i64 as i128;
                                    sign_ext != bits as i128
                                } else {
                                    // Unsigned: check if value > u64::MAX
                                    bits > u64::MAX as u128
                                };
                                if needs_static {
                                    let bytes_vec = bits.to_le_bytes().to_vec();
                                    let sym = format!(".Lconst.{}", {
                                        let id = *self.data_counter;
                                        *self.data_counter += 1;
                                        id
                                    });
                                    let sym_id = self.symbols.intern(&sym);
                                    self.static_data.push((sym_id, bytes_vec, vec![]));
                                    val = self.builder.symbol_addr(sym_id, Origin::synthetic());
                                }
                            }
                        }
                    }

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
                        let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                        self.builder
                            .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic())
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
                                Some(self.builder.iconst(meta as i64, Origin::synthetic()))
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
                                        Some(self.builder.iconst(len as i64, Origin::synthetic()))
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
                        self.current_mem = self.builder.store(
                            val.into(),
                            dst_addr.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        // Store fat component (length/vtable) into dst[8..16].
                        let off8 = self.builder.iconst(8, Origin::synthetic());
                        let hi = self.builder.ptradd(
                            dst_addr.into(),
                            off8.into(),
                            0,
                            Origin::synthetic(),
                        );
                        self.current_mem = self.builder.store(
                            fat_val.into(),
                            hi.into(),
                            8,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    } else if is_ptr_val && bytes > 8 {
                        // val is a pointer to multi-word data — copy word-by-word.
                        let num_words = (bytes as u64).div_ceil(8);
                        for w in 0..num_words {
                            let byte_off = w * 8;
                            let word_size = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                            let src = if byte_off == 0 {
                                val
                            } else {
                                let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                                self.builder
                                    .ptradd(val.into(), off.into(), 0, Origin::synthetic())
                            };
                            let word = self.builder.load(
                                src.into(),
                                word_size,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let dst = if byte_off == 0 {
                                dst_addr
                            } else {
                                let off = self.builder.iconst(byte_off as i64, Origin::synthetic());
                                self.builder.ptradd(
                                    dst_addr.into(),
                                    off.into(),
                                    0,
                                    Origin::synthetic(),
                                )
                            };
                            self.current_mem = self.builder.store(
                                word.into(),
                                dst.into(),
                                word_size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
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
                            None,
                            Origin::synthetic(),
                        );
                        self.current_mem = self.builder.store(
                            loaded.into(),
                            dst_addr.into(),
                            bytes,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                    } else {
                        self.current_mem = self.builder.store(
                            val.into(),
                            dst_addr.into(),
                            bytes,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
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
                // 1. Non-stack local with fat component tracked in fat_locals.
                if place.projection.is_empty()
                    && let Some(len) = self.fat_locals.get(place.local)
                {
                    return Some(len);
                }
                // 1b. Cast-to-fat metadata (e.g. NonNull<[T]> as *const [T]).
                if place.projection.is_empty()
                    && let Some(len) = self.cast_fat_meta.get(place.local)
                {
                    return Some(len);
                }
                // 2. Stack local: load length from slot + 8.
                if place.projection.is_empty()
                    && self.stack_locals.is_stack(place.local)
                    && let Some(slot) = self.locals.get(place.local)
                {
                    let off8 = self.builder.iconst(8, Origin::synthetic());
                    let len_addr =
                        self.builder
                            .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                    let data = self.builder.load(
                        len_addr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    return Some(data);
                }
                // 3. Projected place (e.g. _s.field): compute the fat
                //    pointer's address and load length from offset +8.
                if !place.projection.is_empty()
                    && let Some((addr, _)) = self.translate_place_to_addr(place)
                {
                    let addr = self.coerce_to_ptr(addr);
                    let off8 = self.builder.iconst(8, Origin::synthetic());
                    let len_addr =
                        self.builder
                            .ptradd(addr.into(), off8.into(), 0, Origin::synthetic());
                    let data = self.builder.load(
                        len_addr.into(),
                        8,
                        Type::Int,
                        self.current_mem.into(),
                        None,
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
                let op_ty = match operand {
                    Operand::Copy(p) | Operand::Move(p) => {
                        Some(self.monomorphize(p.ty(&self.mir.local_decls, self.tcx).ty))
                    }
                    Operand::Constant(c) => Some(self.monomorphize(c.ty())),
                    _ => None,
                };
                // Float negation: use FNeg IR op, which keeps the result Float-typed.
                if let Some(ty) = op_ty {
                    if ty.is_floating_point() {
                        let ft = match ty.kind() {
                            ty::Float(ty::FloatTy::F32) => FloatType::F32,
                            ty::Float(ty::FloatTy::F64) => FloatType::F64,
                            _ => return Some(v),
                        };
                        return Some(self.builder.fneg(
                            v.into(),
                            Type::Float(ft),
                            Origin::synthetic(),
                        ));
                    }
                }
                let neg_ann = op_ty.and_then(translate_annotation);
                // For large integral types (>8 bytes, e.g. i128) stored in memory,
                // translate_place_to_value returns a Ptr to the stack slot.
                // Load the value before negating.
                let v = if matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                    && op_ty.is_some_and(|t| t.is_integral())
                    && op_ty
                        .and_then(|t| type_size(self.tcx, t))
                        .is_some_and(|sz| sz > 8)
                {
                    let sz = op_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(16) as u32;
                    self.builder.load(
                        v.into(),
                        sz,
                        Type::Int,
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    )
                } else {
                    // Coerce Bool/Ptr to Int for integer negation.
                    self.coerce_to_int(v)
                };
                if !matches!(self.builder.value_type(v), Some(Type::Int)) {
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }
                let zero = self.builder.iconst(0, Origin::synthetic());
                Some(
                    self.builder
                        .sub(zero.into(), v.into(), neg_ann, Origin::synthetic()),
                )
            }
            Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
                let v = self.translate_operand(operand)?;
                let mir_ty = match operand {
                    Operand::Copy(p) | Operand::Move(p) => {
                        let ty = p.ty(&self.mir.local_decls, self.tcx).ty;
                        Some(self.monomorphize(ty))
                    }
                    Operand::Constant(c) => Some(self.monomorphize(c.ty())),
                    _ => None,
                };
                let not_ann = mir_ty.and_then(|t| translate_annotation(t));
                let is_bool = mir_ty.is_some_and(|t| t.is_bool());
                if is_bool {
                    // Boolean NOT: XOR 1.
                    let int_v = self.coerce_to_int(v);
                    let one = self.builder.iconst(1, Origin::synthetic());
                    Some(
                        self.builder
                            .xor(int_v.into(), one.into(), None, Origin::synthetic()),
                    )
                } else {
                    match self.builder.value_type(v) {
                        Some(Type::Bool) => {
                            let int_v = self.builder.bool_to_int(v.into(), Origin::synthetic());
                            let one = self.builder.iconst(1, Origin::synthetic());
                            Some(self.builder.xor(
                                int_v.into(),
                                one.into(),
                                None,
                                Origin::synthetic(),
                            ))
                        }
                        Some(Type::Ptr(_))
                            if mir_ty.is_some_and(|t| t.is_integral())
                                && mir_ty
                                    .and_then(|t| type_size(self.tcx, t))
                                    .is_some_and(|sz| sz > 8) =>
                        {
                            // The operand is a >8-byte integer (e.g. u128) stored in memory;
                            // translate_place_to_value returned a Ptr to the stack slot.
                            // Load the value as a 16-byte Int before bitwise NOT.
                            let sz =
                                mir_ty.and_then(|t| type_size(self.tcx, t)).unwrap_or(16) as u32;
                            let loaded = self.builder.load(
                                v.into(),
                                sz,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            let ones = self.builder.iconst(-1, Origin::synthetic());
                            Some(self.builder.xor(
                                loaded.into(),
                                ones.into(),
                                not_ann,
                                Origin::synthetic(),
                            ))
                        }
                        _ => {
                            // Bitwise NOT: XOR with -1.
                            let ones = self.builder.iconst(-1, Origin::synthetic());
                            Some(self.builder.xor(
                                v.into(),
                                ones.into(),
                                not_ann,
                                Origin::synthetic(),
                            ))
                        }
                    }
                }
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
                    return Some(self.builder.iconst(0, Origin::synthetic()));
                }
                let total = (elem_size * n) as u32;
                let slot = if dest_place.projection.is_empty() {
                    if let Some(existing) = self.locals.get(dest_place.local) {
                        if matches!(self.builder.value_type(existing), Some(Type::Ptr(_))) {
                            existing
                        } else {
                            self.builder.stack_slot(total, Origin::synthetic())
                        }
                    } else {
                        self.builder.stack_slot(total, Origin::synthetic())
                    }
                } else {
                    self.builder.stack_slot(total, Origin::synthetic())
                };
                let store_size = elem_size as u32;
                for i in 0..n {
                    let offset = (i * elem_size) as i64;
                    let dst = if offset == 0 {
                        slot
                    } else {
                        let off = self.builder.iconst(offset, Origin::synthetic());
                        self.builder
                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                    };
                    self.current_mem = self.builder.store(
                        elem_val.into(),
                        dst.into(),
                        store_size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                }
                self.stack_locals.mark(dest_place.local);
                Some(slot)
            }
            _ => None,
        }
    }

    pub(super) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    let val = self.locals.get(place.local);
                    // For scalar locals promoted to stack slots (multi-BB
                    // mutation), load the current value from the slot.
                    if self.stack_locals.is_stack(place.local)
                        && let Some(slot) = val
                    {
                        let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(8);
                        let slot_size = self.builder.stack_slot_size(slot);
                        let ir_ty = translate_ty(self.tcx, ty);
                        let is_slot_ptr =
                            matches!(self.builder.value_type(slot), Some(Type::Ptr(_)));
                        let should_load_stack_int = matches!(ir_ty, Some(Type::Int))
                            && is_slot_ptr
                            && ((size <= 8 && slot_size.is_some_and(|sz| sz <= 8))
                                || (size > 8
                                    && ty.is_integral()
                                    && slot_size.is_some_and(|sz| u64::from(sz) >= size)));
                        let should_load_stack_ptr = matches!(ir_ty, Some(Type::Ptr(_)))
                            && is_slot_ptr
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= 8);
                        let should_load_stack_scalar = is_slot_ptr
                            && size <= 8
                            && slot_size.is_some_and(|sz| sz <= 8)
                            && matches!(ir_ty, Some(Type::Bool | Type::Float(_)));
                        if should_load_stack_int
                            || should_load_stack_ptr
                            || should_load_stack_scalar
                        {
                            let load_ty = if should_load_stack_ptr {
                                Type::Ptr(0)
                            } else {
                                ir_ty.unwrap_or(Type::Int)
                            };
                            let ann = translate_annotation(ty);
                            let loaded = self.builder.load(
                                slot.into(),
                                size as u32,
                                load_ty,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                    }
                    // Non-stack local holding a memory address (e.g. symbol_addr
                    // for an indirect constant like `const S: Point = ...`).
                    // For Int-typed locals stored at a memory address (symbol or
                    // PtrAdd), load the actual value instead of returning the
                    // raw pointer.  This covers both small scalars (≤8 bytes)
                    // and large integers such as i128/u128 (16 bytes).
                    if !self.stack_locals.is_stack(place.local)
                        && let Some(v) = val
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                        && self.builder.is_memory_address(v)
                    {
                        let ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        let size = type_size(self.tcx, ty).unwrap_or(8);
                        if matches!(translate_ty(self.tcx, ty), Some(Type::Int))
                            && (size <= 8 || ty.is_integral())
                        {
                            let ann = translate_annotation(ty);
                            let loaded = self.builder.load(
                                v.into(),
                                size as u32,
                                Type::Int,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            return Some(loaded);
                        }
                    }
                    val
                } else {
                    self.translate_place_to_value(place)
                }
            }
            Operand::Constant(constant) => translate_const(
                self.tcx,
                self.instance,
                constant,
                &mut self.builder,
                &mut self.symbols,
                &mut self.static_data,
                &mut self.current_mem,
                &mut self.referenced_instances,
                self.data_counter,
            ),
            Operand::RuntimeChecks(_) => {
                // UbChecks / ContractChecks / OverflowChecks: emit false (0)
                // to skip runtime checks, matching release-mode behaviour.
                Some(self.builder.iconst(0, Origin::synthetic()))
            }
        }
    }
}
