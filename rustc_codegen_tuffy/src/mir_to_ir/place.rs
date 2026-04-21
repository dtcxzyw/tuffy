use rustc_middle::mir::{Place, PlaceElem};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Returns the discriminant value for one enum variant.
    pub(super) fn enum_variant_discriminant(
        &self,
        ty: ty::Ty<'tcx>,
        variant_idx: rustc_abi::VariantIdx,
    ) -> Option<i64> {
        let ty = self.monomorphize(ty);
        let ty::Adt(adt_def, _) = ty.kind() else {
            return None;
        };
        Some(adt_def.discriminant_for_variant(self.tcx, variant_idx).val as i64)
    }

    /// Returns payload/empty variant info for enums cached in `option_scalar_locals`.
    pub(super) fn simple_option_scalar_info(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Option<(ty::Ty<'tcx>, rustc_abi::VariantIdx, rustc_abi::VariantIdx)> {
        let ty = self.monomorphize(ty);
        let ty::Adt(adt_def, args) = ty.kind() else {
            return None;
        };
        if !adt_def.is_enum() || adt_def.variants().len() != 2 {
            return None;
        }

        let payload_variants = adt_def
            .variants()
            .iter_enumerated()
            .filter_map(|(variant_idx, variant)| {
                let [field] = variant.fields.raw.as_slice() else {
                    return None;
                };
                let field_ty = self.monomorphize(field.ty(self.tcx, args));
                let field_size = type_size(self.tcx, field_ty).unwrap_or(0);
                (field_size > 0
                    && matches!(
                        translate_ty(self.tcx, field_ty),
                        Some(Type::Int | Type::Bool | Type::Ptr(_))
                    ))
                .then_some((variant_idx, field_ty))
            })
            .collect::<Vec<_>>();
        let [(payload_variant, payload_ty)] = payload_variants.as_slice() else {
            return None;
        };

        let empty_variant = adt_def
            .variants()
            .iter_enumerated()
            .find(|(variant_idx, variant)| {
                if variant_idx == payload_variant {
                    return false;
                }
                variant.fields.iter().all(|field| {
                    let field_ty = self.monomorphize(field.ty(self.tcx, args));
                    type_size(self.tcx, field_ty).unwrap_or(0) == 0
                })
            })
            .map(|(variant_idx, _)| variant_idx)?;

        Some((*payload_ty, *payload_variant, empty_variant))
    }

    /// Returns the payload type for a simple scalar `Option<T>`.
    pub(super) fn simple_option_scalar_payload_ty(&self, ty: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        self.simple_option_scalar_info(ty)
            .map(|(payload_ty, _, _)| payload_ty)
    }

    /// Returns the cached payload for a simple scalar `Option<T>` projection.
    pub(super) fn simple_option_scalar_payload(&mut self, place: &Place<'tcx>) -> Option<ValueRef> {
        if place.projection.len() != 2
            || self.stack_locals.is_stack(place.local)
            || !matches!(place.projection[1], PlaceElem::Field(idx, _) if idx.as_usize() == 0)
        {
            return None;
        }
        let PlaceElem::Downcast(_, payload_variant) = place.projection[0] else {
            return None;
        };
        let (_, expected_variant, _) =
            self.simple_option_scalar_info(self.mir.local_decls[place.local].ty)?;
        let cached = self.option_scalar_locals.get(place.local)?;
        (payload_variant == expected_variant && cached.payload_variant == expected_variant)
            .then_some(cached.payload)
    }

    /// Returns cached `(data_ptr, len)` for one field of a split-pair local.
    pub(super) fn split_pair_field(&mut self, place: &Place<'tcx>) -> Option<(ValueRef, ValueRef)> {
        if place.projection.len() != 1 {
            return None;
        }
        let pair = self.split_pair_locals.get(place.local)?;
        let PlaceElem::Field(field_idx, field_ty) = place.projection[0] else {
            return None;
        };
        let field_ty = self.monomorphize(field_ty);
        if !is_fat_ptr(self.tcx, field_ty) {
            return None;
        }
        pair.field(field_idx.as_usize())
    }

    /// Materializes a cached split-pair local into a stack slot on demand.
    pub(super) fn materialize_split_pair_local(
        &mut self,
        local: rustc_middle::mir::Local,
    ) -> Option<ValueRef> {
        if let Some(existing) = self.locals.get(local)
            && self.builder.stack_slot_size(existing).is_some()
        {
            return Some(existing);
        }
        let pair = self.split_pair_locals.get(local)?;
        let ty = self.monomorphize(self.mir.local_decls[local].ty);
        let size = type_size(self.tcx, ty).unwrap_or(32).max(1) as u32;
        let align = type_align(self.tcx, ty).unwrap_or(8) as u32;
        let slot = self.builder.stack_slot(size, align, Origin::synthetic());
        self.current_mem = self
            .builder
            .store(
                pair.left_ptr.into(),
                slot.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
        let off8 = self
            .builder
            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
        let left_len_addr = self
            .builder
            .ptradd(slot.into(), off8.into(), 0, Origin::synthetic())
            .raw();
        self.current_mem = self
            .builder
            .store(
                pair.left_len.into(),
                left_len_addr.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
        let off16 = self
            .builder
            .iconst(16, 64, IntSignedness::DontCare, Origin::synthetic());
        let right_ptr_addr = self
            .builder
            .ptradd(slot.into(), off16.into(), 0, Origin::synthetic())
            .raw();
        self.current_mem = self
            .builder
            .store(
                pair.right_ptr.into(),
                right_ptr_addr.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
        let off24 = self
            .builder
            .iconst(24, 64, IntSignedness::DontCare, Origin::synthetic());
        let right_len_addr = self
            .builder
            .ptradd(slot.into(), off24.into(), 0, Origin::synthetic())
            .raw();
        self.current_mem = self
            .builder
            .store(
                pair.right_len.into(),
                right_len_addr.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
        self.locals.set(local, slot);
        Some(slot)
    }

    /// Computes the address that a MIR place refers to, along with its final type.
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
        let mut addr = if let Some(value) = self.locals.get(place.local) {
            value
        } else if self.split_pair_locals.get(place.local).is_some() {
            self.materialize_split_pair_local(place.local)?
        } else {
            return None;
        };
        let mut cur_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
        let pair_materialized = self.split_pair_locals.get(place.local).is_some()
            && self.builder.stack_slot_size(addr).is_some();

        // If the base local is not stack-allocated and the first projection
        // needs an address (Field, Index, etc.), spill the scalar value to a
        // temporary stack slot so we can compute sub-field addresses.
        if !pair_materialized
            && !self.stack_locals.is_stack(place.local)
            && !place.projection.is_empty()
            && !matches!(place.projection[0], PlaceElem::Deref)
        {
            let size = type_size(self.tcx, cur_ty).unwrap_or(8) as u32;
            let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
            // For fat pointer locals (e.g. &[T] parameters), the value in
            // `addr` is just the data pointer (8 bytes) while the metadata
            // (length / vtable) lives in fat_locals.  Reconstruct the full
            // fat pointer in the stack slot instead of doing a wide store
            // that would dereference the data pointer.
            if let Some(fat_val) = self.fat_locals.get(place.local) {
                // Store data pointer into slot[0..8].
                self.current_mem = self
                    .builder
                    .store(
                        addr.into(),
                        slot.into(),
                        8,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                // Store fat component (length/vtable) into slot[8..16].
                let off8 = self
                    .builder
                    .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                let hi_addr = self
                    .builder
                    .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
                self.current_mem = self
                    .builder
                    .store(
                        fat_val.into(),
                        hi_addr.into(),
                        8,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
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
                        let off = self.builder.iconst(
                            byte_off as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        self.builder
                            .ptradd(addr.into(), off.into(), 0, Origin::synthetic())
                            .raw()
                    };
                    let word = self.builder.load(
                        src.into(),
                        chunk,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(chunk),
                        Origin::synthetic(),
                    );
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
                            word.into(),
                            dst.into(),
                            chunk,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else {
                self.current_mem = self
                    .builder
                    .store(
                        addr.into(),
                        slot.into(),
                        size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
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
                        let off_val = self.builder.iconst(
                            offset as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        addr = self
                            .builder
                            .ptradd(addr.into(), off_val.into(), 0, Origin::synthetic())
                            .raw();
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
                            int_annotation_for_bytes(8),
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
                    let size_val = self.builder.iconst(
                        elem_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let byte_offset = self.builder.mul(
                        idx_val.into(),
                        size_val.into(),
                        IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::DontCare,
                        },
                        Origin::synthetic(),
                    );
                    addr = self
                        .builder
                        .ptradd(addr.into(), byte_offset.into(), 0, Origin::synthetic())
                        .raw();
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
                PlaceElem::OpaqueCast(ty) | PlaceElem::UnwrapUnsafeBinder(ty) => {
                    // These projections only refine the static type carried by the
                    // place. The underlying address remains unchanged.
                    cur_ty = self.monomorphize(ty);
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
                            let off_val = self.builder.iconst(
                                byte_off as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            addr = self
                                .builder
                                .ptradd(addr.into(), off_val.into(), 0, Origin::synthetic())
                                .raw();
                        }
                    } else {
                        // from_end: index = len - offset
                        let ann = IntAnnotation {
                            bit_width: 64,
                            signedness: IntSignedness::Unsigned,
                        };
                        let off_val = self.builder.iconst(
                            offset as i64,
                            64,
                            IntSignedness::Unsigned,
                            Origin::synthetic(),
                        );
                        let idx = match cur_ty.kind() {
                            ty::Array(_, n) => {
                                let n = n.try_to_target_usize(self.tcx).unwrap_or(0);
                                self.builder.iconst(
                                    (n - offset) as i64,
                                    64,
                                    IntSignedness::Unsigned,
                                    Origin::synthetic(),
                                )
                            }
                            ty::Slice(_) => {
                                let len = self.find_fat_metadata_for_place(place)?;
                                self.builder.sub(
                                    len.into(),
                                    off_val.into(),
                                    ann,
                                    Origin::synthetic(),
                                )
                            }
                            _ => return None,
                        };
                        let size_val = self.builder.iconst(
                            elem_size as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let byte_off =
                            self.builder
                                .mul(idx.into(), size_val.into(), ann, Origin::synthetic());
                        addr = self
                            .builder
                            .ptradd(addr.into(), byte_off.into(), 0, Origin::synthetic())
                            .raw();
                    }
                    cur_ty = elem_ty;
                }
                PlaceElem::Subslice { from, to, from_end } => {
                    let elem_ty = match cur_ty.kind() {
                        ty::Array(elem_ty, _) | ty::Slice(elem_ty) => *elem_ty,
                        _ => return None,
                    };
                    let elem_size = type_size(self.tcx, elem_ty)?;
                    if from > 0 {
                        let off = self.builder.iconst(
                            (from * elem_size) as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        addr = self
                            .builder
                            .ptradd(addr.into(), off.into(), 0, Origin::synthetic())
                            .raw();
                    }
                    cur_ty = if from_end {
                        match cur_ty.kind() {
                            // Array: [T; N] -> [T; N - from - to]
                            ty::Array(_, n) => {
                                let n = n.try_to_target_usize(self.tcx).unwrap_or(0);
                                ty::Ty::new_array(self.tcx, elem_ty, n - from - to)
                            }
                            // Slice: result is still a slice
                            ty::Slice(_) => cur_ty,
                            _ => return None,
                        }
                    } else {
                        // Slice: result is still a slice
                        cur_ty
                    };
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
            return self
                .locals
                .get(place.local)
                .or_else(|| self.materialize_split_pair_local(place.local));
        }
        if let Some(payload) = self.simple_option_scalar_payload(place) {
            return Some(payload);
        }
        if let Some((data_ptr, _)) = self.split_pair_field(place) {
            return Some(data_ptr);
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
                    return Some(
                        self.builder
                            .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                            .raw(),
                    );
                }
            }
        }
        let (addr, projected_ty) = self.translate_place_to_addr(place)?;
        let addr = self.coerce_to_ptr(addr);
        let bytes = type_size(self.tcx, projected_ty).unwrap_or(8) as u32;
        // ZST: no data to load — return a dummy value.
        if bytes == 0 {
            return Some(
                self.builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                    .raw(),
            );
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
        if let Some((load_ty, load_bytes, ann)) = scalar_value_info(self.tcx, projected_ty) {
            let data = self.builder.load(
                addr.into(),
                load_bytes,
                load_ty,
                self.current_mem.into(),
                ann,
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
        let ann = if matches!(ty, Type::Int) {
            int_annotation_for_bytes(bytes)
        } else {
            None
        };
        let data = self.builder.load(
            addr.into(),
            bytes,
            ty,
            self.current_mem.into(),
            ann,
            Origin::synthetic(),
        );
        Some(data)
    }
}
