use rustc_middle::mir::{Place, PlaceElem};
use rustc_middle::ty;
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::{IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
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
        // Wide integral scalars (e.g. i128): load as a full-width
        // Type::Int value so downstream code sees a value, not an
        // address. The legalizer lowers wide integer values later.
        if bytes > 8 && projected_ty.is_integral() {
            let ann = translate_annotation(projected_ty);
            let data = self.builder.load(
                addr.into(),
                bytes,
                Type::Int,
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
