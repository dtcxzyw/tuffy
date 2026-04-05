use rustc_middle::mir::Place;
use rustc_middle::ty;
use tuffy_ir::instruction::{ICmpOp, Origin};
use tuffy_ir::types::{IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::types::*;

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

    /// Set the discriminant of an enum at `place` to `variant_index`.
    ///
    /// Handles `TagEncoding::Direct` (store discriminant value) and
    /// `TagEncoding::Niche` (store niche value, skip for untagged variant).
    pub(super) fn translate_set_discriminant(
        &mut self,
        place: &Place<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let place_ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(place_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        // Compute the tag value to store.
        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match place_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    // The payload already encodes this variant — nothing to write.
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

        // Resolve the base address of the enum.
        let base_addr = if place.projection.is_empty() {
            if self.stack_locals.is_stack(place.local) {
                match self.locals.get(place.local) {
                    Some(v) => v,
                    None => return,
                }
            } else {
                return;
            }
        } else {
            match self.translate_place_to_addr(place) {
                Some((addr, _)) => self.coerce_to_ptr(addr),
                None => return,
            }
        };

        // Tag field offset and store size.
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

        let tag_const =
            self.builder
                .iconst(tag_val, 64, IntSignedness::DontCare, Origin::synthetic());
        self.current_mem = self
            .builder
            .store(
                tag_const.into(),
                tag_addr.into(),
                tag_size,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
    }

    /// Write the discriminant tag for an enum variant into a slot pointer.
    ///
    /// Called from the `Rvalue::Aggregate` handler to set the correct
    /// discriminant after storing variant fields.
    pub(super) fn write_enum_tag(
        &mut self,
        slot: ValueRef,
        enum_ty: ty::Ty<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let layout = match self.tcx.layout_of(typing_env.as_query_input(enum_ty)) {
            Ok(l) => l,
            Err(_) => return,
        };

        let (tag, tag_encoding, tag_field) = match layout.variants {
            rustc_abi::Variants::Single { .. } | rustc_abi::Variants::Empty => return,
            rustc_abi::Variants::Multiple {
                ref tag,
                ref tag_encoding,
                tag_field,
                ..
            } => (*tag, tag_encoding.clone(), tag_field),
        };

        let tag_val: i64 = match &tag_encoding {
            rustc_abi::TagEncoding::Direct => match enum_ty.kind() {
                ty::Adt(adt_def, _) => {
                    adt_def
                        .discriminant_for_variant(self.tcx, variant_index)
                        .val as i64
                }
                _ => variant_index.as_u32() as i64,
            },
            rustc_abi::TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } => {
                if variant_index == *untagged_variant {
                    return;
                }
                let variant_u128 = variant_index.as_u32() as u128;
                let start_u128 = niche_variants.start().as_u32() as u128;
                niche_start.wrapping_add(variant_u128 - start_u128) as i64
            }
        };

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
                .ptradd(slot.into(), off.into(), 0, Origin::synthetic())
                .raw()
        } else {
            slot
        };

        let tag_const =
            self.builder
                .iconst(tag_val, 64, IntSignedness::DontCare, Origin::synthetic());
        self.current_mem = self
            .builder
            .store(
                tag_const.into(),
                tag_addr.into(),
                tag_size,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
    }
}
