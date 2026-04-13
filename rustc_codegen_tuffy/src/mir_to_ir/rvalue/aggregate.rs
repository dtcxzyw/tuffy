use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Returns whether `operand` is currently represented by a stack slot.
    fn operand_uses_stack_slot(&self, operand: &Operand<'tcx>) -> bool {
        matches!(
            operand,
            Operand::Copy(place) | Operand::Move(place)
                if place.projection.is_empty() && self.stack_locals.is_stack(place.local)
        )
    }

    /// Returns cached or recomputed fat-pointer metadata for `operand`.
    fn fat_metadata_for_operand(&mut self, operand: &Operand<'tcx>) -> Option<ValueRef> {
        self.extract_fat_component(&Rvalue::Use(operand.clone()))
    }

    /// Computes the source address to use when copying `operand` into memory.
    fn copy_source_addr_for_operand(
        &mut self,
        operand: &Operand<'tcx>,
        val: ValueRef,
    ) -> Option<ValueRef> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if !place.projection.is_empty() => self
                .translate_place_to_addr(place)
                .map(|(addr, _)| self.coerce_to_ptr(addr)),
            Operand::Copy(place) | Operand::Move(place)
                if place.projection.is_empty() && self.stack_locals.is_stack(place.local) =>
            {
                self.locals.get(place.local)
            }
            Operand::Constant(_) if self.builder.is_memory_address(val) => Some(val),
            _ => None,
        }
    }

    /// Stores `val` into `dst_addr`, using the operand shape to choose the right strategy.
    pub(super) fn store_operand_value(
        &mut self,
        operand: &Operand<'tcx>,
        val: ValueRef,
        dst_addr: ValueRef,
        bytes: u32,
    ) {
        let is_ptr_val = matches!(self.builder.value_type(val), Some(Type::Ptr(_)));
        let operand_ty =
            operand_ty_projected(operand, self.mir, self.tcx).map(|ty| self.monomorphize(ty));
        let operand_is_scalar =
            operand_ty.is_some_and(|ty| matches!(repr_kind(self.tcx, ty), ReprKind::Scalar));
        let val_is_stack_slot = self.builder.stack_slot_size(val).is_some()
            && self.builder.is_local_memory_address(val);

        if is_ptr_val && bytes <= 8 && operand_is_scalar && !val_is_stack_slot {
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
            return;
        }

        if bytes > 8
            && let Some(fat_val) = self.fat_metadata_for_operand(operand)
        {
            let data_ptr = if self.operand_uses_stack_slot(operand) {
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
            self.current_mem = self
                .builder
                .store(
                    data_ptr.into(),
                    dst_addr.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();
            let off8 = self
                .builder
                .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
            let meta_addr =
                self.builder
                    .ptradd(dst_addr.into(), off8.into(), 0, Origin::synthetic());
            self.current_mem = self
                .builder
                .store(
                    fat_val.into(),
                    meta_addr.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();
            return;
        }

        if is_ptr_val && bytes > 8 {
            let src_base = self
                .copy_source_addr_for_operand(operand, val)
                .unwrap_or(val);
            let num_words = (bytes as u64).div_ceil(8);
            for w in 0..num_words {
                let byte_off = w * 8;
                let word_size = std::cmp::min(8, bytes as u64 - byte_off) as u32;
                let src_addr = if byte_off == 0 {
                    src_base
                } else {
                    let off = self.builder.iconst(
                        byte_off as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    self.builder
                        .ptradd(src_base.into(), off.into(), 0, Origin::synthetic())
                        .raw()
                };
                let word = self.builder.load(
                    src_addr.into(),
                    word_size,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(word_size),
                    Origin::synthetic(),
                );
                let chunk_dst = if byte_off == 0 {
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
                        chunk_dst.into(),
                        word_size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
            return;
        }

        if self.operand_uses_stack_slot(operand)
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
            return;
        }

        if is_ptr_val
            && bytes <= 8
            && self.builder.is_symbol_addr(val)
            && self.is_indirect_nonref_const(operand)
            && !operand_is_scalar
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
            return;
        }

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

    /// Lowers aggregate construction by assembling the destination in memory or registers.
    pub(super) fn translate_aggregate(
        &mut self,
        kind: &mir::AggregateKind<'tcx>,
        operands: &[Operand<'tcx>],
        dest_place: &Place<'tcx>,
    ) -> Option<ValueRef> {
        // Extract enum variant index when constructing an enum.
        let enum_variant_idx = match kind {
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
        let agg_ty = match kind {
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
        let is_coroutine = matches!(kind, mir::AggregateKind::Coroutine(..));
        if (enum_variant_idx.is_some() || operands.is_empty() || is_coroutine) && total_size > 0 {
            let zero = self
                .builder
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
            let field_ty =
                operand_ty_projected(op, self.mir, self.tcx).map(|ty| self.monomorphize(ty));
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
                variant_field_offset(self.tcx, agg_ty, variant_idx, i).unwrap_or(i as u64 * 8)
            } else {
                field_offset(self.tcx, agg_ty, i).unwrap_or(i as u64 * 8)
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
            self.store_operand_value(op, val, dst_addr, bytes);
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
}
