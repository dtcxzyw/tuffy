use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Try to handle a call as a compiler intrinsic.
    /// Returns `true` if the call was fully handled (caller should return).
    /// Returns `false` if the intrinsic should fall through to the normal call path.
    pub(super) fn try_handle_intrinsic_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        intrinsic_name: &str,
        intrinsic_substs: &'tcx ty::List<ty::GenericArg<'tcx>>,
    ) -> bool {
        // Translate intrinsic arguments to IR values.
        let mut intrinsic_args: Vec<ValueRef> = Vec::new();
        for arg in args {
            if let Some(v) = self.translate_operand(&arg.node) {
                intrinsic_args.push(v);
                // Also push fat pointer metadata for intrinsics that
                // need it (e.g. size_of_val on unsized types).
                if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                    && place.projection.is_empty()
                    && let Some(fat_v) = self.fat_locals.get(place.local)
                {
                    let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                    if is_fat_ptr(self.tcx, local_ty) {
                        intrinsic_args.push(fat_v);
                    }
                }
            } else if intrinsic_name.starts_with("simd_") {
                self.tcx.dcx().fatal(format!(
                    "failed to translate SIMD intrinsic argument {:?} in {:?}, arg_ty={:?}",
                    &arg.node,
                    self.instance,
                    arg.node.ty(&self.mir.local_decls, self.tcx),
                ));
            }
        }

        // Try simple inline handling first (black_box, etc.).
        // Save the stack slot pointer before the intrinsic overwrites it
        // via locals.set — we need it to emit a store afterward.
        let saved_slot = if self.stack_locals.is_stack(destination.local) {
            self.locals.get(destination.local)
        } else {
            None
        };
        // When the destination has projections (e.g. `(*RET) = bswap(...)`),
        // pre-compute the projected address before the intrinsic overwrites
        // the local.  We also save the original local value to restore it.
        let has_dest_projection = !destination.projection.is_empty();
        // For Deref-based projections (e.g. `(*ptr).field`), the base
        // pointer must not change.  For Field/Index projections on a
        // non-stack local, we must persist the spill so future reads (in
        // subsequent blocks) see the mutated slot instead of the original
        // read-only constant.
        let dest_is_deref_projection = has_dest_projection
            && matches!(destination.projection.first(), Some(mir::PlaceElem::Deref));
        let (proj_addr, proj_size, saved_local_for_proj, spilled_local_for_proj) =
            if has_dest_projection {
                let saved = self.locals.get(destination.local);
                // When the local has no value yet (first assignment to a
                // projected field like `_8.0 = bswap(...)`), allocate a
                // stack slot so translate_place_to_addr_inner can compute
                // the field address.  Without this, it returns None and
                // the intrinsic result is never stored — causing reads in
                // other basic blocks to see uninitialized memory.
                if saved.is_none() && !dest_is_deref_projection {
                    let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
                    let size = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                    let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                    self.locals.set(destination.local, slot);
                }
                let info = if dest_is_deref_projection {
                    self.translate_place_to_addr(destination)
                } else {
                    // Non-deref: persist the spill so future reads via
                    // `locals` see the mutated slot.
                    self.translate_place_to_addr_inner(destination, true)
                }
                .map(|(a, ty)| {
                    let a = self.coerce_to_ptr(a);
                    let sz = type_size(self.tcx, ty).unwrap_or(8) as u32;
                    (a, sz)
                });
                // Capture the local *after* the potential spill.
                let spilled = self.locals.get(destination.local);
                match info {
                    Some((a, sz)) => (Some(a), sz, saved, spilled),
                    None => (None, 0, saved, spilled),
                }
            } else {
                (None, 0, None, None)
            };
        let handled = self.translate_intrinsic(
            intrinsic_name,
            intrinsic_substs,
            &intrinsic_args,
            destination.local,
            if has_dest_projection { proj_addr } else { None },
        );
        if handled {
            // Capture the intrinsic result before any store-back.
            let intrinsic_result = self.locals.get(destination.local);

            if has_dest_projection {
                // Destination has projections (e.g. `(*RET) = bswap(...)`).
                // Store the result through the pre-computed projected
                // address and restore the local to its correct slot.
                // For Deref projections the base pointer is unchanged
                // (restore to original).  For Field/Index projections on a
                // non-stack local we restore to the newly spilled slot so
                // subsequent reads see the mutation.
                let restore_target = if dest_is_deref_projection {
                    saved_local_for_proj
                } else {
                    spilled_local_for_proj
                };
                if let Some(slot) = restore_target {
                    self.locals.set(destination.local, slot);
                }
                // If the intrinsic didn't change the local (e.g. i128
                // bswap writes directly through the pointer obtained from
                // locals.get()), the data is already at the correct
                // location — skip the redundant store which would
                // overwrite the result with the raw pointer value.
                let intrinsic_changed_local = intrinsic_result != saved_local_for_proj;
                if intrinsic_changed_local
                    && let Some(result) = intrinsic_result
                    && let Some(addr) = proj_addr
                    && proj_size > 0
                {
                    self.current_mem = self
                        .builder
                        .store(
                            result.into(),
                            addr.into(),
                            proj_size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else {
                // If the destination is a stack local, the intrinsic set the
                // local to the raw result value.  Store it into the stack slot
                // and restore the local to point at the slot.
                // If the local still points at the slot (result_val == slot),
                // the intrinsic already wrote to the slot directly (e.g. i128
                // bswap) — skip the redundant store.
                if let Some(slot) = saved_slot
                    && let Some(result_val) = self.locals.get(destination.local)
                    && result_val != slot
                {
                    let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
                    let size = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                    let part_bytes = self.target_part_bytes() as u32;
                    // When result_val is a pointer to a known memory
                    // location (stack slot, symbol, ptr_add) and the type
                    // spans multiple direct ABI parts, copy word-by-word from that
                    // address.  Bare pointer *values* (e.g. the data-ptr
                    // half of a fat pointer returned by black_box) must
                    // NOT be dereferenced — fall through to the scalar
                    // store path instead.
                    let val_is_ptr =
                        matches!(self.builder.value_type(result_val), Some(Type::Ptr(_)));
                    if val_is_ptr && self.builder.is_memory_address(result_val) {
                        let mut offset = 0u32;
                        while offset < size {
                            let chunk = std::cmp::min(part_bytes, size - offset);
                            let src_addr = if offset == 0 {
                                result_val
                            } else {
                                let off = self.builder.iconst(
                                    offset as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                self.builder
                                    .ptradd(result_val.into(), off.into(), 0, Origin::synthetic())
                                    .raw()
                            };
                            let word = self.builder.load(
                                src_addr.into(),
                                chunk,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(chunk),
                                Origin::synthetic(),
                            );
                            let dst_addr = if offset == 0 {
                                slot
                            } else {
                                let off = self.builder.iconst(
                                    offset as i64,
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
                                    dst_addr.into(),
                                    chunk,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            offset += chunk;
                        }
                    } else {
                        // For fat-pointer types the result is just the
                        // first scalar (e.g. data_ptr); cap the store at one
                        // ABI part so we don't write past the value width.
                        // bytes so we don't write past the value width.
                        // The second half (metadata) is persisted separately
                        // by the fat-metadata propagation below.
                        let store_size = if val_is_ptr && size > part_bytes {
                            part_bytes
                        } else {
                            size.max(1)
                        };
                        self.current_mem = self
                            .builder
                            .store(
                                result_val.into(),
                                slot.into(),
                                store_size,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                    }
                    self.locals.set(destination.local, slot);
                }

                // Propagate fat pointer metadata to the stack slot.
                // When an intrinsic (e.g. black_box) sets fat_locals for
                // the destination, we must also persist the metadata to
                // slot+part_bytes so that Return loads see both halves.
                if let Some(fat_val) = self.fat_locals.get(destination.local)
                    && let Some(slot) = self.locals.get(destination.local)
                    && self.stack_locals.is_stack(destination.local)
                {
                    let off = self.builder.iconst(
                        self.target_part_bytes() as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let meta_addr =
                        self.builder
                            .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                    self.current_mem = self
                        .builder
                        .store(
                            fat_val.into(),
                            meta_addr.into(),
                            self.target_part_bytes() as u32,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } // end else (no dest projection)
            if let Some(target) = target {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            return true;
        }

        // Try lowering memory intrinsics to libc calls.
        let mem_handled = self.translate_memory_intrinsic(
            intrinsic_name,
            intrinsic_substs,
            &intrinsic_args,
            destination.local,
        );
        if let Some(new_mem) = mem_handled {
            self.current_mem = new_mem;
            // Store-back for stack locals: translate_memory_intrinsic
            // may set the local to a raw result value via locals.set().
            // If the destination is a stack local, persist the value
            // into the stack slot so that merge points (multiple BBs
            // converging on a common successor) read the correct data.
            if let Some(slot) = saved_slot
                && let Some(result_val) = self.locals.get(destination.local)
                && result_val != slot
            {
                let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
                let size = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                let val_is_ptr = matches!(self.builder.value_type(result_val), Some(Type::Ptr(_)));
                if val_is_ptr && self.builder.is_memory_address(result_val) {
                    let mut offset = 0u32;
                    while offset < size {
                        let chunk = std::cmp::min(8, size - offset);
                        let src_addr = if offset == 0 {
                            result_val
                        } else {
                            let off = self.builder.iconst(
                                offset as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .ptradd(result_val.into(), off.into(), 0, Origin::synthetic())
                                .raw()
                        };
                        let word = self.builder.load(
                            src_addr.into(),
                            chunk,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(chunk),
                            Origin::synthetic(),
                        );
                        let dst_addr = if offset == 0 {
                            slot
                        } else {
                            let off = self.builder.iconst(
                                offset as i64,
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
                                dst_addr.into(),
                                chunk,
                                self.current_mem.into(),
                                Origin::synthetic(),
                            )
                            .raw();
                        offset += chunk;
                    }
                } else {
                    self.current_mem = self
                        .builder
                        .store(
                            result_val.into(),
                            slot.into(),
                            size.max(1),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
                self.locals.set(destination.local, slot);
            }
            if let Some(target) = target {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            return true;
        }
        // Intrinsic detected but not handled inline.  If it maps to a
        // libc symbol (e.g. compare_bytes → memcmp), fall through to
        // the normal call path so resolve_call_target can emit the call.
        // Newer intrinsics (e.g. carryless_mul) have fallback bodies
        // compiled as regular functions — also fall through for those.
        // Any intrinsic that reaches this point must lower to either a libc
        // symbol or a real Rust fallback body. Silent no-op lowering is a bug.
        if intrinsic_to_libc(intrinsic_name).is_none() {
            // Check if the intrinsic has a fallback body we can call.
            // Intrinsics with must_be_overridden=false have Rust
            // fallback implementations; those with must_be_overridden=true
            // must be handled by the backend.
            let has_fallback_body = if let Operand::Constant(c) = func {
                let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                    self.instance.args,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(c.ty()),
                );
                if let ty::FnDef(def_id, _) = fn_ty.kind() {
                    self.tcx
                        .intrinsic(*def_id)
                        .is_some_and(|i| !i.must_be_overridden)
                } else {
                    false
                }
            } else {
                false
            };

            if !has_fallback_body {
                self.tcx.dcx().fatal(format!(
                    "unsupported intrinsic {intrinsic_name} in {:?}",
                    self.instance
                ));
            }
            // has_fallback_body: fall through to normal call path below
        }
        false
    }
}
