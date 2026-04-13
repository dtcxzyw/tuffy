use super::*;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Lowers MIR `Drop` terminators into explicit drop-glue calls.
    pub(super) fn translate_drop(
        &mut self,
        place: &mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: &mir::UnwindAction,
    ) {
        let drop_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
        let drop_ty = self.monomorphize(drop_ty);
        let target_block = self.block_map.get(target);
        let cleanup_label = match unwind {
            mir::UnwindAction::Cleanup(cleanup_bb) => {
                Some(self.setup_cleanup_landing_pad(*cleanup_bb))
            }
            _ => None,
        };

        // Only emit drop glue when the type actually needs dropping.
        if drop_ty.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) {
            // Trait object drops: dispatch through vtable[0] instead of
            // calling drop_in_place directly (which would recurse).
            if matches!(drop_ty.kind(), ty::Dynamic(..)) {
                // The place is `*local` where local is a fat pointer
                // (data ptr + vtable ptr). Get both components.
                let base_local = place.local;
                let data_ptr = self.locals.get(base_local);
                let vtable_ptr = self.fat_locals.get(base_local);
                if let (Some(data), Some(vtable)) = (data_ptr, vtable_ptr) {
                    // Load drop function pointer from vtable[0].
                    // It may be NULL for types with no drop glue.
                    let drop_fn = self.builder.load(
                        vtable.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    // Null check: vtable drop can be null for
                    // trivially-droppable concrete types.
                    let drop_as_int =
                        self.builder
                            .ptrtoint(drop_fn.into(), 64, Origin::synthetic());
                    let zero =
                        self.builder
                            .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic());
                    let is_nonnull = self.builder.icmp(
                        ICmpOp::Ne,
                        drop_as_int.into(),
                        zero.into(),
                        Origin::synthetic(),
                    );
                    let call_block = self.builder.create_block();
                    let call_mem_arg = self.builder.add_block_arg(call_block, Type::Mem, None);
                    let merge_block = self.builder.create_block();
                    let merge_mem_arg = self.builder.add_block_arg(merge_block, Type::Mem, None);

                    self.builder.brif(
                        is_nonnull.into(),
                        call_block,
                        vec![self.current_mem.into()],
                        merge_block,
                        vec![self.current_mem.into()],
                        Origin::synthetic(),
                    );

                    // call_block: invoke the drop function
                    self.builder.switch_to_block(call_block);
                    let (call_mem, _) = self.builder.call(
                        drop_fn.into(),
                        vec![data.into()],
                        Type::Unit,
                        call_mem_arg.into(),
                        cleanup_label,
                        None,
                        Origin::synthetic(),
                    );
                    self.builder
                        .br(merge_block, vec![call_mem.into()], Origin::synthetic());

                    // Continue from merge_block
                    self.builder.switch_to_block(merge_block);
                    self.current_mem = merge_mem_arg;
                }
            } else {
                let drop_instance = ty::Instance::resolve_drop_in_place(self.tcx, drop_ty);
                self.referenced_instances.push(drop_instance);
                if !drop_instance.args.has_non_region_param() {
                    let sym_name = self.tcx.symbol_name(drop_instance).name.to_string();
                    let sym_id = self.symbols.intern(&sym_name);
                    let callee = self.builder.symbol_addr(sym_id, Origin::synthetic());

                    // Get a pointer to the place being dropped, plus
                    // optional metadata for unsized drops (*mut [T] etc.).
                    let (drop_ptr, drop_meta): (Option<ValueRef>, Option<ValueRef>) = if place
                        .projection
                        .is_empty()
                    {
                        if self.stack_locals.is_stack(place.local) {
                            (self.locals.get(place.local), None)
                        } else if let Some(v) = self.locals.get(place.local) {
                            // Non-stack local: the value IS the pointer
                            // (e.g. a Box or reference).  For types that
                            // need dropping and are stored as a register
                            // value, we need to spill to a stack slot so
                            // drop_in_place gets a valid &mut T.
                            let ty_size = type_size(self.tcx, drop_ty).unwrap_or(8);
                            if ty_size == 0 {
                                // ZST with a dummy register value —
                                // use a dangling aligned pointer so
                                // drop_in_place receives a well-aligned &mut T.
                                let align = self
                                    .tcx
                                    .layout_of(
                                        ty::TypingEnv::fully_monomorphized()
                                            .as_query_input(drop_ty),
                                    )
                                    .map(|l| l.align.abi.bytes())
                                    .unwrap_or(1);
                                (
                                    Some(
                                        self.builder
                                            .iconst(
                                                align as i64,
                                                64,
                                                IntSignedness::DontCare,
                                                Origin::synthetic(),
                                            )
                                            .raw(),
                                    ),
                                    None,
                                )
                            } else if let Some(fat_val) = self.fat_locals.get(place.local) {
                                // Fat pointer: drop_in_place<[T]> / drop_in_place<dyn Trait>
                                // takes the fat pointer components as separate register
                                // arguments (data_ptr in rdi, metadata in rsi).
                                (Some(v), Some(fat_val))
                            } else if ty_size > self.target_part_bytes()
                                || matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                            {
                                (Some(v), None)
                            } else {
                                let slot =
                                    self.builder
                                        .stack_slot(ty_size as u32, 0, Origin::synthetic());
                                self.current_mem = self
                                    .builder
                                    .store(
                                        v.into(),
                                        slot.into(),
                                        ty_size as u32,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                (Some(slot), None)
                            }
                        } else {
                            // ZST with no stored value — use a
                            // dangling aligned pointer so
                            // drop_in_place is still called.
                            let align = self
                                .tcx
                                .layout_of(
                                    ty::TypingEnv::fully_monomorphized().as_query_input(drop_ty),
                                )
                                .map(|l| l.align.abi.bytes())
                                .unwrap_or(1);
                            (
                                Some(
                                    self.builder
                                        .iconst(
                                            align as i64,
                                            64,
                                            IntSignedness::DontCare,
                                            Origin::synthetic(),
                                        )
                                        .raw(),
                                ),
                                None,
                            )
                        }
                    } else {
                        let addr = self
                            .translate_place_to_addr(place)
                            .map(|(a, _)| self.coerce_to_ptr(a));
                        // For unsized drops through a Deref of a fat pointer
                        // (e.g. `(*_6)` where `_6: *const [T]`), the metadata
                        // (slice length / vtable ptr) lives in fat_locals and
                        // must be passed as the second register argument.
                        let meta = if !place.projection.is_empty()
                            && matches!(place.projection[0], mir::PlaceElem::Deref)
                        {
                            self.fat_locals.get(place.local)
                        } else {
                            None
                        };
                        (addr, meta)
                    };

                    if let Some(ptr) = drop_ptr {
                        let mut args = vec![ptr.into()];
                        if let Some(meta) = drop_meta {
                            args.push(meta.into());
                        }
                        let (call_mem, _) = self.builder.call(
                            callee.into(),
                            args,
                            Type::Unit,
                            self.current_mem.into(),
                            cleanup_label,
                            None,
                            Origin::synthetic(),
                        );
                        self.current_mem = call_mem.raw();
                    }
                }
            }
        }

        self.builder.br(
            target_block,
            vec![self.current_mem.into()],
            Origin::synthetic(),
        );
    }
}
