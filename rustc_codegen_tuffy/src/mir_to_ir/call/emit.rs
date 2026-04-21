use super::*;
use crate::mir_to_ir::ctx::OptionScalarLocal;
use crate::mir_to_ir::ctx::SplitPairLocal;

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    /// Emit a panic-bounds-check call with already-lowered integer values.
    fn emit_bounds_check_panic_values(
        &mut self,
        index: ValueRef,
        len: ValueRef,
        source_info: mir::SourceInfo,
    ) {
        let location = self.make_caller_location(source_info);
        let def_id = self
            .tcx
            .require_lang_item(rustc_hir::LangItem::PanicBoundsCheck, source_info.span);
        if let Some(instance) = Instance::try_resolve(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            def_id,
            ty::List::empty(),
        )
        .ok()
        .flatten()
        {
            let sym_name = self.tcx.symbol_name(instance).name.to_string();
            let sym_id = self.symbols.intern(&sym_name);
            let callee = self.builder.symbol_addr(sym_id, Origin::synthetic()).raw();
            let index = self.coerce_to_int(index);
            let len = self.coerce_to_int(len);
            let (call_mem, _) = self.builder.call(
                callee.into(),
                vec![index.into(), len.into(), location.into()],
                Type::Unit,
                self.current_mem.into(),
                None,
                None,
                Origin::synthetic(),
            );
            self.current_mem = call_mem.raw();
        }
        self.builder.trap(Origin::synthetic());
    }

    /// Return whether the resolved callee is one of the core slice split helpers.
    fn split_at_mut_kind(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) -> Option<bool> {
        if args.len() != 2 || !destination.projection.is_empty() {
            return None;
        }
        let Operand::Constant(c) = func else {
            return None;
        };
        let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(c.ty()),
        );
        let ty::FnDef(def_id, _) = fn_ty.kind() else {
            return None;
        };
        let unchecked = match self.tcx.opt_item_name(*def_id)?.as_str() {
            "split_at_mut" => false,
            "split_at_mut_unchecked" => true,
            _ => return None,
        };
        let arg0_ty = self.monomorphize(operand_ty_projected(&args[0].node, self.mir, self.tcx)?);
        let ty::Ref(_, inner, rustc_hir::Mutability::Mut) = arg0_ty.kind() else {
            return None;
        };
        if !matches!(inner.kind(), ty::Slice(_)) {
            return None;
        }
        let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
        let ty::Tuple(fields) = dest_ty.kind() else {
            return None;
        };
        if fields.len() != 2 || fields[0] != arg0_ty || fields[1] != arg0_ty {
            return None;
        }
        Some(unchecked)
    }

    /// Returns whether `local` is only consumed via `discriminant(_local)` and
    /// `((_local as Some).0)` payload reads.
    pub(in crate::mir_to_ir) fn local_only_used_as_option_discriminant_and_payload(
        &self,
        local: mir::Local,
    ) -> bool {
        let mut saw_discriminant = false;
        let mut saw_payload = false;

        let payload_projection = |place: &Place<'tcx>| {
            place.local == local
                && place.projection.len() == 2
                && matches!(
                    place.projection[0],
                    rustc_middle::mir::PlaceElem::Downcast(_, _)
                )
                && matches!(place.projection[1], rustc_middle::mir::PlaceElem::Field(idx, _) if idx.as_usize() == 0)
        };

        for bb_data in self.mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let mir::StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                    match rvalue {
                        mir::Rvalue::Discriminant(place)
                            if place.local == local && place.projection.is_empty() =>
                        {
                            saw_discriminant = true;
                        }
                        mir::Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                            if payload_projection(place) =>
                        {
                            saw_payload = true;
                        }
                        mir::Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                            if place.local == local =>
                        {
                            return false;
                        }
                        mir::Rvalue::UnaryOp(_, operand) | mir::Rvalue::Cast(_, operand, _)
                            if matches!(operand, Operand::Copy(place) | Operand::Move(place) if place.local == local) =>
                        {
                            return false;
                        }
                        mir::Rvalue::BinaryOp(_, box (lhs, rhs))
                            if matches!(lhs, Operand::Copy(place) | Operand::Move(place) if place.local == local)
                                || matches!(rhs, Operand::Copy(place) | Operand::Move(place) if place.local == local) =>
                        {
                            return false;
                        }
                        mir::Rvalue::Ref(_, _, place)
                        | mir::Rvalue::RawPtr(_, place)
                        | mir::Rvalue::CopyForDeref(place)
                            if place.local == local =>
                        {
                            return false;
                        }
                        mir::Rvalue::Aggregate(_, operands)
                            if operands.iter().any(|operand| {
                                matches!(operand, Operand::Copy(place) | Operand::Move(place) if place.local == local)
                            }) =>
                        {
                            return false;
                        }
                        _ => {}
                    }
                }
            }

            if let Some(terminator) = &bb_data.terminator {
                match &terminator.kind {
                    mir::TerminatorKind::SwitchInt {
                        discr: Operand::Copy(place) | Operand::Move(place),
                        ..
                    } if place.local == local => return false,
                    mir::TerminatorKind::Call { func, args, .. }
                        if matches!(func, Operand::Copy(place) | Operand::Move(place) if place.local == local)
                            || args.iter().any(|arg| {
                                matches!(&arg.node, Operand::Copy(place) | Operand::Move(place) if place.local == local)
                            }) =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
        }

        saw_discriminant || saw_payload
    }

    /// Try to lower `Range<usize>::next` directly into SSA state.
    fn try_handle_range_usize_next_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: BasicBlock,
    ) -> bool {
        // This fast path keeps the destination `Option<usize>` entirely in
        // `option_scalar_locals`. It is only sound while the local never has
        // to exist as an addressable enum value, so stack-backed destinations
        // and arbitrary consumers are rejected up front.
        if args.len() != 1
            || !destination.projection.is_empty()
            || self.stack_locals.is_stack(destination.local)
            || !self.local_only_used_as_option_discriminant_and_payload(destination.local)
        {
            return false;
        }
        let Operand::Constant(c) = func else {
            return false;
        };
        let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
            self.instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(c.ty()),
        );
        let ty::FnDef(def_id, _) = fn_ty.kind() else {
            return false;
        };
        if self
            .tcx
            .opt_item_name(*def_id)
            .is_none_or(|name| name.as_str() != "next")
        {
            return false;
        }

        let Some(arg_ty) = operand_ty_projected(&args[0].node, self.mir, self.tcx) else {
            return false;
        };
        let arg_ty = self.monomorphize(arg_ty);
        let ty::Ref(_, range_ty, rustc_hir::Mutability::Mut) = arg_ty.kind() else {
            return false;
        };
        let ty::Adt(range_def, range_args) = range_ty.kind() else {
            return false;
        };
        if self
            .tcx
            .opt_item_name(range_def.did())
            .is_none_or(|name| name.as_str() != "Range")
            || range_args.types().next().is_none_or(|ty| !ty.is_usize())
        {
            return false;
        }

        let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
        let Some((payload_ty, payload_variant, empty_variant)) =
            self.simple_option_scalar_info(dest_ty)
        else {
            return false;
        };
        if !payload_ty.is_usize() {
            return false;
        }
        let Some(some_discr) = self.enum_variant_discriminant(dest_ty, payload_variant) else {
            return false;
        };
        let Some(none_discr) = self.enum_variant_discriminant(dest_ty, empty_variant) else {
            return false;
        };

        let Some(range_ptr) = self.translate_operand(&args[0].node) else {
            return false;
        };
        let range_ptr = self.coerce_to_ptr(range_ptr);
        let start = self.builder.load(
            range_ptr.into(),
            8,
            Type::Int,
            self.current_mem.into(),
            int_annotation_for_bytes(8),
            Origin::synthetic(),
        );
        let end_off = field_offset(self.tcx, *range_ty, 1).unwrap_or(8);
        let end_ptr = if end_off == 0 {
            range_ptr
        } else {
            let off = self.builder.iconst(
                end_off as i64,
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            self.builder
                .ptradd(range_ptr.into(), off.into(), 0, Origin::synthetic())
                .raw()
        };
        let end = self.builder.load(
            end_ptr.into(),
            8,
            Type::Int,
            self.current_mem.into(),
            int_annotation_for_bytes(8),
            Origin::synthetic(),
        );
        let has_value = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Lt,
            start.into(),
            end.into(),
            Origin::synthetic(),
        );
        let target_block = self.block_map.get(target);
        let some_block = self.builder.create_block();
        let some_mem = self.builder.add_block_arg(some_block, Type::Mem, None);
        let none_block = self.builder.create_block();
        let none_mem = self.builder.add_block_arg(none_block, Type::Mem, None);
        self.builder.brif(
            has_value.into(),
            some_block,
            vec![self.current_mem.into()],
            none_block,
            vec![self.current_mem.into()],
            Origin::synthetic(),
        );

        self.builder.switch_to_block(some_block);
        self.current_mem = some_mem;
        let one = self
            .builder
            .iconst(1, 64, IntSignedness::Unsigned, Origin::synthetic());
        let next_start = self.builder.add(
            start.into(),
            one.into(),
            IntAnnotation {
                bit_width: 64,
                signedness: IntSignedness::Unsigned,
            },
            Origin::synthetic(),
        );
        self.current_mem = self
            .builder
            .store(
                next_start.into(),
                range_ptr.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            )
            .raw();
        let some =
            self.builder
                .iconst(some_discr, 64, IntSignedness::Unsigned, Origin::synthetic());
        self.option_scalar_locals.set(
            destination.local,
            OptionScalarLocal {
                discriminant: some.raw(),
                payload_variant,
                payload: start,
            },
        );
        self.builder.br(
            target_block,
            vec![self.current_mem.into()],
            Origin::synthetic(),
        );

        self.builder.switch_to_block(none_block);
        self.current_mem = none_mem;
        let none =
            self.builder
                .iconst(none_discr, 64, IntSignedness::Unsigned, Origin::synthetic());
        let zero = self
            .builder
            .iconst(0, 64, IntSignedness::Unsigned, Origin::synthetic())
            .raw();
        self.option_scalar_locals.set(
            destination.local,
            OptionScalarLocal {
                discriminant: none.raw(),
                payload_variant,
                payload: zero,
            },
        );
        self.builder.br(
            target_block,
            vec![self.current_mem.into()],
            Origin::synthetic(),
        );
        true
    }

    /// Try to lower `core::slice::split_at_mut{,_unchecked}` directly.
    fn try_handle_split_at_mut_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: BasicBlock,
        source_info: mir::SourceInfo,
    ) -> bool {
        let Some(unchecked) = self.split_at_mut_kind(func, args, destination) else {
            return false;
        };

        let Some(raw_slice) = self.translate_operand(&args[0].node) else {
            return false;
        };
        let data_ptr = self.load_fat_data_for_operand(&args[0].node, raw_slice);
        let Some(len_value) = self.find_fat_metadata_for_operand(&args[0].node) else {
            return false;
        };
        let Some(mid_value) = self.translate_operand(&args[1].node) else {
            return false;
        };
        let mid_value = self.coerce_to_int(mid_value);
        let len_value = self.coerce_to_int(len_value);

        let arg0_ty = self.monomorphize(
            operand_ty_projected(&args[0].node, self.mir, self.tcx)
                .expect("split_at_mut arg should have a type"),
        );
        let elem_ty = match arg0_ty.kind() {
            ty::Ref(_, inner, _) => match inner.kind() {
                ty::Slice(elem) => *elem,
                _ => return false,
            },
            _ => return false,
        };
        let elem_size = type_size(self.tcx, elem_ty).unwrap_or(1);
        let offset = if elem_size == 1 {
            mid_value
        } else {
            let size_const = self.builder.iconst(
                elem_size as i64,
                64,
                IntSignedness::Unsigned,
                Origin::synthetic(),
            );
            self.builder
                .mul(
                    mid_value.into(),
                    size_const.into(),
                    IntAnnotation {
                        bit_width: 64,
                        signedness: IntSignedness::Unsigned,
                    },
                    Origin::synthetic(),
                )
                .raw()
        };
        let right_ptr = self
            .builder
            .ptradd(data_ptr.into(), offset.into(), 0, Origin::synthetic())
            .raw();
        let right_len = self
            .builder
            .sub(
                len_value.into(),
                mid_value.into(),
                IntAnnotation {
                    bit_width: 64,
                    signedness: IntSignedness::Unsigned,
                },
                Origin::synthetic(),
            )
            .raw();

        let target_block = self.block_map.get(target);
        let store_result = |this: &mut Self, mem: ValueRef| {
            this.current_mem = mem;
            if !this.stack_locals.is_stack(destination.local) {
                this.locals.clear(destination.local);
                this.fat_locals.clear(destination.local);
                // Keep the tuple destructured in SSA until some later use
                // requires an actual tuple address. Place translation consults
                // `split_pair_locals` to answer `.0` / `.1` projections
                // without materializing the four-word aggregate in memory.
                this.split_pair_locals.set(
                    destination.local,
                    SplitPairLocal {
                        left_ptr: data_ptr,
                        left_len: mid_value,
                        right_ptr,
                        right_len,
                    },
                );
            } else {
                // Stack-backed destinations must hold the concrete tuple
                // layout because later field projections and references load
                // from slot offsets rather than consulting the split-pair
                // cache.
                let dest_ty = this.monomorphize(this.mir.local_decls[destination.local].ty);
                let dest_size = type_size(this.tcx, dest_ty).unwrap_or(32) as u32;
                let dest_align = type_align(this.tcx, dest_ty).unwrap_or(8) as u32;
                let dest_slot = match this.locals.get(destination.local) {
                    Some(existing)
                        if matches!(this.builder.value_type(existing), Some(Type::Ptr(_))) =>
                    {
                        existing
                    }
                    _ => {
                        let slot =
                            this.builder
                                .stack_slot(dest_size, dest_align, Origin::synthetic());
                        this.locals.set(destination.local, slot);
                        this.stack_locals.mark(destination.local);
                        slot
                    }
                };
                this.current_mem = this
                    .builder
                    .store(
                        data_ptr.into(),
                        dest_slot.into(),
                        8,
                        this.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                let off8 = this
                    .builder
                    .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                let left_len_addr = this
                    .builder
                    .ptradd(dest_slot.into(), off8.into(), 0, Origin::synthetic())
                    .raw();
                this.current_mem = this
                    .builder
                    .store(
                        mid_value.into(),
                        left_len_addr.into(),
                        8,
                        this.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                let off16 =
                    this.builder
                        .iconst(16, 64, IntSignedness::DontCare, Origin::synthetic());
                let right_ptr_addr = this
                    .builder
                    .ptradd(dest_slot.into(), off16.into(), 0, Origin::synthetic())
                    .raw();
                this.current_mem = this
                    .builder
                    .store(
                        right_ptr.into(),
                        right_ptr_addr.into(),
                        8,
                        this.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                let off24 =
                    this.builder
                        .iconst(24, 64, IntSignedness::DontCare, Origin::synthetic());
                let right_len_addr = this
                    .builder
                    .ptradd(dest_slot.into(), off24.into(), 0, Origin::synthetic())
                    .raw();
                this.current_mem = this
                    .builder
                    .store(
                        right_len.into(),
                        right_len_addr.into(),
                        8,
                        this.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
            }
            this.builder.br(
                target_block,
                vec![this.current_mem.into()],
                Origin::synthetic(),
            );
        };

        if unchecked {
            store_result(self, self.current_mem);
            return true;
        }

        let ok = self.builder.icmp(
            tuffy_ir::instruction::ICmpOp::Le,
            mid_value.into(),
            len_value.into(),
            Origin::synthetic(),
        );
        let success_block = self.builder.create_block();
        let success_mem = self.builder.add_block_arg(success_block, Type::Mem, None);
        let panic_block = self.builder.create_block();
        let panic_mem = self.builder.add_block_arg(panic_block, Type::Mem, None);
        self.builder.brif(
            ok.into(),
            success_block,
            vec![self.current_mem.into()],
            panic_block,
            vec![self.current_mem.into()],
            Origin::synthetic(),
        );

        self.builder.switch_to_block(success_block);
        store_result(self, success_mem);

        self.builder.switch_to_block(panic_block);
        self.current_mem = panic_mem;
        self.emit_bounds_check_panic_values(mid_value, len_value, source_info);
        true
    }

    /// Lowers one MIR call terminator into IR control flow and call instructions.
    pub(in crate::mir_to_ir) fn translate_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        cleanup_bb: Option<BasicBlock>,
        source_info: mir::SourceInfo,
    ) {
        // Check for compiler intrinsics and handle them inline.
        if let Some((intrinsic_name, intrinsic_substs)) = self.detect_intrinsic(func)
            && self.try_handle_intrinsic_call(
                func,
                args,
                destination,
                target,
                &intrinsic_name,
                intrinsic_substs,
            )
        {
            return;
        }

        // Skip precondition_check calls — these are debug-mode
        // assertions for unchecked operations that may not have MonoItems.
        // Note: drop_in_place calls are NOT skipped — they must be emitted
        // for assume_init_drop, ptr::drop_in_place, etc. to work correctly.
        // The Drop terminator handler only covers implicit drops at end of scope.
        if let Operand::Constant(c) = func {
            let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                self.instance.args,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(c.ty()),
            );
            if let ty::FnDef(def_id, _fn_args) = fn_ty.kind() {
                let skip = self
                    .tcx
                    .opt_item_name(*def_id)
                    .is_some_and(|n| n.as_str() == "precondition_check");
                if skip {
                    if let Some(target) = target {
                        let target_block = self.block_map.get(*target);
                        self.builder.br(
                            target_block,
                            vec![self.current_mem.into()],
                            Origin::synthetic(),
                        );
                    }
                    return;
                }
            }
        }

        // Resolve callee from the function operand's type.
        let resolved = resolve_call_target(self.tcx, func, self.instance, self.mir);
        let callee_target = resolved.target;
        let needs_caller_location = resolved.requires_caller_location;
        let needs_self_deref = resolved.needs_self_deref;
        let needs_tuple_spread = resolved.needs_tuple_spread;
        if cleanup_bb.is_none()
            && let Some(target_bb) = *target
            && self.try_handle_split_at_mut_call(func, args, destination, target_bb, source_info)
        {
            return;
        }
        if cleanup_bb.is_none()
            && let Some(target_bb) = *target
            && self.try_handle_range_usize_next_call(func, args, destination, target_bb)
        {
            return;
        }
        if destination.projection.is_empty() {
            self.split_pair_locals.clear(destination.local);
            self.option_scalar_locals.clear(destination.local);
        }
        if let Some(inst) = resolved.resolved_instance {
            self.referenced_instances.push(inst);
        }
        // Skip LLVM intrinsics (e.g. llvm.x86.sse2.pause from spin_loop).
        // These are target-specific hints with no semantic effect.
        if let Some(CallTarget::Direct(ref sym)) = callee_target
            && sym.starts_with("llvm.")
        {
            if let Some(target) = target {
                let target_block = self.block_map.get(*target);
                self.builder.br(
                    target_block,
                    vec![self.current_mem.into()],
                    Origin::synthetic(),
                );
            }
            return;
        }

        // For virtual dispatch, extract the vtable pointer from the first
        // argument (a fat pointer: data_ptr + vtable_ptr) and load the
        // function pointer from the vtable before processing arguments.
        let virtual_fn_ptr = if let Some(CallTarget::Virtual(idx)) = &callee_target {
            // The first argument is &dyn Trait — a fat pointer.
            // Get the vtable pointer from fat_locals.
            let self_arg = &args[0].node;
            let vtable_ptr = match self_arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    // For stack locals, always reload metadata from the slot.
                    // Cached fat_locals values are not block-sensitive, so a
                    // branch-assigned fat pointer local can otherwise pick up
                    // the vtable from a different control-flow path.
                    if self.stack_locals.is_stack(place.local) && place.projection.is_empty() {
                        // The fat pointer lives in a stack slot. The vtable
                        // pointer is the second word (offset 8).
                        if let Some(base) = self.locals.get(place.local) {
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let vtable_addr = self.builder.ptradd(
                                base.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let vtable = self.builder.load(
                                vtable_addr.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            Some(vtable)
                        } else {
                            None
                        }
                    } else if let Some(v) = self.fat_locals.get(place.local) {
                        Some(v)
                    } else {
                        // Projected place (e.g. (*_1).buf) — compute the
                        // address of the fat pointer field and load the
                        // vtable from offset 8.
                        if let Some((addr, _)) = self.translate_place_to_addr(place) {
                            let addr = self.coerce_to_ptr(addr);
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let vtable_addr = self.builder.ptradd(
                                addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let vtable = self.builder.load(
                                vtable_addr.into(),
                                8,
                                Type::Ptr(0),
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            Some(vtable)
                        } else {
                            None
                        }
                    }
                }
                _ => None,
            };
            if let Some(vtable) = vtable_ptr {
                // Coerce to Ptr in case fat_locals stored it as Int.
                let vtable = self.coerce_to_ptr(vtable);
                // vtable layout: [drop_in_place, size, align, method0, method1, ...]
                // rustc's InstanceKind::Virtual idx already includes the 3
                // metadata entries, so the byte offset is simply idx * 8.
                let offset = idx * 8;
                let off_val = self.builder.iconst(
                    offset as i64,
                    64,
                    IntSignedness::DontCare,
                    Origin::synthetic(),
                );
                let fn_addr =
                    self.builder
                        .ptradd(vtable.into(), off_val.into(), 0, Origin::synthetic());
                let fn_ptr = self.builder.load(
                    fn_addr.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    int_annotation_for_bytes(8),
                    Origin::synthetic(),
                );
                Some(fn_ptr)
            } else {
                None
            }
        } else {
            None
        };
        let is_virtual = virtual_fn_ptr.is_some();

        // Use destination type for semantic return handling.
        // Target-specific ABI lowering happens later in codegen/backend.
        let dest_ty = if destination.projection.is_empty() {
            self.monomorphize(self.mir.local_decls[destination.local].ty)
        } else {
            self.monomorphize(destination.ty(&self.mir.local_decls, self.tcx).ty)
        };
        let dest_size = type_size(self.tcx, dest_ty);
        let dest_repr = repr_kind(self.tcx, dest_ty);
        let part_bytes = self.target_part_bytes();
        let direct_abi_bytes = self.target_direct_abi_bytes();

        // Values that fit in the target's direct integer-register ABI path
        // stay in registers; larger ones use SRET.
        let needs_sret = match dest_repr {
            ReprKind::Zst => false,
            ReprKind::Scalar => false,
            ReprKind::ScalarPair => dest_size.is_some_and(|sz| sz > direct_abi_bytes),
            ReprKind::Memory => dest_size.is_some_and(|sz| sz > part_bytes),
        };
        let sret_slot = if needs_sret {
            // Always use the destination local's own stack slot (or a fresh
            // one) as the call's sret buffer.  Do NOT pass self.sret_ptr
            // directly: MIR blocks are translated in numeric order, so the
            // return block (which copies from _0's local slot to sret) may
            // have been translated before this call site, using the original
            // local slot.  Passing sret_ptr here would write to sret but
            // leave the local slot uninitialised — the return memcopy then
            // overwrites sret with garbage.
            if destination.projection.is_empty()
                && self.stack_locals.is_stack(destination.local)
                && let Some(existing) = self.locals.get(destination.local)
            {
                // The destination local already has a pre-allocated stack slot
                // (from the pre-scan phase in mod.rs). Reuse it so that any
                // code in other basic blocks that was already translated with
                // this slot as the local's address reads the correct result.
                // MIR blocks are translated in numeric order, not control-flow
                // order, so use-blocks may be translated before the call site.
                Some(existing)
            } else {
                let sz = dest_size.unwrap() as u32;
                Some(self.builder.stack_slot(sz, 0, Origin::synthetic()))
            }
        } else {
            None
        };

        // When the destination has projections (e.g. `_5.fld0 = fn1()`),
        // pre-compute the projected address before translating arguments
        // (which may modify locals).  We also save the original local value
        // so we can restore it after storing the call result.
        let has_call_dest_proj = !destination.projection.is_empty();
        // For Deref-based projections the base pointer must not change.
        // For Field/Index projections on a non-stack local we persist the
        // spill so that subsequent reads see the mutated slot.
        let call_dest_is_deref = has_call_dest_proj
            && matches!(destination.projection.first(), Some(mir::PlaceElem::Deref));
        let (call_proj_addr, call_proj_size, call_spilled_local) = if has_call_dest_proj {
            // Ensure the local has a stack slot before computing the projected
            // address — same rationale as the intrinsic path above.
            if self.locals.get(destination.local).is_none() && !call_dest_is_deref {
                let dest_ty = self.monomorphize(self.mir.local_decls[destination.local].ty);
                let size = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
                let slot = self.builder.stack_slot(size, 0, Origin::synthetic());
                self.locals.set(destination.local, slot);
            }
            let info = if call_dest_is_deref {
                self.translate_place_to_addr(destination)
            } else {
                self.translate_place_to_addr_inner(destination, true)
            }
            .map(|(a, ty)| {
                let a = self.coerce_to_ptr(a);
                let sz = type_size(self.tcx, ty).unwrap_or(8) as u32;
                (a, sz)
            });
            // Capture the (possibly newly spilled) local AFTER translate_place_to_addr_inner.
            let spilled = self.locals.get(destination.local);
            match info {
                Some((a, sz)) => (Some(a), sz, spilled),
                None => (None, 0, spilled),
            }
        } else {
            (None, 0, None)
        };

        // Translate arguments to IR operands using semantic values.
        let mut ir_args: Vec<tuffy_ir::instruction::Operand> = Vec::new();

        // Detect whether this call uses C ABI (extern "C").  For C ABI,
        // struct params > 32 bytes (SysV MEMORY class) must be placed on the
        // caller's stack frame (byval) instead of passed by pointer in a GPR.
        let is_c_abi_call = {
            let func_ty = match func {
                Operand::Constant(c) => {
                    let ty = self.tcx.instantiate_and_normalize_erasing_regions(
                        self.instance.args,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(c.ty()),
                    );
                    Some(ty)
                }
                Operand::Copy(place) | Operand::Move(place) => {
                    let ty = self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty);
                    Some(ty)
                }
                _ => None,
            };
            func_ty.is_some_and(|ty| {
                let sig = match ty.kind() {
                    ty::FnDef(def_id, args) => {
                        Some(self.tcx.fn_sig(*def_id).instantiate(self.tcx, args))
                    }
                    ty::FnPtr(sig_tys, hdr) => Some(sig_tys.with(*hdr)),
                    _ => None,
                };
                sig.is_some_and(|s| !s.skip_binder().abi.is_rustic_abi())
            })
        };

        // For SRET, pass the return slot address as the first argument.
        if let Some(slot) = sret_slot {
            ir_args.push(slot.into());
        }

        // Track how many ir_args were pushed before the argument loop
        // (i.e. just the SRET slot, if any) so the virtual dispatch
        // vtable-skip heuristic accounts for it.
        let pre_args_count = ir_args.len();

        for arg in args {
            // Skip zero-sized (Unit) and untranslatable args — they don't
            // occupy a runtime slot. But don't skip structs with non-zero size.
            let arg_ty = operand_ty_projected(&arg.node, self.mir, self.tcx)
                .map(|ty| self.monomorphize(ty))
                .unwrap_or_else(|| {
                    self.monomorphize(self.mir.local_decls[mir::Local::from_usize(0)].ty)
                });
            let arg_size = type_size(self.tcx, arg_ty).unwrap_or(0);
            if matches!(translate_ty(self.tcx, arg_ty), Some(Type::Unit)) {
                continue;
            }
            // Skip zero-sized ADTs (e.g. Global allocator) — they
            // don't occupy a runtime slot.
            if arg_size == 0 {
                continue;
            }

            // Tuple spreading for closure calls through Fn/FnMut/FnOnce:
            // the caller passes args as a single tuple but the closure
            // body expects individual parameters.  Spread all tuples
            // with at least 1 non-ZST field — even 1-tuples need
            // spreading when the tuple lives on the stack (otherwise the
            // stack address would be passed instead of the loaded value).
            //
            // Handle both place operands (Copy/Move) and constant operands.
            let tuple_base = if needs_tuple_spread
                && let ty::Tuple(fields) = arg_ty.kind()
                && fields
                    .iter()
                    .filter(|f| type_size(self.tcx, *f).unwrap_or(0) > 0)
                    .count()
                    >= 1
            {
                match &arg.node {
                    Operand::Copy(place) | Operand::Move(place) => {
                        self.locals.get(place.local).filter(|base| {
                            matches!(self.builder.value_type(*base), Some(Type::Ptr(_)))
                        })
                    }
                    Operand::Constant(_) => {
                        // For constant tuples, translate_operand returns the address
                        self.translate_operand(&arg.node).filter(|val| {
                            matches!(self.builder.value_type(*val), Some(Type::Ptr(_)))
                        })
                    }
                    _ => None,
                }
            } else {
                None
            };

            if let Some(base) = tuple_base {
                let typing_env = ty::TypingEnv::fully_monomorphized();
                if let Ok(layout) = self.tcx.layout_of(typing_env.as_query_input(arg_ty))
                    && let ty::Tuple(fields) = arg_ty.kind()
                {
                    for i in 0..fields.len() {
                        let ft = fields[i];
                        let fsz = type_size(self.tcx, ft).unwrap_or(0);
                        if fsz == 0 {
                            continue;
                        }
                        let offset = layout.fields.offset(i).bytes();
                        let addr = if offset == 0 {
                            base
                        } else {
                            let off = self.builder.iconst(
                                offset as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            self.builder
                                .ptradd(base.into(), off.into(), 0, Origin::synthetic())
                                .raw()
                        };
                        if fsz <= part_bytes {
                            let fty = translate_ty(self.tcx, ft).unwrap_or(Type::Int);
                            let ann = if matches!(fty, Type::Int) {
                                translate_annotation(ft)
                                    .or_else(|| int_annotation_for_bytes(fsz as u32))
                            } else {
                                None
                            };
                            let val = self.builder.load(
                                addr.into(),
                                fsz as u32,
                                fty,
                                self.current_mem.into(),
                                ann,
                                Origin::synthetic(),
                            );
                            ir_args.push(val.into());
                        } else if fsz <= direct_abi_bytes {
                            let prk = repr_kind(self.tcx, ft);
                            if matches!(prk, ReprKind::ScalarPair | ReprKind::Scalar) {
                                // Decompose into the target's direct ABI parts.
                                let w0 = self.builder.load(
                                    addr.into(),
                                    part_bytes as u32,
                                    Type::Int,
                                    self.current_mem.into(),
                                    int_annotation_for_bytes(part_bytes as u32),
                                    Origin::synthetic(),
                                );
                                ir_args.push(w0.into());
                                let off8 = self.builder.iconst(
                                    part_bytes as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let a1 = self.builder.ptradd(
                                    addr.into(),
                                    off8.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                let w1 = self.builder.load(
                                    a1.into(),
                                    part_bytes as u32,
                                    Type::Int,
                                    self.current_mem.into(),
                                    int_annotation_for_bytes(part_bytes as u32),
                                    Origin::synthetic(),
                                );
                                ir_args.push(w1.into());
                            } else {
                                // Memory repr: pass pointer (callee
                                // expects indirect).
                                ir_args.push(addr.into());
                            }
                        } else {
                            // Larger fields are passed indirectly.
                            ir_args.push(addr.into());
                        }
                    }
                    continue;
                }
            }

            if let Some(mut v) = self.translate_operand(&arg.node) {
                let arg_size = type_size(self.tcx, arg_ty).unwrap_or(0);

                // For constant aggregates (tuples, structs, arrays) ≤8 bytes, translate_operand
                // returns a pointer to the constant data. Load the value so it's passed
                // by value in a register, not by reference.
                // Exception: scalar ADTs (e.g. DynMetadata which wraps a single pointer)
                // where translate_const already returns the scalar value directly via
                // symbol_addr — loading from it would dereference THROUGH the value.
                let is_scalar_adt = matches!(arg_ty.kind(), ty::Adt(..))
                    && matches!(repr_kind(self.tcx, arg_ty), ReprKind::Scalar);
                if matches!(&arg.node, Operand::Constant(_))
                    && matches!(arg_ty.kind(), ty::Tuple(_) | ty::Adt(..) | ty::Array(..))
                    && arg_size > 0
                    && arg_size <= part_bytes
                    && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                    && !is_scalar_adt
                {
                    v = self.builder.load(
                        v.into(),
                        arg_size as u32,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(arg_size as u32),
                        Origin::synthetic(),
                    );
                }

                // Decompose small aggregate arguments into the target's direct
                // integer-register ABI parts. Stack-allocated structs are
                // represented as Ptr values; load both parts so the callee
                // receives the direct-register ABI form.
                // Fat pointer values from constants (symbol_addr to
                // string data) or non-stack locals (the data pointer
                // itself) are NOT addresses of [ptr, len] pairs.
                // They must not be decomposed by word-by-word loads;
                // the fat component is pushed separately below.
                let is_fat_value_not_slot = is_fat_ptr(self.tcx, arg_ty)
                    && match &arg.node {
                        Operand::Constant(_) => true,
                        Operand::Copy(p) | Operand::Move(p) => {
                            p.projection.is_empty() && !self.stack_locals.is_stack(p.local)
                        }
                        _ => false,
                    };
                // For fat pointer args from stack locals, translate_operand
                // returns the data pointer (loaded from slot[0:8]), NOT
                // the slot address.  Using that for struct decomposition
                // would dereference THROUGH the data pointer.  Load both
                // components from the stack slot instead.
                // This also covers projected field accesses like (_1.0: &str)
                // where _1 is a stack-local tuple.
                let is_fat_stack_local = is_fat_ptr(self.tcx, arg_ty)
                    && match &arg.node {
                        Operand::Copy(p) | Operand::Move(p) => {
                            // Either a direct stack local or a field projection
                            // into a stack local — both cases store the fat ptr
                            // in the stack slot and translate_operand returns
                            // the loaded data pointer, not the slot address.
                            self.stack_locals.is_stack(p.local)
                        }
                        _ => false,
                    };
                let is_struct_arg = arg_size > part_bytes
                    && arg_size <= direct_abi_bytes
                    && matches!(repr_kind(self.tcx, arg_ty), ReprKind::ScalarPair)
                    && !is_fat_value_not_slot
                    && !is_fat_stack_local
                    && matches!(self.builder.value_type(v), Some(Type::Ptr(_)));
                let decomposed = if is_fat_stack_local
                    && arg_size > part_bytes
                    && arg_size <= direct_abi_bytes
                {
                    // Load both words from the stack slot (at the projected
                    // field offset if applicable).
                    // For virtual dispatch self args, only pass the data
                    // pointer (w0) — the vtable (w1) was already used to
                    // look up the function pointer and must not be forwarded.
                    let skip_vtable = is_virtual && ir_args.len() == pre_args_count;
                    let slot_base = match &arg.node {
                        Operand::Copy(p) | Operand::Move(p) => {
                            if p.projection.is_empty() {
                                self.locals.get(p.local)
                            } else {
                                // For projected fields (e.g. _1.0), compute
                                // the address of the fat pointer within the
                                // parent struct's stack slot.
                                self.translate_place_to_addr(p)
                                    .map(|(a, _)| self.coerce_to_ptr(a))
                            }
                        }
                        _ => None,
                    };
                    if let Some(slot_addr) = slot_base {
                        let w0 = self.builder.load(
                            slot_addr.into(),
                            part_bytes as u32,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(part_bytes as u32),
                            Origin::synthetic(),
                        );
                        ir_args.push(w0.into());
                        if !skip_vtable {
                            let off8 = self.builder.iconst(
                                part_bytes as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let hi_addr = self.builder.ptradd(
                                slot_addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let w1 = self.builder.load(
                                hi_addr.into(),
                                part_bytes as u32,
                                Type::Int,
                                self.current_mem.into(),
                                int_annotation_for_bytes(part_bytes as u32),
                                Origin::synthetic(),
                            );
                            ir_args.push(w1.into());
                        }
                        true
                    } else {
                        false
                    }
                } else if is_struct_arg {
                    let w0 = self.builder.load(
                        v.into(),
                        part_bytes as u32,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(part_bytes as u32),
                        Origin::synthetic(),
                    );
                    ir_args.push(w0.into());
                    let off8 = self.builder.iconst(
                        part_bytes as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let hi_addr =
                        self.builder
                            .ptradd(v.into(), off8.into(), 0, Origin::synthetic());
                    let w1 = self.builder.load(
                        hi_addr.into(),
                        part_bytes as u32,
                        Type::Int,
                        self.current_mem.into(),
                        int_annotation_for_bytes(part_bytes as u32),
                        Origin::synthetic(),
                    );
                    ir_args.push(w1.into());
                    true
                } else {
                    false
                };

                if !decomposed {
                    // Memory aggregate > 8 bytes: pass a pointer to a fresh copy.
                    // Passing the original slot directly would let the callee overwrite
                    // the caller's local (violating Rust pass-by-value semantics).
                    let is_memory_indirect = arg_size > part_bytes
                        && matches!(repr_kind(self.tcx, arg_ty), ReprKind::Memory)
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)));
                    if (arg_size > direct_abi_bytes || is_memory_indirect)
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                    {
                        let align = type_align(self.tcx, arg_ty).unwrap_or(1) as u32;
                        let tmp = self
                            .builder
                            .stack_slot(arg_size as u32, 0, Origin::synthetic());
                        let count = self.builder.iconst(
                            arg_size as i64,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let tmp_annotated = IrOperand::annotated(tmp, Annotation::Align(align));
                        let v_annotated = IrOperand::annotated(v, Annotation::Align(align));
                        let new_mem = self.builder.mem_copy(
                            tmp_annotated.into(),
                            v_annotated.into(),
                            count.into(),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        );
                        self.current_mem = new_mem.raw();
                        // For C ABI, structs > 32 bytes are MEMORY class:
                        // the callee expects the data ON THE STACK, not a
                        // pointer in a register.  Annotate with Byval so
                        // the ISel emits a stack copy.
                        if is_c_abi_call && arg_size > 32 {
                            ir_args.push(IrOperand::annotated(
                                tmp,
                                Annotation::Byval(arg_size as u32),
                            ));
                        } else {
                            ir_args.push(tmp.into());
                        }
                    } else if arg_size > 0
                        && arg_size <= part_bytes
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                        && self.builder.is_local_memory_address(v)
                        && translate_ty(self.tcx, arg_ty).is_none()
                        && !matches!(repr_kind(self.tcx, arg_ty), ReprKind::Scalar)
                    {
                        // Small aggregate (1-8 bytes) in a stack slot:
                        // load the value so it is passed by register.
                        // Only load when `v` is actually a stack slot /
                        // memory address — NOT when it is a loaded pointer
                        // value (e.g. NonNull<u8> transmuted from *mut u8).
                        // Exclude scalar ADTs (e.g. DynMetadata) where the
                        // symbol_addr IS the scalar value (a vtable pointer),
                        // not a reference to the data.
                        let loaded = self.builder.load(
                            v.into(),
                            arg_size as u32,
                            Type::Int,
                            self.current_mem.into(),
                            int_annotation_for_bytes(arg_size as u32),
                            Origin::synthetic(),
                        );
                        ir_args.push(loaded.into());
                    } else {
                        // Push value with type annotation so the legalizer
                        // can identify wide integer values.
                        if let Some(ann) = translate_annotation(arg_ty) {
                            ir_args.push(IrOperand::annotated(v, ann));
                        } else {
                            ir_args.push(v.into());
                        }
                    }
                    // If this arg is a Copy/Move of a checked-op local (e.g.
                    // (i64, bool) from AddWithOverflow), pack or append the
                    // overflow flag. Small tuples whose primary fits in half
                    // of one ABI part stay in a single register; larger tuples
                    // use the next direct ABI part or go indirect.
                    if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                        && place.projection.is_empty()
                        && !self.stack_locals.is_stack(place.local)
                        && let Some(overflow_flag) = self.overflow_locals.get(place.local)
                    {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        if let ty::Tuple(fields) = local_ty.kind()
                            && fields.len() == 2
                            && fields[1].is_bool()
                            && !fields[0].is_bool()
                        {
                            let primary_bytes =
                                type_size(self.tcx, fields[0]).unwrap_or(part_bytes);
                            if primary_bytes <= part_bytes / 2 {
                                // Pack overflow flag into the same register:
                                // value |= (flag_as_int << (primary_bytes * 8))
                                let shift_bits = (primary_bytes * 8) as i64;
                                let shift_val = self.builder.iconst(
                                    shift_bits,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let one = self.builder.iconst(
                                    1,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let zero = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let flag_int = self.builder.select(
                                    overflow_flag.into(),
                                    one.into(),
                                    zero.into(),
                                    Type::Int,
                                    Some(Annotation::Int(IntAnnotation {
                                        bit_width: 64,
                                        signedness: IntSignedness::DontCare,
                                    })),
                                    Origin::synthetic(),
                                );
                                let ann64 = IntAnnotation {
                                    bit_width: 64,
                                    signedness: IntSignedness::DontCare,
                                };
                                let shifted = self.builder.shl(
                                    flag_int.into(),
                                    shift_val.into(),
                                    ann64,
                                    Origin::synthetic(),
                                );
                                // Replace the last pushed arg with the packed value.
                                // Mask the primary value to its type width first
                                // to prevent sign-extended bits from bleeding into
                                // the overflow flag position.
                                if let Some(last) = ir_args.last_mut() {
                                    let last_op: tuffy_ir::typed::IntOperand =
                                        (*last).clone().into();
                                    let mask_val =
                                        (1u64 << (primary_bytes * 8)).wrapping_sub(1) as i64;
                                    let mask = self.builder.iconst(
                                        mask_val,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
                                    let masked = self.builder.and(
                                        last_op,
                                        mask.into(),
                                        ann64,
                                        Origin::synthetic(),
                                    );
                                    let packed = self.builder.or(
                                        masked.into(),
                                        shifted.into(),
                                        ann64,
                                        Origin::synthetic(),
                                    );
                                    *last = packed.into();
                                }
                            } else if primary_bytes > part_bytes {
                                // The primary spans more than one ABI part, so
                                // the full tuple is passed indirectly.
                                // Store primary + overflow flag into a stack slot and
                                // pass its address.
                                let full_size = type_size(self.tcx, local_ty).unwrap_or(32) as u32;
                                let slot =
                                    self.builder.stack_slot(full_size, 0, Origin::synthetic());
                                // Store the primary value (u128).
                                let prev_arg = ir_args.pop().unwrap();
                                self.current_mem = self
                                    .builder
                                    .store(
                                        prev_arg,
                                        slot.into(),
                                        primary_bytes as u32,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                // Store the overflow bool at offset primary_bytes.
                                let flag_off = self.builder.iconst(
                                    primary_bytes as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let flag_addr = self.builder.ptradd(
                                    slot.into(),
                                    flag_off.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                let one = self.builder.iconst(
                                    1,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let zero = self.builder.iconst(
                                    0,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let flag_int = self.builder.select(
                                    overflow_flag.into(),
                                    one.into(),
                                    zero.into(),
                                    Type::Int,
                                    Some(Annotation::Int(IntAnnotation {
                                        bit_width: 8,
                                        signedness: IntSignedness::Unsigned,
                                    })),
                                    Origin::synthetic(),
                                );
                                self.current_mem = self
                                    .builder
                                    .store(
                                        flag_int.into(),
                                        flag_addr.into(),
                                        1,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                                ir_args.push(slot.into());
                            } else {
                                // Large primary (8 bytes): separate register arg.
                                ir_args.push(overflow_flag.into());
                            }
                        }
                    }
                    // If this arg is a Copy/Move of a fat local, also pass the high part.
                    // Exception: for virtual dispatch, skip the vtable pointer on the
                    // first argument (self) — the actual method only takes the data ptr.
                    // Use pre_args_count to account for any SRET slot pushed before the loop.
                    let skip_fat = is_virtual && ir_args.len() == pre_args_count + 1;
                    if !skip_fat && let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                        let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                        if place.projection.is_empty() {
                            // Non-projected place: use fat_locals for the metadata.
                            if let Some(fat_v) = self.fat_locals.get(place.local) {
                                // Only push the fat component when the local's
                                // type is actually a fat pointer.  Aggregates
                                // (structs) with 2+ fields also set fat_locals
                                // but their second field is not ABI metadata.
                                let needs_fat = is_fat_ptr(self.tcx, local_ty)
                                    || (local_ty.is_box()
                                        && local_ty.boxed_ty().is_some_and(|bt| {
                                            matches!(
                                                bt.kind(),
                                                ty::Str | ty::Slice(..) | ty::Dynamic(..)
                                            )
                                        }));
                                if needs_fat {
                                    ir_args.push(fat_v.into());
                                }
                            }
                        } else {
                            // Projected place: the projected type may be a fat
                            // pointer even if the base local is a struct.  Load
                            // the metadata from the projected address + 8.
                            let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                            let projected_ty = self.monomorphize(projected_ty);
                            if is_fat_ptr(self.tcx, projected_ty)
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
                                let meta = self.builder.load(
                                    meta_addr.into(),
                                    8,
                                    Type::Int,
                                    self.current_mem.into(),
                                    int_annotation_for_bytes(8),
                                    Origin::synthetic(),
                                );
                                ir_args.push(meta.into());
                            }
                        }
                    }
                    // If this arg is a constant fat pointer, pass the length.
                    // Resolve Unevaluated constants first.
                    if let Operand::Constant(c) = &arg.node {
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
                            let len_val = self.builder.iconst(
                                meta as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            ir_args.push(len_val.into());
                        } else if let Some(mir::ConstValue::Indirect { alloc_id, offset }) =
                            resolved
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
                                let len_val = self.builder.iconst(
                                    len as i64,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                ir_args.push(len_val.into());
                            }
                        }
                    }
                }
            }
        }

        // ZST closure environments are not uniform at the Rust ABI level:
        // some monomorphized closure bodies still expect an explicit env
        // pointer, others do not. Compare the resolved callee's runtime ABI
        // arity to the arguments we just lowered and only inject the env
        // pointer when the body actually expects one extra runtime argument.
        if let Some(instance) = resolved.resolved_instance
            && self.tcx.is_closure_like(instance.def_id())
        {
            let runtime_parts_for_ty = |ty: ty::Ty<'tcx>| -> usize {
                let sz = type_size(self.tcx, ty).unwrap_or(0);
                let ir_ty = translate_ty(self.tcx, ty);
                if matches!(ir_ty, Some(Type::Unit)) || sz == 0 {
                    return 0;
                }
                if ir_ty.is_none() {
                    let repr = repr_kind(self.tcx, ty);
                    if matches!(repr, ReprKind::ScalarPair | ReprKind::Scalar)
                        && sz > part_bytes
                        && sz <= direct_abi_bytes
                    {
                        return 2;
                    }
                    return 1;
                }

                let mut parts = 1;
                if is_fat_ptr(self.tcx, ty) {
                    parts += 1;
                }
                parts
            };

            let callee_mir = self.tcx.instance_mir(instance.def);
            let expected_runtime_args = callee_mir
                .args_iter()
                .map(|local| {
                    self.tcx.instantiate_and_normalize_erasing_regions(
                        instance.args,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(callee_mir.local_decls[local].ty),
                    )
                })
                .map(runtime_parts_for_ty)
                .sum::<usize>();
            let provided_runtime_args = ir_args.len().saturating_sub(pre_args_count);

            if expected_runtime_args == provided_runtime_args + 1 {
                let closure_env = args
                    .first()
                    .and_then(|arg| {
                        operand_ty_projected(&arg.node, self.mir, self.tcx)
                            .map(|ty| self.monomorphize(ty))
                            .filter(|ty| {
                                matches!(ty.kind(), ty::Closure(..) | ty::CoroutineClosure(..))
                            })
                            .and(Some(&arg.node))
                    })
                    .unwrap_or(func);
                let align = operand_ty_projected(closure_env, self.mir, self.tcx)
                    .map(|ty| self.monomorphize(ty))
                    .and_then(|ty| type_align(self.tcx, ty))
                    .unwrap_or(1)
                    .max(1) as u32;
                let env = match closure_env {
                    Operand::Copy(place) | Operand::Move(place) => self
                        .translate_place_to_addr(place)
                        .map(|(addr, _)| self.coerce_to_ptr(addr)),
                    Operand::Constant(_) => self.translate_operand(closure_env).filter(|value| {
                        matches!(self.builder.value_type(*value), Some(Type::Ptr(_)))
                    }),
                    _ => None,
                }
                .unwrap_or_else(|| self.builder.stack_slot(1, align, Origin::synthetic()));
                ir_args.insert(pre_args_count, env.into());
            }
        }

        // When Instance::try_resolve resolved through a blanket impl that
        // strips a reference from Self, the first argument has an extra level
        // of indirection.  Dereference it so the callee receives the correct
        // pointer type (e.g. &mut Formatter instead of &&mut Formatter).
        // Only apply when the argument is a Ptr (stack slot address) — if
        // it's already an Int/scalar, the extra indirection doesn't exist.
        if needs_self_deref {
            let self_idx = 0;
            if self_idx < ir_args.len() {
                let arg_ty = self.builder.value_type(ir_args[self_idx].value);
                if matches!(arg_ty, Some(Type::Ptr(_))) {
                    let old_self = ir_args[self_idx].clone();
                    let derefed = self.builder.load(
                        old_self.into(),
                        8,
                        Type::Ptr(0),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                    ir_args[self_idx] = derefed.into();
                }
            }
        }

        // If the callee has #[track_caller], append an implicit &Location
        // as the last ABI argument.
        if needs_caller_location {
            let loc_ptr = self.make_caller_location(source_info);
            ir_args.push(loc_ptr.into());
        }

        // Emit a Call IR instruction.
        let callee_val = if let Some(fn_ptr) = virtual_fn_ptr {
            // Virtual dispatch: callee is a function pointer loaded from vtable.
            fn_ptr
        } else if let Some(CallTarget::Direct(ref sym)) = callee_target {
            let sym_id = self.symbols.intern(sym);
            self.builder.symbol_addr(sym_id, Origin::synthetic()).raw()
        } else if let Some(fn_ptr) = self.translate_operand(func) {
            // Indirect call through a function pointer in a local.
            fn_ptr
        } else {
            self.builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                .raw()
        };
        // Determine the IR return type for the call instruction.
        // Small aggregates that fit in the target's direct integer-register
        // return path use `Type::Int` so the call captures the register value.
        let call_ret_ty = translate_ty(self.tcx, dest_ty).unwrap_or_else(|| {
            if dest_size.is_some_and(|sz| sz > 0 && sz <= direct_abi_bytes) {
                Type::Int
            } else {
                Type::Unit
            }
        });
        let call_ret_ann = if matches!(call_ret_ty, Type::Int) {
            translate_annotation(dest_ty).or_else(|| {
                // For structs ≤8 bytes, use annotation based on size.
                // For scalar returns wider than one register, use an exact
                // double-width annotation so legalization can recover the
                // backend's low/high return convention.
                // For ScalarPair, use only the first scalar's byte width
                // as the call annotation — the remaining ABI part is
                // captured via metadata.
                dest_size.and_then(|sz| {
                    if matches!(dest_repr, ReprKind::ScalarPair) {
                        // ScalarPair: annotation covers only the primary ABI
                        // register part; the remaining direct ABI part arrives
                        // via backend metadata.
                        let first_sz = scalar_pair_info(self.tcx, dest_ty)
                            .map(|(a, _, _)| a as u32)
                            .unwrap_or(sz.min(part_bytes) as u32);
                        int_annotation_for_bytes(first_sz)
                    } else if sz <= part_bytes
                        || (sz <= direct_abi_bytes && matches!(dest_repr, ReprKind::Scalar))
                    {
                        int_annotation_for_bytes(sz as u32)
                    } else if sz <= direct_abi_bytes {
                        // Small memory aggregates capture only the primary ABI
                        // register part at the IR call result.
                        int_annotation_for_bytes(part_bytes as u32)
                    } else {
                        None
                    }
                })
            })
        } else {
            None
        };
        let cleanup_label = cleanup_bb.map(|bb| self.setup_cleanup_landing_pad(bb));
        let (call_mem, call_data) = self.builder.call(
            callee_val.into(),
            ir_args,
            call_ret_ty,
            self.current_mem.into(),
            cleanup_label,
            call_ret_ann,
            Origin::synthetic(),
        );
        self.current_mem = call_mem.raw();

        // For non-void calls, call_data is Some(data_vref).
        // For void calls, call_data is None — use a dummy zero.
        let call_vref = call_data.unwrap_or_else(|| {
            self.builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                .raw()
        });

        if has_call_dest_proj {
            // Destination has projections (e.g. `_5.fld0 = fn1()`).
            // Store the call result through the pre-computed projected address.
            // For non-Deref projections, also update the base local to point at
            // the newly spilled slot so subsequent reads see the mutation.
            if let Some(addr) = call_proj_addr
                && call_proj_size > 0
            {
                if let Some(sret) = sret_slot {
                    // SRET function: the callee wrote the value to `sret`.
                    // Copy it to the projected destination address.
                    let count = self.builder.iconst(
                        call_proj_size as i64,
                        64,
                        IntSignedness::DontCare,
                        Origin::synthetic(),
                    );
                    let addr_annotated = IrOperand::annotated(addr, Annotation::Align(1));
                    let sret_annotated = IrOperand::annotated(sret, Annotation::Align(1));
                    self.current_mem = self
                        .builder
                        .mem_copy(
                            addr_annotated.into(),
                            sret_annotated.into(),
                            count.into(),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                } else {
                    self.current_mem = self
                        .builder
                        .store(
                            call_vref.into(),
                            addr.into(),
                            call_proj_size,
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            }
            // For non-Deref projections restore local to spilled slot.
            if !call_dest_is_deref && let Some(slot) = call_spilled_local {
                self.locals.set(destination.local, slot);
                self.stack_locals.mark(destination.local);
            }
        } else if let Some(slot) = sret_slot {
            // Indirect return: the callee wrote the result to the
            // stack slot we passed as the first argument. Just record the
            // slot as the destination local.
            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
        } else if dest_size.unwrap_or(0) > part_bytes && matches!(dest_repr, ReprKind::Scalar) {
            // Wide scalar return (e.g. i128, transparent newtype over i128):
            // emit a single full-width store and let legalization split the
            // value into lo/hi halves with the correct RDX capture.
            let size = dest_size.unwrap();
            let slot = if let Some(existing) = self.locals.get(destination.local) {
                if self.stack_locals.is_stack(destination.local) {
                    existing
                } else {
                    self.builder.stack_slot(size as u32, 0, Origin::synthetic())
                }
            } else {
                self.builder.stack_slot(size as u32, 0, Origin::synthetic())
            };
            self.current_mem = self
                .builder
                .store(
                    call_vref.into(),
                    slot.into(),
                    size as u32,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();
            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
        } else if matches!(dest_repr, ReprKind::ScalarPair) {
            // Direct-register aggregate return (ScalarPair): the primary ABI
            // part is returned in the normal call result and the secondary
            // part is read explicitly via `call_ret2`.
            let size = dest_size.unwrap();
            let (a_size, b_size, b_offset) = scalar_pair_info(self.tcx, dest_ty).unwrap_or((
                size.min(part_bytes),
                size.saturating_sub(part_bytes),
                part_bytes,
            ));
            let slot = if let Some(existing) = self.locals.get(destination.local) {
                if self.stack_locals.is_stack(destination.local) {
                    existing
                } else {
                    self.builder.stack_slot(size as u32, 0, Origin::synthetic())
                }
            } else {
                self.builder.stack_slot(size as u32, 0, Origin::synthetic())
            };
            // Store the primary ABI part at offset 0.
            self.current_mem = self
                .builder
                .store(
                    call_vref.into(),
                    slot.into(),
                    a_size as u32,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();
            let ret2 = self.builder.call_ret2(
                call_mem.into(),
                Type::Int,
                int_annotation_for_bytes(b_size as u32),
                Origin::synthetic(),
            );
            // Store the secondary ABI part at the correct offset.
            let off_val = self.builder.iconst(
                b_offset as i64,
                64,
                IntSignedness::DontCare,
                Origin::synthetic(),
            );
            let hi_addr = self
                .builder
                .ptradd(slot.into(), off_val.into(), 0, Origin::synthetic());
            self.current_mem = self
                .builder
                .store(
                    ret2.into(),
                    hi_addr.into(),
                    b_size as u32,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();

            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
        } else {
            // Scalar return (≤ 8 bytes).
            //
            // MIR optimization may merge a value return with a subsequent
            // Ref, giving the destination local a reference type (`&T`)
            // even though the callee returns `T` by value.  Detect this
            // mismatch and spill the return value to a stack slot so the
            // local holds a valid pointer.
            let dest_is_thin_ref = matches!(
                dest_ty.kind(),
                ty::Ref(_, inner, _) if !matches!(inner.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
            );
            let callee_returns_value = {
                // Resolve the callee's actual return type from its signature.
                let mut ret_is_value = false;
                if let Operand::Constant(c) = func {
                    let fn_ty = self.monomorphize(c.ty());
                    if let ty::FnDef(def_id, fn_args) = fn_ty.kind() {
                        let sig = self.tcx.fn_sig(*def_id).instantiate(self.tcx, fn_args);
                        let sig = self.tcx.normalize_erasing_late_bound_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            sig,
                        );
                        let ret_ty = sig.output();
                        ret_is_value = !matches!(ret_ty.kind(), ty::Ref(..) | ty::RawPtr(..));
                    }
                }
                ret_is_value
            };

            if dest_is_thin_ref && callee_returns_value {
                // Callee returns T by value but destination expects &T.
                // Spill the return value to a stack slot.
                let inner_ty = match dest_ty.kind() {
                    ty::Ref(_, inner, _) => *inner,
                    _ => unreachable!(),
                };
                let size = type_size(self.tcx, inner_ty).unwrap_or(8) as u32;
                let slot = self.builder.stack_slot(size.max(1), 0, Origin::synthetic());
                self.current_mem = self
                    .builder
                    .store(
                        call_vref.into(),
                        slot.into(),
                        size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    )
                    .raw();
                self.locals.set(destination.local, slot);
            } else if self.stack_locals.is_stack(destination.local) {
                // Destination was pre-promoted to a stack local (e.g. because
                // its address is taken later via `&`).  Store the scalar
                // return value into the existing slot instead of overwriting
                // the slot pointer with the raw value.
                if let Some(slot) = self.locals.get(destination.local) {
                    let size = dest_size.unwrap_or(8) as u32;
                    self.current_mem = self
                        .builder
                        .store(
                            call_vref.into(),
                            slot.into(),
                            size.max(1),
                            self.current_mem.into(),
                            Origin::synthetic(),
                        )
                        .raw();
                }
            } else {
                self.locals.set(destination.local, call_vref);
            }
        }

        // Branch to the continuation block if present.
        if let Some(target_bb) = target {
            let target_block = self.block_map.get(*target_bb);
            self.builder.br(
                target_block,
                vec![self.current_mem.into()],
                Origin::synthetic(),
            );
        }
    }
}
