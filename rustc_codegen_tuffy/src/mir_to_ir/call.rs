//! Call translation for MIR → IR conversion.

use rustc_middle::mir::{self, BasicBlock, Operand, Place};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};
use rustc_span::source_map::Spanned;

use tuffy_ir::instruction::Origin;
use tuffy_ir::types::Type;
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::intrinsic::{
    detect_intrinsic, intrinsic_to_libc, translate_intrinsic, translate_memory_intrinsic,
};
use super::types::*;

/// Resolved call target: direct symbol or virtual dispatch.
pub(super) enum CallTarget {
    /// Direct call to a named symbol.
    Direct(String),
    /// Virtual dispatch: load function pointer from vtable at given index.
    Virtual(usize),
}

/// Result of resolving a call target, including caller-location metadata.
pub(super) struct ResolvedCall<'tcx> {
    pub(super) target: Option<CallTarget>,
    /// True if the callee has `#[track_caller]` and expects an implicit
    /// `&Location` as the last ABI argument.
    pub(super) requires_caller_location: bool,
    /// True when `Instance::try_resolve` resolved through a blanket impl
    /// that strips a reference level from Self (e.g. `<&mut Formatter as
    /// Write>::write_fmt` → `<Formatter as Write>::write_fmt`).  The MIR
    /// passes `&mut &mut Formatter` but the resolved callee expects
    /// `&mut Formatter`, so the first argument needs a dereference.
    pub(super) needs_self_deref: bool,
    /// The resolved Instance, if available. Used to compile `#[inline]`
    /// functions not collected as mono items.
    pub(super) resolved_instance: Option<Instance<'tcx>>,
    /// True when the call goes through Fn::call / FnMut::call_mut /
    /// FnOnce::call_once and resolves to a closure body.  The caller
    /// passes args as a single tuple but the closure body expects
    /// individual parameters — the tuple must be spread at the call site.
    pub(super) needs_tuple_spread: bool,
}

/// Resolve the callee symbol name from a Call terminator's function operand.
pub(super) fn resolve_call_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_op: &Operand<'tcx>,
    caller: Instance<'tcx>,
    mir: &mir::Body<'tcx>,
) -> ResolvedCall<'tcx> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        Operand::Copy(place) | Operand::Move(place) => {
            // Use the projected type so that Deref projections (e.g.
            // `move (*_self)` in call_mut shims where _self: &mut FnDef)
            // resolve to the underlying FnDef type, not &mut FnDef.
            place.ty(&mir.local_decls, tcx).ty
        }
        _ => {
            return ResolvedCall {
                target: None,
                requires_caller_location: false,
                needs_self_deref: false,
                resolved_instance: None,
                needs_tuple_spread: false,
            };
        }
    };
    // Monomorphize the callee type using the caller's substitutions.
    // This resolves generic parameters (F/#0, Self/#0, etc.) that appear
    // when the caller is a generic function monomorphized for specific types.
    let ty = tcx.instantiate_and_normalize_erasing_regions(
        caller.args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(ty),
    );
    match ty.kind() {
        ty::FnDef(def_id, args) => {
            // Check if this is an intrinsic that maps to a libc symbol.
            if let Some(intrinsic) = tcx.intrinsic(*def_id) {
                let iname = intrinsic.name.as_str();
                if let Some(libc_sym) = intrinsic_to_libc(iname) {
                    return ResolvedCall {
                        target: Some(CallTarget::Direct(libc_sym.to_string())),
                        requires_caller_location: false,
                        needs_self_deref: false,
                        resolved_instance: None,
                        needs_tuple_spread: false,
                    };
                }
            }
            if args.has_non_region_param() {
                return ResolvedCall {
                    target: None,
                    requires_caller_location: false,
                    needs_self_deref: false,
                    resolved_instance: None,
                    needs_tuple_spread: false,
                };
            }
            let instance =
                Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), *def_id, args)
                    .ok()
                    .flatten();
            let instance = match instance {
                Some(i) => i,
                None => {
                    return ResolvedCall {
                        target: None,
                        requires_caller_location: false,
                        needs_self_deref: false,
                        resolved_instance: None,
                        needs_tuple_spread: false,
                    };
                }
            };
            // Detect blanket-impl resolution that strips a reference from
            // Self.  For example, `<&mut Formatter as Write>::write_fmt`
            // with args=[&mut Formatter] resolves to
            // `<Formatter as Write>::write_fmt`.  The MIR passes
            // `&mut &mut Formatter` but the compiled callee expects
            // `&mut Formatter`, so we must dereference the first argument.
            //
            // There are two cases:
            //
            // Case A: Resolution went THROUGH the blanket impl to the
            // direct impl (e.g. `write_fmt` which the blanket impl
            // doesn't override).  The resolved impl's raw Self is
            // non-reference.  We just need needs_self_deref.
            //
            // Case B: Resolution went TO the blanket impl itself (e.g.
            // `write_str` which the blanket impl DOES override).  The
            // resolved impl's raw Self IS a reference.  The blanket
            // impl's method just delegates to the inner type's method,
            // but the monomorphization collector doesn't instantiate
            // the blanket impl's wrapper — it expects the call to go
            // directly to the inner type's method.  So we must
            // re-resolve with the inner type and set needs_self_deref.
            //
            // IMPORTANT: This check only applies to trait methods where
            // args[0] is the Self type.  For inherent methods (e.g.
            // `<[T]>::iter`), args[0] is a type parameter like T, NOT
            // Self.  Checking it would incorrectly trigger needs_self_deref
            // when T happens to be a reference type (e.g. T = &str).
            let mut needs_self_deref = false;
            let is_trait_method = matches!(
                tcx.def_kind(tcx.parent(*def_id)),
                rustc_hir::def::DefKind::Trait
            );
            let instance = if is_trait_method && let Some(orig_self) = args.first() {
                if let Some(orig_ty) = orig_self.as_type() {
                    if let ty::Ref(_, _inner_ty, _) = orig_ty.kind() {
                        let impl_def_id = tcx.parent(instance.def_id());
                        let is_impl = matches!(
                            tcx.def_kind(impl_def_id),
                            rustc_hir::def::DefKind::Impl { .. }
                        );
                        let raw_impl_self = if is_impl {
                            Some(tcx.type_of(impl_def_id).skip_binder())
                        } else {
                            None
                        };
                        if matches!(raw_impl_self, Some(t) if !matches!(t.kind(), ty::Ref(_, _, _) | ty::Param(_)))
                        {
                            // Case A: resolved through blanket impl to direct impl.
                            needs_self_deref = true;
                            instance
                        } else {
                            // Case B (blanket impl) or non-impl parent — skip for now.
                            instance
                        }
                    } else {
                        instance
                    }
                } else {
                    instance
                }
            } else {
                instance
            };
            let needs_location = instance.def.requires_caller_location(tcx);
            // Detect virtual dispatch (trait object method calls).
            if let ty::InstanceKind::Virtual(_, idx) = instance.def {
                return ResolvedCall {
                    target: Some(CallTarget::Virtual(idx)),
                    requires_caller_location: needs_location,
                    needs_self_deref: false,
                    resolved_instance: None,
                    needs_tuple_spread: false,
                };
            }
            if instance.args.has_non_region_param() {
                return ResolvedCall {
                    target: None,
                    requires_caller_location: needs_location,
                    needs_self_deref: false,
                    resolved_instance: None,
                    needs_tuple_spread: false,
                };
            }
            // Detect calls through Fn/FnMut/FnOnce that resolve to a
            // closure body — the caller passes args as a tuple but the
            // closure body expects individual parameters.
            let is_fn_trait_call = is_trait_method && {
                let trait_id = tcx.parent(*def_id);
                Some(trait_id) == tcx.lang_items().fn_trait()
                    || Some(trait_id) == tcx.lang_items().fn_mut_trait()
                    || Some(trait_id) == tcx.lang_items().fn_once_trait()
            };
            let needs_spread = is_fn_trait_call && tcx.is_closure_like(instance.def_id());
            ResolvedCall {
                target: Some(CallTarget::Direct(
                    tcx.symbol_name(instance).name.to_string(),
                )),
                requires_caller_location: needs_location,
                needs_self_deref,
                resolved_instance: Some(instance),
                needs_tuple_spread: needs_spread,
            }
        }
        _ => ResolvedCall {
            target: None,
            requires_caller_location: false,
            needs_self_deref: false,
            resolved_instance: None,
            needs_tuple_spread: false,
        },
    }
}

impl<'a, 'tcx> TranslationCtx<'a, 'tcx> {
    pub(super) fn translate_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        target: &Option<BasicBlock>,
        source_info: mir::SourceInfo,
    ) {
        // Check for compiler intrinsics and handle them inline.
        if let Some((intrinsic_name, intrinsic_substs)) =
            detect_intrinsic(self.tcx, func, self.instance)
        {
            // Translate intrinsic arguments to IR values.
            let mut intrinsic_args: Vec<ValueRef> = Vec::new();
            for arg in args {
                if let Some(v) = self.translate_operand(&arg.node) {
                    intrinsic_args.push(v);
                    // Also push fat pointer metadata for intrinsics that
                    // need it (e.g. size_of_val on unsized types).
                    if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                        if place.projection.is_empty() {
                            if let Some(fat_v) = self.fat_locals.get(place.local) {
                                let local_ty =
                                    self.monomorphize(self.mir.local_decls[place.local].ty);
                                if is_fat_ptr(self.tcx, local_ty) {
                                    intrinsic_args.push(fat_v);
                                }
                            }
                        }
                    }
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
            let (proj_addr, proj_size, saved_local_for_proj) = if has_dest_projection {
                let saved = self.locals.get(destination.local);
                let info = self.translate_place_to_addr(destination).map(|(a, ty)| {
                    let a = self.coerce_to_ptr(a);
                    let sz = type_size(self.tcx, ty).unwrap_or(8) as u32;
                    (a, sz)
                });
                match info {
                    Some((a, sz)) => (Some(a), sz, saved),
                    None => (None, 0, saved),
                }
            } else {
                (None, 0, None)
            };
            let handled = translate_intrinsic(
                self.tcx,
                &intrinsic_name,
                intrinsic_substs,
                &intrinsic_args,
                destination.local,
                &mut self.builder,
                &mut self.locals,
                &mut self.symbols,
                self.current_mem,
                if has_dest_projection { proj_addr } else { None },
            );
            if handled {
                // Capture the intrinsic result before any store-back.
                let intrinsic_result = self.locals.get(destination.local);

                if has_dest_projection {
                    // Destination has projections (e.g. `(*RET) = bswap(...)`).
                    // Store the result through the pre-computed projected
                    // address and restore the original local value.
                    if let Some(orig) = saved_local_for_proj {
                        self.locals.set(destination.local, orig);
                    }
                    // If the intrinsic didn't change the local (e.g. i128
                    // bswap writes directly through the pointer obtained from
                    // locals.get()), the data is already at the correct
                    // location — skip the redundant store which would
                    // overwrite the result with the raw pointer value.
                    let intrinsic_changed_local = intrinsic_result != saved_local_for_proj;
                    if intrinsic_changed_local {
                        if let Some(result) = intrinsic_result {
                            if let Some(addr) = proj_addr {
                                if proj_size > 0 {
                                    self.current_mem = self.builder.store(
                                        result.into(),
                                        addr.into(),
                                        proj_size,
                                        self.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                }
                            }
                        }
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
                        // When result_val is a pointer (another stack slot) and
                        // the type is wider than 8 bytes, copy word-by-word
                        // instead of storing the pointer value as data.
                        let val_is_ptr =
                            matches!(self.builder.value_type(result_val), Some(Type::Ptr(_)));
                        if val_is_ptr && size > 8 {
                            let mut offset = 0u32;
                            while offset < size {
                                let chunk = std::cmp::min(8, size - offset);
                                let src_addr = if offset == 0 {
                                    result_val
                                } else {
                                    let off =
                                        self.builder.iconst(offset as i64, Origin::synthetic());
                                    self.builder.ptradd(
                                        result_val.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    )
                                };
                                let word = self.builder.load(
                                    src_addr.into(),
                                    chunk,
                                    Type::Int,
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                let dst_addr = if offset == 0 {
                                    slot
                                } else {
                                    let off =
                                        self.builder.iconst(offset as i64, Origin::synthetic());
                                    self.builder.ptradd(
                                        slot.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    )
                                };
                                self.current_mem = self.builder.store(
                                    word.into(),
                                    dst_addr.into(),
                                    chunk,
                                    self.current_mem.into(),
                                    Origin::synthetic(),
                                );
                                offset += chunk;
                            }
                        } else {
                            self.current_mem = self.builder.store(
                                result_val.into(),
                                slot.into(),
                                size.max(1),
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
                        }
                        self.locals.set(destination.local, slot);
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
                return;
            }

            // Try lowering memory intrinsics to libc calls.
            let mem_handled = translate_memory_intrinsic(
                self.tcx,
                &intrinsic_name,
                intrinsic_substs,
                &intrinsic_args,
                destination.local,
                &mut self.builder,
                &mut self.locals,
                &mut self.symbols,
                self.current_mem,
            );
            if let Some(new_mem) = mem_handled {
                self.current_mem = new_mem;
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
            // Intrinsic detected but not handled inline.  If it maps to a
            // libc symbol (e.g. compare_bytes → memcmp), fall through to
            // the normal call path so resolve_call_target can emit the call.
            // Only treat truly unhandled intrinsics as no-ops.
            if intrinsic_to_libc(&intrinsic_name).is_none() {
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

        // Skip drop_in_place calls within function bodies.  The Drop
        // terminator handler above calls drop_in_place directly for types
        // that need it, but recursive field-dropping inside drop glue may
        // reference drop_in_place instances that rustc didn't collect as
        // MonoItems.  Skipping these avoids undefined symbol errors while
        // still executing custom Drop impls.
        // Also skip precondition_check calls — these are debug-mode
        // assertions for unchecked operations that may not have MonoItems.
        if let Operand::Constant(c) = func {
            let fn_ty = self.tcx.instantiate_and_normalize_erasing_regions(
                self.instance.args,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(c.ty()),
            );
            if let ty::FnDef(def_id, _fn_args) = fn_ty.kind() {
                let skip = Some(*def_id) == self.tcx.lang_items().drop_in_place_fn()
                    || self
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
                    // First try fat_locals (set when the fat pointer was created
                    // from a parameter or an Unsize coercion).
                    if let Some(v) = self.fat_locals.get(place.local) {
                        Some(v)
                    } else if self.stack_locals.is_stack(place.local) && place.projection.is_empty()
                    {
                        // The fat pointer lives in a stack slot.  The vtable
                        // pointer is the second word (offset 8).
                        if let Some(base) = self.locals.get(place.local) {
                            let off8 = self.builder.iconst(8, Origin::synthetic());
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
                    } else {
                        // Projected place (e.g. (*_1).buf) — compute the
                        // address of the fat pointer field and load the
                        // vtable from offset 8.
                        if let Some((addr, _)) = self.translate_place_to_addr(place) {
                            let addr = self.coerce_to_ptr(addr);
                            let off8 = self.builder.iconst(8, Origin::synthetic());
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
                let off_val = self.builder.iconst(offset as i64, Origin::synthetic());
                let fn_addr =
                    self.builder
                        .ptradd(vtable.into(), off_val.into(), 0, Origin::synthetic());
                let fn_ptr = self.builder.load(
                    fn_addr.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    None,
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

        // Check if the callee returns a large struct (needs sret on caller side).
        // When the destination has a projection (e.g. `_3.fld0 = fn1(...)`),
        // use the projected field type, not the local's aggregate type.
        let dest_ty = if destination.projection.is_empty() {
            self.monomorphize(self.mir.local_decls[destination.local].ty)
        } else {
            self.monomorphize(destination.ty(&self.mir.local_decls, self.tcx).ty)
        };
        let dest_size = type_size(self.tcx, dest_ty);
        let callee_sret = needs_indirect_return(self.tcx, dest_ty);

        // When the destination has projections (e.g. `_5.fld0 = fn1()`),
        // pre-compute the projected address before translating arguments
        // (which may modify locals).  We also save the original local value
        // so we can restore it after storing the call result.
        let has_call_dest_proj = !destination.projection.is_empty();
        let (call_proj_addr, call_proj_size, _call_saved_local) = if has_call_dest_proj {
            let saved = self.locals.get(destination.local);
            let info = self.translate_place_to_addr(destination).map(|(a, ty)| {
                let a = self.coerce_to_ptr(a);
                let sz = type_size(self.tcx, ty).unwrap_or(8) as u32;
                (a, sz)
            });
            match info {
                Some((a, sz)) => (Some(a), sz, saved),
                None => (None, 0, saved),
            }
        } else {
            (None, 0, None)
        };

        // Translate arguments to IR operands, decomposing fat pointers.
        let mut ir_args: Vec<tuffy_ir::instruction::Operand> = Vec::new();

        // If callee uses sret, allocate a stack slot and prepend as first arg.
        // Reuse the destination's existing stack slot when it is already a
        // stack local AND large enough — this avoids creating a separate sret
        // slot that other basic blocks cannot see (cross-block value flow).
        let sret_slot = if callee_sret {
            let needed_size = type_size(self.tcx, dest_ty).unwrap_or(8) as u32;
            let existing_slot = if self.stack_locals.is_stack(destination.local) {
                self.locals
                    .get(destination.local)
                    .filter(|s| matches!(self.builder.value_type(*s), Some(Type::Ptr(_))))
                    .filter(|s| {
                        // Only reuse if the existing slot is large enough.
                        self.builder.stack_slot_size(*s).unwrap_or(0) >= needed_size
                    })
            } else {
                None
            };
            let slot = existing_slot
                .unwrap_or_else(|| self.builder.stack_slot(needed_size, Origin::synthetic()));
            ir_args.push(slot.into());
            Some(slot)
        } else {
            None
        };

        for arg in args {
            // Skip zero-sized (Unit) and untranslatable args — they don't
            // occupy an ABI slot, matching the callee's param skipping.
            let arg_ty = match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty)
                }
                Operand::Constant(c) => self.monomorphize(c.ty()),
                _ => self.monomorphize(self.mir.local_decls[mir::Local::from_usize(0)].ty),
            };
            if matches!(translate_ty(arg_ty), Some(Type::Unit) | None) {
                continue;
            }
            // Skip zero-sized ADTs (e.g. Global allocator) — they
            // don't occupy an ABI slot, matching the callee's param skipping.
            if type_size(self.tcx, arg_ty).unwrap_or(0) == 0 {
                continue;
            }

            // Tuple spreading for closure calls through Fn/FnMut/FnOnce:
            // the caller passes args as a single tuple but the closure
            // body expects individual parameters.  Only spread tuples
            // with 2+ non-ZST fields — 1-tuples have identical layout
            // to the inner type and don't need spreading.
            if needs_tuple_spread
                && let ty::Tuple(fields) = arg_ty.kind()
                && fields
                    .iter()
                    .filter(|f| type_size(self.tcx, *f).unwrap_or(0) > 0)
                    .count()
                    >= 2
                && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                && let Some(base) = self.locals.get(place.local)
                && matches!(self.builder.value_type(base), Some(Type::Ptr(_)))
            {
                let typing_env = ty::TypingEnv::fully_monomorphized();
                if let Ok(layout) = self.tcx.layout_of(typing_env.as_query_input(arg_ty)) {
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
                            let off = self.builder.iconst(offset as i64, Origin::synthetic());
                            self.builder
                                .ptradd(base.into(), off.into(), 0, Origin::synthetic())
                        };
                        if fsz <= 8 {
                            let fty = translate_ty(ft).unwrap_or(Type::Int);
                            let val = self.builder.load(
                                addr.into(),
                                fsz as u32,
                                fty,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(val.into());
                        } else if fsz <= 16 {
                            // Decompose 9-16 byte fields into two words.
                            let w0 = self.builder.load(
                                addr.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(w0.into());
                            let off8 = self.builder.iconst(8, Origin::synthetic());
                            let a1 = self.builder.ptradd(
                                addr.into(),
                                off8.into(),
                                0,
                                Origin::synthetic(),
                            );
                            let w1 = self.builder.load(
                                a1.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(w1.into());
                        } else {
                            // >16 byte fields: pass pointer.
                            ir_args.push(addr.into());
                        }
                    }
                    continue;
                }
            }

            if let Some(v) = self.translate_operand(&arg.node) {
                // Check if this argument is a stack-allocated local that
                // should be decomposed into register-sized words (≤16 bytes).
                let decomposed = if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                    // Detect stack-local arguments that need decomposition:
                    // 1. Non-projected stack locals (e.g. `move _3` where _3 is stack)
                    // 2. Projected places on stack locals where the projected
                    //    type is > 8 bytes (e.g. `move _2.0` where _2 is a
                    //    stack local and field 0 is &str/16 bytes).  In this
                    //    case translate_operand returns an address into the
                    //    source slot, which must be decomposed into registers.
                    let (is_stack_arg, arg_size) =
                        if place.projection.is_empty() && self.stack_locals.is_stack(place.local) {
                            let arg_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
                            (true, type_size(self.tcx, arg_ty).unwrap_or(0))
                        } else if !place.projection.is_empty()
                            && self.stack_locals.is_stack(place.local)
                        {
                            let projected_ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                            let projected_ty = self.monomorphize(projected_ty);
                            let psize = type_size(self.tcx, projected_ty).unwrap_or(0);
                            // Only treat as stack arg if the projected type is
                            // large enough that translate_operand returned an
                            // address rather than a loaded value.
                            if psize > 8 {
                                (true, psize)
                            } else {
                                (false, psize)
                            }
                        } else {
                            (false, 0)
                        };
                    if is_stack_arg && arg_size > 8 && arg_size <= 16 {
                        // Only decompose stack locals larger than 8 bytes.
                        // For ≤8-byte stack locals, translate_operand already
                        // loaded the value from the slot — decomposing again
                        // would double-dereference pointer-typed values.
                        // For projected places, use the projected address (v)
                        // returned by translate_operand, not the base local's slot.
                        let slot = if !place.projection.is_empty() {
                            v
                        } else {
                            self.locals.get(place.local).unwrap_or(v)
                        };
                        let slot_is_ptr =
                            matches!(self.builder.value_type(slot), Some(Type::Ptr(_)));
                        if slot_is_ptr {
                            // Load word(s) from the stack slot and pass in registers.
                            let word0 = self.builder.load(
                                slot.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(word0.into());
                            if arg_size > 8 {
                                let off = self.builder.iconst(8, Origin::synthetic());
                                let addr1 = self.builder.ptradd(
                                    slot.into(),
                                    off.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                let word1 = self.builder.load(
                                    addr1.into(),
                                    8,
                                    Type::Int,
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                );
                                ir_args.push(word1.into());
                            }
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !decomposed {
                    // Check if this is a constant struct (9-16 bytes) that
                    // needs to be decomposed into two register-sized words
                    // for the SysV ABI.  translate_const returns a
                    // symbol_addr for Indirect constants, but the callee
                    // expects the struct fields in separate registers.
                    let const_decomposed = if let Operand::Constant(_) = &arg.node {
                        let arg_size = type_size(self.tcx, arg_ty).unwrap_or(0);
                        if arg_size > 8
                            && arg_size <= 16
                            && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                            && !is_fat_ptr(self.tcx, arg_ty)
                        {
                            let word0 = self.builder.load(
                                v.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(word0.into());
                            let off = self.builder.iconst(8, Origin::synthetic());
                            let addr1 =
                                self.builder
                                    .ptradd(v.into(), off.into(), 0, Origin::synthetic());
                            let word1 = self.builder.load(
                                addr1.into(),
                                8,
                                Type::Int,
                                self.current_mem.into(),
                                None,
                                Origin::synthetic(),
                            );
                            ir_args.push(word1.into());
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if const_decomposed {
                        // Already pushed both words — skip normal arg handling.
                    } else {
                        ir_args.push(v.into());
                        // If this arg is a Copy/Move of a fat local, also pass the high part.
                        // Exception: for virtual dispatch, skip the vtable pointer on the
                        // first argument (self) — the actual method only takes the data ptr.
                        let skip_fat =
                            is_virtual && ir_args.len() == 1 + if callee_sret { 1 } else { 0 };
                        if !skip_fat
                            && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                            && let Some(fat_v) = self.fat_locals.get(place.local)
                        {
                            // Only push the fat component when the local's
                            // type is actually a fat pointer.  Aggregates
                            // (structs) with 2+ fields also set fat_locals
                            // but their second field is not ABI metadata.
                            let local_ty = self.monomorphize(self.mir.local_decls[place.local].ty);
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
                                let len_val = self.builder.iconst(meta as i64, Origin::synthetic());
                                ir_args.push(len_val.into());
                            } else if let Some(mir::ConstValue::Indirect { alloc_id, offset }) =
                                resolved
                                && is_fat_ptr(self.tcx, const_ty)
                            {
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
                                    let len_val =
                                        self.builder.iconst(len as i64, Origin::synthetic());
                                    ir_args.push(len_val.into());
                                }
                            }
                        }
                    }
                }
            }
        }

        // When Instance::try_resolve resolved through a blanket impl that
        // strips a reference from Self, the first argument has an extra level
        // of indirection.  Dereference it so the callee receives the correct
        // pointer type (e.g. &mut Formatter instead of &&mut Formatter).
        // Only apply when the argument is a Ptr (stack slot address) — if
        // it's already an Int/scalar, the extra indirection doesn't exist.
        if needs_self_deref {
            let self_idx = if callee_sret { 1 } else { 0 };
            if self_idx < ir_args.len() {
                let arg_ty = self.builder.value_type(ir_args[self_idx].value);
                if matches!(arg_ty, Some(Type::Ptr(_))) {
                    let old_self = ir_args[self_idx].clone();
                    let derefed = self.builder.load(
                        old_self,
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
            self.builder.symbol_addr(sym_id, Origin::synthetic())
        } else if let Some(fn_ptr) = self.translate_operand(func) {
            // Indirect call through a function pointer in a local.
            fn_ptr
        } else {
            self.builder.iconst(0, Origin::synthetic())
        };
        let call_ret_ty = translate_ty(dest_ty).unwrap_or(Type::Unit);
        let (call_mem, call_data) = self.builder.call(
            callee_val.into(),
            ir_args,
            call_ret_ty,
            self.current_mem.into(),
            None,
            Origin::synthetic(),
        );
        self.current_mem = call_mem;
        // For non-void calls, call_data is Some(data_vref).
        // For void calls, call_data is None — use a dummy zero.
        let call_vref = call_data.unwrap_or_else(|| self.builder.iconst(0, Origin::synthetic()));

        if has_call_dest_proj {
            // Destination has projections (e.g. `_5.fld0 = fn1()`).
            // Store the call result through the pre-computed projected
            // address and leave the base local unchanged.
            if let Some(addr) = call_proj_addr {
                if call_proj_size > 0 {
                    self.current_mem = self.builder.store(
                        call_vref.into(),
                        addr.into(),
                        call_proj_size,
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                }
            }
        } else if callee_sret {
            // For sret calls, the result is in the stack slot we allocated.
            // The destination local becomes a pointer to that slot.
            let slot = sret_slot.unwrap();
            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
            // For fat pointer sret returns (&[T], &str, etc.), the second
            // word (length/vtable) is at offset 8 in the sret buffer.
            // Load it into fat_locals so it gets passed when this local
            // is later used as a call argument.
            if is_fat_ptr(self.tcx, dest_ty) {
                let off = self.builder.iconst(8, Origin::synthetic());
                let addr = self
                    .builder
                    .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
                let fat_val = self.builder.load(
                    addr.into(),
                    8,
                    Type::Int,
                    self.current_mem.into(),
                    None,
                    Origin::synthetic(),
                );
                self.fat_locals.set(destination.local, fat_val);
            }
        } else if dest_size.unwrap_or(0) > 8 && !is_i128_or_u128(dest_ty) {
            // Two-register return (9-16 bytes): RAX has first word,
            // RDX has second word. Reconstruct into a stack slot so
            // downstream code gets a valid pointer to the struct.
            // i128/u128 returns are handled by the legalization pass.
            let size = dest_size.unwrap();
            let slot = if let Some(existing) = self.locals.get(destination.local) {
                if self.stack_locals.is_stack(destination.local) {
                    existing
                } else {
                    self.builder.stack_slot(size as u32, Origin::synthetic())
                }
            } else {
                self.builder.stack_slot(size as u32, Origin::synthetic())
            };
            self.current_mem = self.builder.store(
                call_vref.into(),
                slot.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            );

            // Mark the call as producing a secondary return value (RDX).
            self.abi_metadata
                .mark_call_secondary_return(call_mem.index());
            let rdx_val = self.builder.iconst(0, Origin::synthetic());
            self.abi_metadata
                .mark_secondary_return_capture(rdx_val.index(), call_mem.index());
            let off = self.builder.iconst(8, Origin::synthetic());
            let addr1 = self
                .builder
                .ptradd(slot.into(), off.into(), 0, Origin::synthetic());
            self.current_mem = self.builder.store(
                rdx_val.into(),
                addr1.into(),
                8,
                self.current_mem.into(),
                Origin::synthetic(),
            );

            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);

            // For fat pointer two-register returns (&[T], &str, &dyn Trait),
            // also record the RDX placeholder in fat_locals so that
            // PtrMetadata and fat-pointer propagation can find the
            // metadata (length/vtable) without loading from the stack slot.
            if is_fat_ptr(self.tcx, dest_ty) {
                self.fat_locals.set(destination.local, rdx_val);
            }
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
                let slot = self.builder.stack_slot(size.max(1), Origin::synthetic());
                self.current_mem = self.builder.store(
                    call_vref.into(),
                    slot.into(),
                    size,
                    self.current_mem.into(),
                    Origin::synthetic(),
                );
                self.locals.set(destination.local, slot);
            } else if self.stack_locals.is_stack(destination.local) {
                // Destination was pre-promoted to a stack local (e.g. because
                // its address is taken later via `&`).  Store the scalar
                // return value into the existing slot instead of overwriting
                // the slot pointer with the raw value.
                if let Some(slot) = self.locals.get(destination.local) {
                    let size = dest_size.unwrap_or(8) as u32;
                    self.current_mem = self.builder.store(
                        call_vref.into(),
                        slot.into(),
                        size.max(1),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
                }
            } else {
                self.locals.set(destination.local, call_vref);
            }

            // Capture secondary return register only for fat pointer returns
            // (e.g., &str, &[T]) where RDX carries the second word (length/vtable).
            // Non-fat types must NOT get a fat_locals entry, otherwise the
            // spurious high-part value will be injected as an extra argument
            // when this local is later passed to another function call.
            if is_fat_ptr(self.tcx, dest_ty) {
                self.abi_metadata
                    .mark_call_secondary_return(call_mem.index());
                let rdx_val = self.builder.iconst(0, Origin::synthetic());
                self.abi_metadata
                    .mark_secondary_return_capture(rdx_val.index(), call_mem.index());
                self.fat_locals.set(destination.local, rdx_val);
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
