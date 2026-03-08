//! Call translation for MIR → IR conversion.

use rustc_middle::mir::{self, BasicBlock, Operand, Place};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};
use rustc_span::source_map::Spanned;

use tuffy_ir::instruction::{Operand as IrOperand, Origin};
use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;

use super::ctx::TranslationCtx;
use super::intrinsic::intrinsic_to_libc;
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
    // Use the projected type so that Deref projections (e.g.
    // `move (*_self)` in call_mut shims where _self: &mut FnDef)
    // resolve to the underlying FnDef type, not &mut FnDef.
    let Some(ty) = operand_ty_projected(func_op, mir, tcx) else {
        return ResolvedCall {
            target: None,
            requires_caller_location: false,
            needs_self_deref: false,
            resolved_instance: None,
            needs_tuple_spread: false,
        };
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
        if let Some((intrinsic_name, intrinsic_substs)) = self.detect_intrinsic(func) {
            // Translate intrinsic arguments to IR values.
            let mut intrinsic_args: Vec<ValueRef> = Vec::new();
            for arg in args {
                if let Some(v) = self.translate_operand(&arg.node) {
                    // For large scalar types (e.g. i128, 16 bytes) translate_operand
                    // returns a stack-slot pointer rather than the value.  Load the
                    // integer bits so intrinsics (bswap, ctlz, bitreverse, …) receive
                    // the actual value, not an address.
                    let v = if matches!(self.builder.value_type(v), Some(Type::Ptr(_))) {
                        let arg_ty =
                            self.monomorphize(arg.node.ty(&self.mir.local_decls, self.tcx));
                        if let Some(sz) = type_size(self.tcx, arg_ty) {
                            if sz <= 16 && matches!(translate_ty(self.tcx, arg_ty), Some(Type::Int))
                            {
                                self.builder.load(
                                    v.into(),
                                    sz as u32,
                                    default_int_type(),
                                    self.current_mem.into(),
                                    None,
                                    Origin::synthetic(),
                                )
                            } else {
                                v
                            }
                        } else {
                            v
                        }
                    } else {
                        v
                    };
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
                &intrinsic_name,
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
                                    let off = self.builder.iconst(
                                        offset as i64,
                                        64,
                                        IntSignedness::DontCare,
                                        Origin::synthetic(),
                                    );
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
                                    default_int_type(),
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
                                    self.builder.ptradd(
                                        slot.into(),
                                        off.into(),
                                        0,
                                        Origin::synthetic(),
                                    )
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
            let mem_handled = self.translate_memory_intrinsic(
                &intrinsic_name,
                intrinsic_substs,
                &intrinsic_args,
                destination.local,
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
                    default_int_type(),
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

        // Check if this is a large struct return (>16 bytes) that requires SRET.
        // On x86-64 SysV ABI, structs larger than 16 bytes are returned via
        // a hidden pointer passed as the first argument.
        let needs_sret = dest_size.is_some_and(|sz| sz > 16);
        let sret_slot = if needs_sret {
            // If the destination is _0 and the function itself has an SRET
            // pointer, reuse it so the callee writes directly into the
            // caller's return buffer (avoids an extra copy).
            if destination.projection.is_empty()
                && destination.local == mir::Local::from_usize(0)
                && let Some(sret) = self.sret_ptr
            {
                Some(sret)
            } else if destination.projection.is_empty()
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
                Some(self.builder.stack_slot(sz, Origin::synthetic()))
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

        // For SRET, pass the return slot address as the first argument.
        if let Some(slot) = sret_slot {
            ir_args.push(slot.into());
        }

        for arg in args {
            // Skip zero-sized (Unit) and untranslatable args — they don't
            // occupy a runtime slot.
            let arg_ty = operand_ty_projected(&arg.node, self.mir, self.tcx)
                .map(|ty| self.monomorphize(ty))
                .unwrap_or_else(|| {
                    self.monomorphize(self.mir.local_decls[mir::Local::from_usize(0)].ty)
                });
            if matches!(translate_ty(self.tcx, arg_ty), Some(Type::Unit) | None) {
                continue;
            }
            // Skip zero-sized ADTs (e.g. Global allocator) — they
            // don't occupy a runtime slot.
            if type_size(self.tcx, arg_ty).unwrap_or(0) == 0 {
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
                        };
                        if fsz <= 8 {
                            let fty = translate_ty(self.tcx, ft).unwrap_or(default_int_type());
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
                                default_int_type(),
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            ir_args.push(w0.into());
                            let off8 = self.builder.iconst(
                                8,
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
                                8,
                                default_int_type(),
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
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

            if let Some(mut v) = self.translate_operand(&arg.node) {
                let arg_size = type_size(self.tcx, arg_ty).unwrap_or(0);

                // For constant aggregates (tuples, structs, arrays) ≤8 bytes, translate_operand
                // returns a pointer to the constant data. Load the value so it's passed
                // by value in a register, not by reference.
                if matches!(&arg.node, Operand::Constant(_))
                    && matches!(arg_ty.kind(), ty::Tuple(_) | ty::Adt(..) | ty::Array(..))
                    && arg_size > 0
                    && arg_size <= 8
                    && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                {
                    v = self.builder.load(
                        v.into(),
                        arg_size as u32,
                        default_int_type(),
                        self.current_mem.into(),
                        None,
                        Origin::synthetic(),
                    );
                }

                // Decompose 9-16 byte struct arguments into two register-
                // sized words for the SysV ABI.  Stack-allocated structs
                // are represented as Ptr values; load both halves so the
                // callee receives them in two registers (rdi+rsi, etc.).
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
                let is_struct_arg = arg_size > 8
                    && arg_size <= 16
                    && !matches!(repr_kind(self.tcx, arg_ty), ReprKind::Scalar)
                    && !is_fat_value_not_slot
                    && matches!(self.builder.value_type(v), Some(Type::Ptr(_)));
                let decomposed = if is_struct_arg {
                    let w0 = self.builder.load(
                        v.into(),
                        8,
                        default_int_type(),
                        self.current_mem.into(),
                        int_annotation_for_bytes(8),
                        Origin::synthetic(),
                    );
                    ir_args.push(w0.into());
                    let off8 =
                        self.builder
                            .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
                    let hi_addr =
                        self.builder
                            .ptradd(v.into(), off8.into(), 0, Origin::synthetic());
                    let w1 = self.builder.load(
                        hi_addr.into(),
                        8,
                        default_int_type(),
                        self.current_mem.into(),
                        int_annotation_for_bytes(8),
                        Origin::synthetic(),
                    );
                    ir_args.push(w1.into());
                    true
                } else {
                    false
                };

                if !decomposed {
                    // Annotate i128/u128 arguments so the legalization
                    // pass knows to split them into (lo, hi) even when
                    // the value fits in 64 bits (e.g. small constants).
                    if matches!(
                        arg_ty.kind(),
                        ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128)
                    ) {
                        // If the value is a Ptr (address of the i128 in memory, from
                        // translate_place_to_value for >8-byte scalars), load lo+hi
                        // from the address instead of passing the pointer annotated
                        // as 128-bit (which would pass the address value, not the data).
                        if matches!(self.builder.value_type(v), Some(Type::Ptr(_))) {
                            let w0 = self.builder.load(
                                v.into(),
                                8,
                                default_int_type(),
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            ir_args.push(w0.into());
                            let off8 = self.builder.iconst(
                                8,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let hi_addr =
                                self.builder
                                    .ptradd(v.into(), off8.into(), 0, Origin::synthetic());
                            let w1 = self.builder.load(
                                hi_addr.into(),
                                8,
                                default_int_type(),
                                self.current_mem.into(),
                                int_annotation_for_bytes(8),
                                Origin::synthetic(),
                            );
                            ir_args.push(w1.into());
                        } else {
                            let ann = translate_annotation(arg_ty).unwrap_or(Annotation::Int(
                                IntAnnotation {
                                    bit_width: 128,
                                    signedness: IntSignedness::Unsigned,
                                },
                            ));
                            ir_args.push(IrOperand::annotated(v, ann));
                        }
                    } else if arg_size == 16
                        && matches!(repr_kind(self.tcx, arg_ty), ReprKind::Scalar)
                        && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                    {
                        // Newtype wrapper over u128/i128 (e.g. `(u128,)`) with
                        // 16-byte Scalar representation. The value is a pointer to
                        // its 16-byte storage; load lo+hi and pass as two registers.
                        let w0 = self.builder.load(
                            v.into(),
                            8,
                            default_int_type(),
                            self.current_mem.into(),
                            int_annotation_for_bytes(8),
                            Origin::synthetic(),
                        );
                        ir_args.push(w0.into());
                        let off8 = self.builder.iconst(
                            8,
                            64,
                            IntSignedness::DontCare,
                            Origin::synthetic(),
                        );
                        let hi_addr =
                            self.builder
                                .ptradd(v.into(), off8.into(), 0, Origin::synthetic());
                        let w1 = self.builder.load(
                            hi_addr.into(),
                            8,
                            default_int_type(),
                            self.current_mem.into(),
                            int_annotation_for_bytes(8),
                            Origin::synthetic(),
                        );
                        ir_args.push(w1.into());
                    } else {
                        // Large struct/array (>16 bytes): pass a pointer to a fresh copy.
                        // Passing the original slot directly would let the callee overwrite
                        // the caller's local (violating Rust pass-by-value semantics).
                        if arg_size > 16 && matches!(self.builder.value_type(v), Some(Type::Ptr(_)))
                        {
                            let align = type_align(self.tcx, arg_ty).unwrap_or(1) as u32;
                            let tmp = self
                                .builder
                                .stack_slot(arg_size as u32, Origin::synthetic());
                            let count = self.builder.iconst(
                                arg_size as i64,
                                64,
                                IntSignedness::DontCare,
                                Origin::synthetic(),
                            );
                            let tmp_annotated = IrOperand::annotated(tmp, Annotation::Align(align));
                            let v_annotated = IrOperand::annotated(v, Annotation::Align(align));
                            let new_mem = self.builder.mem_copy(
                                tmp_annotated,
                                v_annotated,
                                count.into(),
                                self.current_mem.into(),
                                Origin::synthetic(),
                            );
                            self.current_mem = new_mem;
                            ir_args.push(tmp.into());
                        } else {
                            ir_args.push(v.into());
                        }
                    }
                    // If this arg is a Copy/Move of a fat local, also pass the high part.
                    // Exception: for virtual dispatch, skip the vtable pointer on the
                    // first argument (self) — the actual method only takes the data ptr.
                    let skip_fat = is_virtual && ir_args.len() == 1;
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
                                    matches!(bt.kind(), ty::Str | ty::Slice(..) | ty::Dynamic(..))
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
            self.builder.symbol_addr(sym_id, Origin::synthetic())
        } else if let Some(fn_ptr) = self.translate_operand(func) {
            // Indirect call through a function pointer in a local.
            fn_ptr
        } else {
            self.builder
                .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic())
                .raw()
        };
        let call_ret_ty = translate_ty(self.tcx, dest_ty).unwrap_or(Type::Unit);
        let call_ret_ann = if matches!(call_ret_ty, Type::Int) {
            translate_annotation(dest_ty)
        } else {
            None
        };
        let (call_mem, call_data) = self.builder.call(
            callee_val.into(),
            ir_args,
            call_ret_ty,
            self.current_mem.into(),
            call_ret_ann,
            Origin::synthetic(),
        );
        self.current_mem = call_mem;
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
                    self.current_mem = self.builder.mem_copy(
                        addr_annotated,
                        sret_annotated,
                        count.into(),
                        self.current_mem.into(),
                        Origin::synthetic(),
                    );
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
            // SRET return (>16 bytes): the callee wrote the struct to the
            // stack slot we passed as the first argument. Just record the
            // slot as the destination local.
            self.locals.set(destination.local, slot);
            self.stack_locals.mark(destination.local);
        } else if dest_size.unwrap_or(0) > 8 {
            // Two-register return (9-16 bytes): RAX has the first 8 bytes,
            // RDX has the remaining bytes.  Capture both and store to a
            // stack slot.
            //
            // SRET (>16 bytes) is handled above, so any remaining >8-byte
            // return — whether Scalar (u128/i128) or non-Scalar (small struct)
            // — uses RAX+RDX on x86-64 SysV ABI.  No type-specific special
            // casing is needed here.
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
            // Store RAX (primary return) at offset 0.
            self.current_mem = self
                .builder
                .store(
                    call_vref.into(),
                    slot.into(),
                    8,
                    self.current_mem.into(),
                    Origin::synthetic(),
                )
                .raw();
            // Mark the call as having a secondary return in RDX and
            // capture it via a placeholder instruction.
            let call_idx = call_mem.index();
            self.abi_metadata.mark_call_secondary_return(call_idx);
            let rdx_capture =
                self.builder
                    .iconst(0, 64, IntSignedness::DontCare, Origin::synthetic());
            self.abi_metadata
                .mark_secondary_return_capture(rdx_capture.raw().index(), call_idx);
            // Store RDX (secondary return) at offset 8.
            let off8 = self
                .builder
                .iconst(8, 64, IntSignedness::DontCare, Origin::synthetic());
            let hi_addr = self
                .builder
                .ptradd(slot.into(), off8.into(), 0, Origin::synthetic());
            self.current_mem = self
                .builder
                .store(
                    rdx_capture.into(),
                    hi_addr.into(),
                    8,
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
                let slot = self.builder.stack_slot(size.max(1), Origin::synthetic());
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
