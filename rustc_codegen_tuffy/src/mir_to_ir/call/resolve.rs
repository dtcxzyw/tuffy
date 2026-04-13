use super::*;

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
