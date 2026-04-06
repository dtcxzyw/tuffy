//! MIR → tuffy IR translation.
//!
//! Translates rustc MIR into tuffy IR, supporting basic arithmetic,
//! control flow (branches, SwitchInt), and comparison operations.

mod call;
mod constant;
mod ctx;
mod discriminant;
mod fat_ptr;
mod intrinsic;
mod local_analysis;
mod operand;
mod place;
mod rvalue;
mod simd;
mod statement;
mod terminator;
pub(crate) mod types;

use ctx::{
    BlockMap, FatLocalMap, LocalMap, OverflowLocalMap, StackLocalSet, TranslationCtx,
    extract_param_names,
};
use types::*;

use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness};

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt};

use tuffy_codegen::{AbiMetadataBox, CodegenSession};
use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::Origin;
use tuffy_ir::module::{SymbolId, SymbolTable};
use tuffy_ir::types::Type;

/// Static data entry: (symbol_id, bytes, relocations).
/// Relocations are (offset_in_bytes, target_symbol_name) for function pointers in vtables.
type StaticDataVec = Vec<(SymbolId, Vec<u8>, Vec<(usize, String)>, u64)>;

/// Cache mapping rustc vtable `AllocId` → emitted symbol name.
/// Prevents duplicate vtable emissions for the same (type, trait) pair.
pub type VtableCache = std::collections::HashMap<rustc_middle::mir::interpret::AllocId, String>;

/// Cache mapping rustc memory `AllocId` → emitted symbol name.
/// Prevents duplicate data emissions for the same allocation, ensuring
/// pointers to the same const allocation share the same address.
pub type AllocCache = std::collections::HashMap<rustc_middle::mir::interpret::AllocId, String>;

/// Cache mapping allocation content → emitted symbol name.
/// Catches duplicate const allocations that have different `AllocId`s but
/// identical bytes (e.g., the same const promoted independently after inlining).
pub type ContentCache = std::collections::HashMap<(Vec<u8>, Vec<(usize, String)>, u64), String>;

/// Result of MIR → IR translation.
pub struct TranslationResult<'tcx> {
    pub func: Function,
    /// Interned symbol table shared across the codegen unit.
    pub symbols: SymbolTable,
    /// Static data blobs to emit in .rodata, keyed by SymbolId.
    pub static_data: StaticDataVec,
    /// Target-specific ABI metadata (e.g., secondary return register info).
    pub abi_metadata: AbiMetadataBox,
    /// Instances referenced by direct calls during translation.
    /// Used to compile `#[inline]` functions not collected as mono items.
    pub referenced_instances: Vec<Instance<'tcx>>,
    /// Symbol names that need weak undefined binding in the object file.
    pub weak_undefined_symbols: std::collections::HashSet<String>,
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    session: &CodegenSession,
    data_counter: &mut u64,
    vtable_cache: &mut VtableCache,
    alloc_cache: &mut AllocCache,
    content_cache: &mut ContentCache,
) -> Option<TranslationResult<'tcx>> {
    // Skip partially substituted polymorphic instances — the symbol mangler
    // will panic if generic parameters are still present.
    if instance.args.has_non_region_param() {
        return None;
    }
    // Skip intrinsics that must be overridden by the backend.  These have
    // no MIR body and `instance_mir` would ICE trying to build a shim.
    // They are handled inline at call sites (translate_intrinsic) instead.
    if let ty::InstanceKind::Intrinsic(def_id) = instance.def
        && tcx.intrinsic(def_id).is_some_and(|i| i.must_be_overridden)
    {
        return None;
    }
    // Skip items without MIR.  This covers:
    //  - Cross-crate non-inline functions (already compiled in the rlib)
    //  - Local extern declarations (e.g. `extern { fn panic_impl(); }` in core)
    // Exception: constructors (enum variant / struct) have synthesized MIR
    // via instance_mir even when is_mir_available returns false.
    if let ty::InstanceKind::Item(def_id) = instance.def
        && !tcx.is_mir_available(def_id)
        && !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..))
    {
        return None;
    }

    let mir = tcx.instance_mir(instance.def);
    let name = tcx.symbol_name(instance).name.to_string();
    // Monomorphize a MIR type using the instance's substitutions.
    let monomorphize = |ty: ty::Ty<'tcx>| -> ty::Ty<'tcx> {
        tcx.instantiate_and_normalize_erasing_regions(
            instance.args,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ty),
        )
    };

    let mut params = Vec::new();
    let mut param_anns = Vec::new();
    let mut byval_sizes: Vec<Option<u32>> = Vec::new();
    let target_part_bytes = u64::from(session.max_int_width() / 8);
    let target_direct_abi_bytes = u64::from(session.max_direct_abi_int_bytes());

    let ret_mir_ty = monomorphize(mir.local_decls[mir::RETURN_PLACE].ty);
    let ret_size = type_size(tcx, ret_mir_ty).unwrap_or(0);
    let ret_repr = repr_kind(tcx, ret_mir_ty);
    // Scalar and ScalarPair types that fit within the target's direct
    // integer-register ABI capacity stay in registers; larger values use SRET.
    let needs_sret = match ret_repr {
        ReprKind::Zst => false,
        ReprKind::Scalar => false,
        ReprKind::ScalarPair => ret_size > target_direct_abi_bytes,
        ReprKind::Memory => ret_size > target_part_bytes,
    };

    // For SRET functions, the return type becomes the hidden result pointer.
    // Otherwise, use the semantic return type. Small aggregates that fit in
    // the target's direct integer-register return path are captured as `Int`.
    let (ret_ty, ret_ann) = if needs_sret {
        (Some(Type::Ptr(0)), None)
    } else {
        let ty = translate_ty(tcx, ret_mir_ty)
            .filter(|t| !matches!(t, Type::Unit))
            .or(if ret_size > 0 && ret_size <= target_direct_abi_bytes {
                Some(Type::Int)
            } else {
                None
            });
        let ann = if matches!(ty, Some(Type::Int)) {
            int_bitwidth(ret_mir_ty)
                .map(|bw| {
                    Annotation::Int(IntAnnotation {
                        bit_width: bw,
                        signedness: if is_signed_int(ret_mir_ty) {
                            IntSignedness::Signed
                        } else {
                            IntSignedness::Unsigned
                        },
                    })
                })
                .or_else(|| {
                    // ScalarPair returns capture the first direct-register part
                    // in the primary return value; later lowering models the
                    // remaining ABI part via metadata.
                    if matches!(ret_repr, ReprKind::ScalarPair) {
                        int_annotation_for_bytes(target_part_bytes as u32)
                    } else {
                        int_annotation_for_bytes(ret_size as u32)
                    }
                })
        } else {
            translate_annotation(ret_mir_ty)
        };
        (ty, ann)
    };

    let mut symbols = SymbolTable::new();
    let func_sym = symbols.intern(&name);

    // Detect C ABI for byval stack parameter handling.
    // In SysV x86-64, struct params > 4 eightbytes (> 32 bytes) are MEMORY
    // class and passed on the stack (byval), not by hidden pointer in a register.
    let is_c_abi = {
        // Only Item instances have fn_sig; closures, generators, etc. do not.
        match instance.def {
            ty::InstanceKind::Item(def_id) => {
                let def_kind = tcx.def_kind(def_id);
                if matches!(
                    def_kind,
                    rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
                ) {
                    let fn_sig = tcx.fn_sig(def_id).instantiate(tcx, instance.args);
                    let fn_sig = tcx.normalize_erasing_late_bound_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        fn_sig,
                    );
                    !fn_sig.abi.is_rustic_abi()
                } else {
                    false
                }
            }
            _ => false,
        }
    };

    // Build all-args name map first, then filter to match params.
    let _all_names = extract_param_names(mir, &mut symbols);
    let mut param_names = Vec::new();

    // For SRET, prepend a hidden Ptr parameter (the return slot pointer).
    if needs_sret {
        params.push(Type::Ptr(0));
        param_anns.push(None);
        param_names.push(None);
        byval_sizes.push(None);
    }

    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = monomorphize(mir.local_decls[local].ty);
        let ir_ty = translate_ty(tcx, ty);
        let sz = type_size(tcx, ty).unwrap_or(0);

        if matches!(ir_ty, Some(Type::Unit)) || sz == 0 {
            continue;
        }

        // Non-zero-sized aggregate with no direct IR type: use Int register(s).
        if ir_ty.is_none() {
            let prk = repr_kind(tcx, ty);
            if matches!(prk, ReprKind::ScalarPair | ReprKind::Scalar)
                && sz > target_part_bytes
                && sz <= target_direct_abi_bytes
            {
                // Aggregate fits in the target's direct integer-register ABI path.
                params.push(Type::Int);
                param_anns.push(int_annotation_for_bytes(target_part_bytes as u32));
                param_names.push(None);
                byval_sizes.push(None);
                params.push(Type::Int);
                param_anns.push(int_annotation_for_bytes((sz - target_part_bytes) as u32));
                param_names.push(None);
                byval_sizes.push(None);
            } else if sz > target_part_bytes {
                // Memory type > 8 bytes: passed by hidden pointer.
                // For C ABI with size > 32 bytes, the data is on the
                // caller's stack (byval) rather than via a register pointer.
                let is_byval = is_c_abi && sz > 32;
                params.push(Type::Ptr(0));
                param_anns.push(None);
                param_names.push(None);
                byval_sizes.push(if is_byval { Some(sz as u32) } else { None });
            } else {
                params.push(Type::Int);
                param_anns.push(int_annotation_for_bytes(sz as u32));
                param_names.push(None);
                byval_sizes.push(None);
            }
            continue;
        }

        let ir_ty = ir_ty.unwrap();
        let is_int = matches!(ir_ty, Type::Int);
        // Values larger than the target's direct integer-register ABI
        // capacity are passed indirectly.
        let param_ty = if sz > target_direct_abi_bytes {
            Type::Ptr(0)
        } else {
            ir_ty
        };
        let param_ann = if sz > target_direct_abi_bytes {
            None
        } else if is_int {
            int_bitwidth(ty).map(|bw| {
                Annotation::Int(IntAnnotation {
                    bit_width: bw,
                    signedness: if is_signed_int(ty) {
                        IntSignedness::Signed
                    } else {
                        IntSignedness::Unsigned
                    },
                })
            })
        } else {
            translate_annotation(ty)
        };
        params.push(param_ty);
        param_anns.push(param_ann);
        param_names.push(None);
        // For C ABI with translatable types > 32 bytes, mark as byval.
        let is_byval = is_c_abi && sz > 32;
        byval_sizes.push(if is_byval { Some(sz as u32) } else { None });
        // Fat pointer types (&str, &[T], &dyn Trait) are passed
        // as two register-sized values: data pointer + metadata
        // (length or vtable pointer).
        if is_fat_ptr(tcx, ty) {
            let (meta_ty, meta_ann) = match ty.kind() {
                ty::TyKind::Ref(_, pointee, _) | ty::TyKind::RawPtr(pointee, _) => {
                    let tail =
                        tcx.struct_tail_for_codegen(*pointee, ty::TypingEnv::fully_monomorphized());
                    match tail.kind() {
                        ty::TyKind::Dynamic(..) => (Type::Ptr(0), None),
                        _ => (Type::Int, default_int_annotation()),
                    }
                }
                _ => (Type::Int, default_int_annotation()),
            };
            params.push(meta_ty);
            param_anns.push(meta_ann);
            param_names.push(None);
            byval_sizes.push(None);
        }
    }

    // #[track_caller] functions receive an implicit &Location as the last
    // ABI parameter.  Add it to the IR signature so the callee body can
    // retrieve it via the `caller_location` intrinsic.
    let is_track_caller = instance.def.requires_caller_location(tcx);
    if is_track_caller {
        params.push(Type::Ptr(0));
        param_anns.push(None);
        param_names.push(None);
        byval_sizes.push(None);
    }

    let mut func = Function::new(func_sym, params, param_anns, param_names, ret_ty, ret_ann);
    func.byval_sizes = byval_sizes;
    let mut builder = Builder::new(&mut func);
    let abi_metadata = session.new_metadata();

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    // Compute reverse-postorder so that (except for back edges) every
    // definition of a MIR local is processed before its uses.  Creating
    // IR blocks in this order also means the ISel (which iterates blocks
    // sequentially) sees definitions before cross-block uses.
    let rpo_order = {
        let num_blocks = mir.basic_blocks.len();
        let mut visited = vec![false; num_blocks];
        let mut postorder = Vec::with_capacity(num_blocks);
        let mut stack: Vec<(BasicBlock, usize)> = vec![(BasicBlock::from_usize(0), 0)];
        visited[0] = true;
        while let Some((bb, next_succ)) = stack.last_mut() {
            let term = mir.basic_blocks[*bb].terminator();
            let succs: Vec<BasicBlock> = term.successors().collect();
            if *next_succ < succs.len() {
                let s = succs[*next_succ];
                *next_succ += 1;
                if !visited[s.as_usize()] {
                    visited[s.as_usize()] = true;
                    stack.push((s, 0));
                }
            } else {
                postorder.push(*bb);
                stack.pop();
            }
        }
        for (idx, &vis) in visited.iter().enumerate().take(num_blocks) {
            if !vis {
                postorder.push(BasicBlock::from_usize(idx));
            }
        }
        postorder.reverse();
        postorder
    };

    // Create IR blocks in RPO order so branches can reference target
    // blocks before they are translated, and block numbering follows RPO.
    let mut block_map = BlockMap::new(mir.basic_blocks.len());
    let mut block_mem_args: Vec<Option<tuffy_ir::value::ValueRef>> =
        vec![None; mir.basic_blocks.len()];
    for &bb in &rpo_order {
        let ir_block = builder.create_block();
        block_map.set(bb, ir_block);
        let mem_arg = builder.add_block_arg(ir_block, Type::Mem, None);
        block_mem_args[bb.as_usize()] = Some(mem_arg);
    }

    let entry = block_map.get(BasicBlock::from_u32(0));
    builder.switch_to_block(entry);

    let initial_mem = block_mem_args[0].expect("entry block mem arg missing");

    let mut ctx = TranslationCtx {
        tcx,
        mir,
        builder,
        locals: LocalMap::new(mir.local_decls.len()),
        fat_locals: FatLocalMap::new(),
        stack_locals: StackLocalSet::new(mir.local_decls.len()),
        overflow_locals: OverflowLocalMap::new(),
        symbols,
        static_data: Vec::new(),
        block_map,
        block_mem_args,
        abi_metadata,
        target_max_int_width: session.max_int_width(),
        target_max_abi_int_parts: session.max_abi_int_parts(),
        instance,
        current_mem: initial_mem,
        cast_fat_meta: FatLocalMap::new(),
        referenced_instances: Vec::new(),
        data_counter,
        vtable_cache,
        alloc_cache,
        content_cache,
        sret_ptr: None,
        weak_undefined_symbols: std::collections::HashSet::new(),
        caller_location_param: None,
        exc_ptr_slot: None,
        landing_pad_wrappers: Vec::new(),
        last_call_vref: None,
    };

    // Emit params into the entry block.
    if needs_sret {
        // Param 0 is the hidden SRET pointer. Capture it separately.
        let sret_param = ctx
            .builder
            .param(0, Type::Ptr(0), None, Origin::synthetic());
        ctx.sret_ptr = Some(sret_param);

        // Allocate a local stack slot for constructing the return value.
        // We deliberately do NOT reuse sret_param here: MIR blocks are
        // translated in numeric order, so the return block may be
        // translated before a call that writes to _0 via sret.  Using
        // a separate local keeps the return memcopy correct regardless
        // of translation order.
        let ret_local = mir::Local::from_usize(0);
        let ret_align = type_align(ctx.tcx, ret_mir_ty).unwrap_or(8) as u32;
        let local_slot = ctx
            .builder
            .stack_slot(ret_size as u32, ret_align, Origin::synthetic());
        ctx.locals.set(ret_local, local_slot);
        ctx.stack_locals.mark(ret_local);
    }
    ctx.translate_params();

    ctx.promote_locals_to_stack();

    // Translate each basic block in reverse-postorder.
    for bb in &rpo_order {
        let bb = *bb;
        let bb_data = &mir.basic_blocks[bb];
        let ir_block = ctx.block_map.get(bb);
        ctx.builder.switch_to_block(ir_block);
        if bb.as_usize() != 0 {
            ctx.current_mem = ctx.block_mem_args[bb.as_usize()].expect("block mem arg missing");
        }

        for stmt in &bb_data.statements {
            ctx.translate_statement(stmt);
        }
        if let Some(ref term) = bb_data.terminator {
            ctx.translate_terminator(term);
        }

        if !ctx.builder.current_block_is_terminated() {
            ctx.builder.unreachable(Origin::synthetic());
        }
    }

    // Emit landing-pad wrapper blocks for unwind cleanup.
    //
    // Each wrapper block is entered by the unwinder (not by normal control flow).
    // It captures the exception pointer via LandingPad, stores it to a
    // per-function stack slot, and branches to the actual MIR cleanup block.
    if !ctx.landing_pad_wrappers.is_empty() {
        let exc_slot = ctx.exc_ptr_slot.expect("exc_ptr_slot must be allocated");
        for (wrapper_block, cleanup_bb) in ctx.landing_pad_wrappers.clone() {
            ctx.builder.switch_to_block(wrapper_block);
            let exc_ptr = ctx.builder.landing_pad(Origin::synthetic());
            // Create a fresh mem token as a block arg (dead — no predecessor branches here)
            let wrapper_mem = ctx.builder.add_block_arg(wrapper_block, Type::Mem, None);
            let new_mem = ctx.builder.store(
                exc_ptr.into(),
                exc_slot.into(),
                8,
                wrapper_mem.into(),
                Origin::synthetic(),
            );
            let target = ctx.block_map.get(cleanup_bb);
            ctx.builder
                .br(target, vec![new_mem.into()], Origin::synthetic());
        }
    }

    ctx.builder.exit_region();

    // Destructure ctx to release the borrow on `func` (held by builder).
    let TranslationCtx {
        symbols,
        static_data,
        abi_metadata,
        referenced_instances,
        weak_undefined_symbols,
        ..
    } = ctx;

    Some(TranslationResult {
        func,
        symbols,
        static_data,
        abi_metadata,
        referenced_instances,
        weak_undefined_symbols,
    })
}
