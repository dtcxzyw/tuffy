//! MIR → tuffy IR translation.
//!
//! Translates rustc MIR into tuffy IR, supporting basic arithmetic,
//! control flow (branches, SwitchInt), and comparison operations.

mod call;
mod constant;
mod ctx;
mod intrinsic;
mod rvalue;
mod statement;
mod terminator;
pub(crate) mod types;

use ctx::{
    BlockMap, FatLocalMap, LocalMap, OverflowLocalMap, StackLocalSet, TranslationCtx,
    extract_param_names,
};
use types::*;

use tuffy_ir::types::{Annotation, IntAnnotation, IntSignedness};

use rustc_middle::mir::{self, BasicBlock, Operand, Rvalue, StatementKind, TerminatorKind};
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
) -> Option<TranslationResult<'tcx>> {
    // Skip partially substituted polymorphic instances — the symbol mangler
    // will panic if generic parameters are still present.
    if instance.args.has_non_region_param() {
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

    let ret_mir_ty = monomorphize(mir.local_decls[mir::RETURN_PLACE].ty);
    let ret_size = type_size(tcx, ret_mir_ty).unwrap_or(0);
    let ret_repr = repr_kind(tcx, ret_mir_ty);
    // In Rust/SysV ABI, Scalar and ScalarPair types ≤ 16 bytes are returned
    // in registers (RAX + RDX).  Only use SRET for types that exceed two
    // INTEGER-class registers.
    let needs_sret = match ret_repr {
        ReprKind::Zst => false,
        ReprKind::Scalar => false,
        ReprKind::ScalarPair => ret_size > 16,
        ReprKind::Memory => ret_size > 8,
    };

    // For SRET functions, the return type becomes Ptr (the SRET pointer is
    // returned in RAX per SysV ABI). Otherwise, use the semantic return type.
    // For structs ≤16 bytes, use Type::Int to capture register return.
    let (ret_ty, ret_ann) = if needs_sret {
        (Some(Type::Ptr(0)), None)
    } else {
        let ty = translate_ty(tcx, ret_mir_ty)
            .filter(|t| !matches!(t, Type::Unit))
            .or(if ret_size > 0 && ret_size <= 16 {
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
                    // For ScalarPair returns (e.g. fat pointers, Argument),
                    // use 64-bit annotation since the function returns the first
                    // 8 bytes in RAX; the remaining bytes are returned in RDX
                    // via ABI metadata (see terminator.rs).
                    if matches!(ret_repr, ReprKind::ScalarPair) {
                        int_annotation_for_bytes(8)
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
            if matches!(prk, ReprKind::ScalarPair | ReprKind::Scalar) && sz > 8 && sz <= 16 {
                // ScalarPair ≤ 16 bytes (e.g. fat pointer): two registers.
                params.push(Type::Int);
                param_anns.push(int_annotation_for_bytes(8));
                param_names.push(None);
                byval_sizes.push(None);
                params.push(Type::Int);
                param_anns.push(int_annotation_for_bytes((sz - 8) as u32));
                param_names.push(None);
                byval_sizes.push(None);
            } else if sz > 8 {
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
        // For >16 byte parameters, the caller passes a pointer per x86-64 ABI.
        let param_ty = if sz > 16 { Type::Ptr(0) } else { ir_ty };
        let param_ann = if sz > 16 {
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
        instance,
        current_mem: initial_mem,
        cast_fat_meta: FatLocalMap::new(),
        referenced_instances: Vec::new(),
        data_counter,
        vtable_cache,
        alloc_cache,
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

    // Pre-scan: find scalar locals assigned in more than one basic block.
    // These need stack slots so that mutations in loop bodies are visible
    // at loop headers (SSA values can't be mutated in place).
    {
        let mut assign_bb: Vec<Option<BasicBlock>> = vec![None; mir.local_decls.len()];
        // Function parameters are effectively assigned in the entry block
        // by translate_params.  Seed assign_bb so that any MIR assignment
        // to a parameter in a different block triggers stack promotion.
        let entry_bb = mir::BasicBlock::from_u32(0);
        for i in 0..mir.arg_count {
            let local = mir::Local::from_usize(i + 1);
            // Only seed non-stack params (large structs / two-reg structs
            // are already stack locals from translate_params).
            if !ctx.stack_locals.is_stack(local) {
                assign_bb[local.as_usize()] = Some(entry_bb);
            }
        }
        for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind
                    && place.projection.is_empty()
                {
                    let local = place.local;
                    // _0 (return place) is only skipped when it already has
                    // a stack slot (sret); otherwise it may need promotion
                    // when assigned in multiple BBs.
                    if local.as_usize() == 0 && ctx.stack_locals.is_stack(local) {
                        continue;
                    }
                    let ty = ctx.monomorphize(mir.local_decls[local].ty);
                    let size = type_size(ctx.tcx, ty).unwrap_or(0);
                    if size == 0 {
                        continue;
                    }
                    if let Some(prev_bb) = assign_bb[local.as_usize()] {
                        if prev_bb != bb && !ctx.stack_locals.is_stack(local) {
                            let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                            ctx.promote_local_to_stack(local, size, align);
                        }
                    } else {
                        assign_bb[local.as_usize()] = Some(bb);
                    }
                }
            }
            // Also check call terminators — they assign to a destination local.
            if let Some(terminator) = &bb_data.terminator
                && let TerminatorKind::Call { destination, .. } = &terminator.kind
                && destination.projection.is_empty()
            {
                let local = destination.local;
                if local.as_usize() == 0 && ctx.stack_locals.is_stack(local) {
                    // _0 with sret already has a stack slot — skip.
                } else {
                    let ty = ctx.monomorphize(mir.local_decls[local].ty);
                    let size = type_size(ctx.tcx, ty).unwrap_or(0);
                    if size > 0 {
                        if let Some(prev_bb) = assign_bb[local.as_usize()] {
                            if prev_bb != bb && !ctx.stack_locals.is_stack(local) {
                                let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                                ctx.promote_local_to_stack(local, size, align);
                            }
                        } else {
                            assign_bb[local.as_usize()] = Some(bb);
                        }
                    }
                }
            }
        }

        // Locals assigned via projections (e.g. `_0.0 = ...`) need stack
        // slots unconditionally — partial field writes require addressable memory.
        // Helper: promote a projected place's base local to stack.
        let promote_projected_place =
            |ctx: &mut TranslationCtx<'_, 'tcx>, place: &mir::Place<'tcx>| {
                if !place.projection.is_empty()
                    // A leading Deref means we write *through* the local (e.g.
                    // `(*_0).1 = ...`).  The local itself is a pointer — it must
                    // NOT be turned into a stack slot; doing so would create a
                    // fresh 8-byte slot while the pointer value is never stored.
                    && !matches!(
                        place.projection.first(),
                        Some(mir::PlaceElem::Deref)
                    )
                    && !ctx.stack_locals.is_stack(place.local)
                {
                    let local = place.local;
                    let ty = ctx.monomorphize(mir.local_decls[local].ty);
                    let size = type_size(ctx.tcx, ty).unwrap_or(0);
                    if size > 0 {
                        let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                        ctx.promote_local_to_stack(local, size, align);
                    }
                }
            };
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                    promote_projected_place(&mut ctx, place);
                }
            }
            // Also check Call terminators — they can assign to projected
            // destinations like `(_5.0: u64) = bswap(...)`.
            if let Some(terminator) = &bb_data.terminator
                && let TerminatorKind::Call { destination, .. } = &terminator.kind
            {
                promote_projected_place(&mut ctx, destination);
            }
        }

        // Allocate stack slots for all >8 byte composite locals (arrays, structs).
        // These must be stored in memory for proper argument decomposition.
        for local in mir.local_decls.indices() {
            if !ctx.stack_locals.is_stack(local) {
                let ty = ctx.monomorphize(mir.local_decls[local].ty);
                let size = type_size(ctx.tcx, ty).unwrap_or(0);
                if size > 8 && matches!(ty.kind(), ty::Array(..) | ty::Adt(..)) {
                    let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                    ctx.promote_local_to_stack(local, size, align);
                }
            }
        }

        // Promote locals used in a block that precedes their assignment
        // block in declaration order.
        let collect_used_locals = |op: &Operand<'tcx>| -> Option<mir::Local> {
            match op {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                _ => None,
            }
        };
        for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
            let mut used_locals = Vec::new();
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    // When the LHS has a leading Deref (e.g. `(*_7) = ...`),
                    // the base local is read to obtain the pointer address.
                    // It must be promoted if defined in a later block.
                    if !place.projection.is_empty()
                        && matches!(place.projection.first(), Some(mir::PlaceElem::Deref))
                    {
                        used_locals.push(place.local);
                    }
                    match rvalue {
                        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => {
                            used_locals.extend(collect_used_locals(op));
                        }
                        Rvalue::BinaryOp(_, box (a, b)) => {
                            used_locals.extend(collect_used_locals(a));
                            used_locals.extend(collect_used_locals(b));
                        }
                        Rvalue::Aggregate(_, ops) => {
                            for op in ops.iter() {
                                used_locals.extend(collect_used_locals(op));
                            }
                        }
                        Rvalue::Discriminant(place)
                        | Rvalue::Ref(_, _, place)
                        | Rvalue::RawPtr(_, place)
                        | Rvalue::CopyForDeref(place) => {
                            used_locals.push(place.local);
                        }
                        _ => {}
                    }
                }
            }
            if let Some(terminator) = &bb_data.terminator {
                match &terminator.kind {
                    TerminatorKind::SwitchInt { discr, .. } => {
                        used_locals.extend(collect_used_locals(discr));
                    }
                    TerminatorKind::Call { func, args, .. } => {
                        used_locals.extend(collect_used_locals(func));
                        for arg in args {
                            used_locals.extend(collect_used_locals(&arg.node));
                        }
                    }
                    TerminatorKind::Return => {
                        used_locals.push(mir::Local::from_usize(0));
                    }
                    _ => {}
                }
            }
            for local in used_locals {
                if local.as_usize() > 0 && local.as_usize() <= mir.arg_count {
                    continue;
                }
                if ctx.stack_locals.is_stack(local) {
                    continue;
                }
                if let Some(def_bb) = assign_bb[local.as_usize()]
                    && bb < def_bb
                {
                    let ty = ctx.monomorphize(mir.local_decls[local].ty);
                    let size = type_size(ctx.tcx, ty).unwrap_or(0);
                    if size > 0 {
                        let slot_size = (size as u32).max(1);
                        let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                        let slot = ctx
                            .builder
                            .stack_slot(slot_size, align, Origin::synthetic());
                        ctx.locals.set(local, slot);
                        ctx.stack_locals.mark(local);
                    }
                }
            }
        }
    }

    // Pre-scan: promote locals whose address is taken (Ref / RawPtr) to
    // stack locals.  Without this, `&mut x` inside a loop body would spill
    // the current value into a *new* temporary each iteration, losing
    // mutations made through the reference on previous iterations.
    {
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                    let referenced_local = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(place.local),
                        _ => None,
                    };
                    if let Some(local) = referenced_local {
                        if ctx.stack_locals.is_stack(local) {
                            continue;
                        }
                        let ty = ctx.monomorphize(mir.local_decls[local].ty);
                        let size = type_size(ctx.tcx, ty).unwrap_or(0);
                        let ty_align = type_align(ctx.tcx, ty).unwrap_or(1);
                        if size == 0 && ty_align <= 1 {
                            continue;
                        }
                        // ZSTs with alignment > 1 (e.g. #[repr(align(64))])
                        // need a stack slot so &val produces an aligned address.
                        if size == 0 {
                            let slot =
                                ctx.builder
                                    .stack_slot(0, ty_align as u32, Origin::synthetic());
                            ctx.locals.set(local, slot);
                            ctx.stack_locals.mark(local);
                            continue;
                        }
                        // Large params (size > 16 bytes) are passed by hidden pointer in
                        // the SysV ABI — regardless of whether rustc classifies them as
                        // Memory, ScalarPair, or Scalar.  The received value IS already
                        // the pointer to the data in the caller's stack frame.  Creating
                        // a new slot and only copying 8 bytes (the pointer itself) would
                        // lose the indirection, so just mark the local as stack-allocated
                        // without allocating a new slot.
                        // This optimization only applies to parameters, not to local
                        // variables — locals with size > 16 bytes need a real slot.
                        if size > 16 && local.as_usize() <= mir.arg_count {
                            ctx.stack_locals.mark(local);
                            continue;
                        }
                        let align = type_align(ctx.tcx, ty).unwrap_or(8) as u32;
                        let slot = ctx.builder.stack_slot(
                            (size as u32).max(1),
                            align,
                            Origin::synthetic(),
                        );
                        if let Some(prev) = ctx.locals.get(local) {
                            // For fat pointer ScalarPairs (&str, &[T], &dyn Trait), only
                            // store the first word (data pointer); the second word
                            // (metadata) is handled below via fat_locals.
                            // For non-fat-ptr ScalarPairs (e.g. (char, i64)), store the
                            // full size so the legalizer can emit both lo and hi stores.
                            // Scalar and Memory types store the full size.
                            let store_bytes = if is_fat_ptr(ctx.tcx, ty) {
                                8
                            } else {
                                size as u32
                            };
                            ctx.current_mem = ctx
                                .builder
                                .store(
                                    prev.into(),
                                    slot.into(),
                                    store_bytes,
                                    ctx.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            if let Some(meta) = ctx.fat_locals.get(local) {
                                let off8 = ctx.builder.iconst(
                                    8,
                                    64,
                                    IntSignedness::DontCare,
                                    Origin::synthetic(),
                                );
                                let meta_addr = ctx.builder.ptradd(
                                    slot.into(),
                                    off8.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                ctx.current_mem = ctx
                                    .builder
                                    .store(
                                        meta.into(),
                                        meta_addr.into(),
                                        8,
                                        ctx.current_mem.into(),
                                        Origin::synthetic(),
                                    )
                                    .raw();
                            }
                        }
                        ctx.locals.set(local, slot);
                        ctx.stack_locals.mark(local);
                    }
                }
            }
        }
    }

    // Pre-assign reference holders: when `_5 = &mut _2` (or &, &raw)
    // and `_2` is now a stack local, pre-assign `_5` to `_2`'s slot.
    // MIR passes (e.g. CheckAlignment) can reorder basic blocks so the
    // `_5 = &mut _2` definition may appear in a later-indexed block than
    // a use like `(*_5) = ...`.  Since the flat LocalMap has no per-block
    // scoping, pre-assigning the reference holder here ensures it is
    // visible in all blocks regardless of index order.
    {
        // Collect which locals have their address taken (via &_X or
        // &mut _X where _X has no projections).  These locals need
        // to be backed by stack slots so the address is stable.
        let mut addr_taken: std::collections::HashSet<mir::Local> =
            std::collections::HashSet::new();
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind
                    && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                    && place.projection.is_empty()
                {
                    addr_taken.insert(place.local);
                }
            }
        }
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind {
                    let ref_place = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(place),
                        _ => None,
                    };
                    if let Some(place) = ref_place
                        && place.projection.is_empty()
                        && dest.projection.is_empty()
                        && ctx.stack_locals.is_stack(place.local)
                        && ctx.locals.get(dest.local).is_none()
                        && let Some(slot) = ctx.locals.get(place.local)
                    {
                        // If this local's address is also taken (e.g.
                        // `_5 = &mut _0` where `_0 = &raw const _4`,
                        // then later `_7 = &mut _0`), we need to
                        // store the value in a proper stack slot
                        // so that the spill slot is initialized at
                        // function entry rather than lazily in a
                        // later block.
                        if addr_taken.contains(&dest.local) {
                            let dest_ty = ctx.monomorphize(mir.local_decls[dest.local].ty);
                            let dest_sz = type_size(ctx.tcx, dest_ty).unwrap_or(8) as u32;
                            let new_slot =
                                ctx.builder
                                    .stack_slot(dest_sz.max(8), 0, Origin::synthetic());
                            ctx.current_mem = ctx
                                .builder
                                .store(
                                    slot.into(),
                                    new_slot.into(),
                                    8,
                                    ctx.current_mem.into(),
                                    Origin::synthetic(),
                                )
                                .raw();
                            ctx.locals.set(dest.local, new_slot);
                            ctx.stack_locals.mark(dest.local);
                        } else {
                            ctx.locals.set(dest.local, slot);
                        }
                    }
                }
            }
        }
        // Second pass: handle `_X = &(mut) (*_Y)` where _Y was
        // pre-assigned above (it points to a stack local). Since
        // `*_Y` dereferences to the same stack slot, _X gets the
        // same address.
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind {
                    let ref_place = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(place),
                        _ => None,
                    };
                    if let Some(place) = ref_place
                        && place.projection.len() == 1
                        && matches!(place.projection[0], mir::PlaceElem::Deref)
                        && dest.projection.is_empty()
                        && ctx.locals.get(dest.local).is_none()
                        && let Some(slot) = ctx.locals.get(place.local)
                    {
                        ctx.locals.set(dest.local, slot);
                    }
                }
            }
        }
    }

    // Pre-allocate a stack slot for the return place (_0) when it is a
    // multi-word type (9-16 bytes, e.g. &str, &[T]) or a ScalarPair
    // (e.g. Option<u8>).  ScalarPair returns are always two-register
    // (RAX + RDX), so the return handler needs a stack slot to load
    // both scalars from.
    {
        let ret_local = mir::Local::from_usize(0);
        let ret_ty = ctx.monomorphize(mir.local_decls[ret_local].ty);
        let ret_size = type_size(ctx.tcx, ret_ty).unwrap_or(0);
        let ret_repr = repr_kind(ctx.tcx, ret_ty);
        let needs_slot = (ret_size > 8
            && ret_size <= 16
            && !matches!(ret_repr, ReprKind::Scalar if ret_size <= 8))
            || (matches!(ret_repr, ReprKind::ScalarPair) && ret_size > 0 && ret_size <= 8);
        if needs_slot && !ctx.stack_locals.is_stack(ret_local) {
            let ret_align = type_align(ctx.tcx, ret_ty).unwrap_or(8) as u32;
            let slot = ctx
                .builder
                .stack_slot(ret_size as u32, ret_align, Origin::synthetic());
            ctx.locals.set(ret_local, slot);
            ctx.stack_locals.mark(ret_local);
        }
    }

    // Pre-scan: if any block has an unwind cleanup action, allocate an
    // exception-pointer stack slot in the entry block.  This must happen
    // before the main translation loop so that the slot is available when
    // cleanup terminators are processed.
    {
        use mir::UnwindAction;
        let has_cleanup = mir.basic_blocks.iter().any(|bb| {
            if let Some(ref term) = bb.terminator {
                match &term.kind {
                    TerminatorKind::Call { unwind, .. } | TerminatorKind::Drop { unwind, .. } => {
                        matches!(unwind, UnwindAction::Cleanup(_))
                    }
                    _ => false,
                }
            } else {
                false
            }
        });
        if has_cleanup {
            let slot = ctx.builder.stack_slot(8, 0, Origin::synthetic());
            ctx.exc_ptr_slot = Some(slot);
        }
    }

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
