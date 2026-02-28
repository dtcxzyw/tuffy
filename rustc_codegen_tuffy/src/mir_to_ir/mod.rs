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

use ctx::{BlockMap, FatLocalMap, LocalMap, StackLocalSet, TranslationCtx, extract_param_names};
use types::*;

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
type StaticDataVec = Vec<(SymbolId, Vec<u8>, Vec<(usize, String)>)>;

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
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    session: &CodegenSession,
    data_counter: &mut u64,
) -> Option<TranslationResult<'tcx>> {
    // Skip partially substituted polymorphic instances — the symbol mangler
    // will panic if generic parameters are still present.
    if instance.args.has_non_region_param() {
        return None;
    }
    // Cross-crate items only have MIR available if they are #[inline].
    // Non-inline external functions are already compiled in the rlib.
    // Exception: constructors (enum variant / struct) have synthesized MIR
    // via instance_mir even when is_mir_available returns false.
    if let ty::InstanceKind::Item(def_id) = instance.def
        && !def_id.is_local()
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

    let ret_mir_ty = monomorphize(mir.local_decls[mir::RETURN_PLACE].ty);
    // Detect whether this function returns a large struct via sret.
    // Must be computed before building params so the hidden sret pointer
    // is included in the parameter list.
    let use_sret = needs_indirect_return(tcx, ret_mir_ty);
    let _ret_size = type_size(tcx, ret_mir_ty);

    // When using sret, the ABI return value is the sret pointer (Ptr),
    // not the logical Rust return type.
    let ret_ty = if use_sret {
        Some(Type::Ptr(0))
    } else {
        translate_ty(ret_mir_ty).filter(|t| !matches!(t, Type::Unit))
    };
    let ret_ann = if use_sret {
        None
    } else {
        translate_annotation(ret_mir_ty)
    };

    let mut symbols = SymbolTable::new();
    let func_sym = symbols.intern(&name);

    // Build all-args name map first, then filter to match params.
    let all_names = extract_param_names(mir, &mut symbols);
    let mut param_names = Vec::new();

    // If sret, the first ABI parameter is a hidden pointer for the return value.
    if use_sret {
        params.push(Type::Ptr(0));
        param_anns.push(None);
        param_names.push(None);
    }

    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = monomorphize(mir.local_decls[local].ty);
        match translate_ty(ty) {
            Some(Type::Unit) | None => continue,
            Some(ir_ty) => {
                // System V AMD64 ABI struct parameter passing:
                // - > 16 bytes: passed by hidden pointer
                // - 9-16 bytes: passed in TWO registers
                // - <= 8 bytes: passed in one register
                let param_size = type_size(tcx, ty).unwrap_or(0);
                // Skip zero-sized ADTs (e.g. Global allocator) — they
                // don't occupy an ABI slot.
                if param_size == 0 {
                    continue;
                }
                let is_int_ty = matches!(ir_ty, Type::Int);
                if param_size > 16 && is_int_ty {
                    params.push(Type::Ptr(0));
                    param_anns.push(None);
                } else {
                    params.push(ir_ty);
                    param_anns.push(translate_annotation(ty));
                }
                param_names.push(all_names.get(i).copied().flatten());
                // Two-register structs (9-16 bytes) occupy two ABI slots.
                if param_size > 8 && param_size <= 16 && is_int_ty && !is_fat_ptr(tcx, ty) {
                    params.push(Type::Int);
                    param_anns.push(None);
                    param_names.push(None);
                }
                // Fat pointers (&str, &[T], &Path, etc.) occupy two ABI slots.
                if is_fat_ptr(tcx, ty) {
                    params.push(fat_ptr_meta_type(tcx, ty));
                    param_anns.push(None);
                    param_names.push(None);
                }
            }
        }
    }

    let mut func = Function::new(func_sym, params, param_anns, param_names, ret_ty, ret_ann);
    let mut builder = Builder::new(&mut func);
    let abi_metadata = session.new_metadata();

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    // Create IR blocks for all MIR basic blocks upfront so branches can
    // reference target blocks before they are translated.
    // Each block gets a Type::Mem block argument for MemSSA threading.
    let mut block_map = BlockMap::new(mir.basic_blocks.len());
    let mut block_mem_args = Vec::with_capacity(mir.basic_blocks.len());
    for (bb, _) in mir.basic_blocks.iter_enumerated() {
        let ir_block = builder.create_block();
        block_map.set(bb, ir_block);
        let mem_arg = builder.add_block_arg(ir_block, Type::Mem);
        block_mem_args.push(mem_arg);
    }

    let entry = block_map.get(BasicBlock::from_u32(0));
    builder.switch_to_block(entry);

    let initial_mem = block_mem_args[0];

    let mut ctx = TranslationCtx {
        tcx,
        mir,
        builder,
        locals: LocalMap::new(mir.local_decls.len()),
        fat_locals: FatLocalMap::new(),
        stack_locals: StackLocalSet::new(mir.local_decls.len()),
        symbols,
        static_data: Vec::new(),
        block_map,
        block_mem_args,
        abi_metadata,
        instance,
        sret_ptr: None,
        use_sret,
        current_mem: initial_mem,
        cast_fat_meta: FatLocalMap::new(),
        referenced_instances: Vec::new(),
        data_counter,
    };

    // Emit params into the entry block.
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
                    let ty = monomorphize(mir.local_decls[local].ty);
                    let size = type_size(tcx, ty).unwrap_or(0);
                    if size == 0 {
                        continue;
                    }
                    if let Some(prev_bb) = assign_bb[local.as_usize()] {
                        if prev_bb != bb && !ctx.stack_locals.is_stack(local) {
                            let slot = ctx
                                .builder
                                .stack_slot(std::cmp::max(size as u32, 1), Origin::synthetic());
                            // If the local already holds a value (e.g. a
                            // function parameter from translate_params),
                            // store it into the new stack slot so it isn't
                            // lost.
                            if let Some(old_val) = ctx.locals.get(local) {
                                ctx.current_mem = ctx.builder.store(
                                    old_val.into(),
                                    slot.into(),
                                    std::cmp::max(size as u32, 1),
                                    ctx.current_mem.into(),
                                    Origin::synthetic(),
                                );
                            }
                            ctx.locals.set(local, slot);
                            ctx.stack_locals.mark(local);
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
                    let ty = monomorphize(mir.local_decls[local].ty);
                    let size = type_size(tcx, ty).unwrap_or(0);
                    if size > 0 {
                        if let Some(prev_bb) = assign_bb[local.as_usize()] {
                            if prev_bb != bb && !ctx.stack_locals.is_stack(local) {
                                let slot = ctx
                                    .builder
                                    .stack_slot(std::cmp::max(size as u32, 1), Origin::synthetic());
                                if let Some(old_val) = ctx.locals.get(local) {
                                    ctx.current_mem = ctx.builder.store(
                                        old_val.into(),
                                        slot.into(),
                                        std::cmp::max(size as u32, 1),
                                        ctx.current_mem.into(),
                                        Origin::synthetic(),
                                    );
                                }
                                ctx.locals.set(local, slot);
                                ctx.stack_locals.mark(local);
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
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (place, _)) = &stmt.kind
                    && !place.projection.is_empty()
                    && !ctx.stack_locals.is_stack(place.local)
                {
                    let local = place.local;
                    let ty = monomorphize(mir.local_decls[local].ty);
                    let size = type_size(tcx, ty).unwrap_or(0);
                    if size > 0 {
                        let slot = ctx
                            .builder
                            .stack_slot(std::cmp::max(size as u32, 1), Origin::synthetic());
                        if let Some(old_val) = ctx.locals.get(local) {
                            ctx.current_mem = ctx.builder.store(
                                old_val.into(),
                                slot.into(),
                                std::cmp::max(size as u32, 1),
                                ctx.current_mem.into(),
                                Origin::synthetic(),
                            );
                        }
                        ctx.locals.set(local, slot);
                        ctx.stack_locals.mark(local);
                    }
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
                if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
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
                    let ty = monomorphize(mir.local_decls[local].ty);
                    let size = type_size(tcx, ty).unwrap_or(0);
                    if size > 0 {
                        let slot = ctx
                            .builder
                            .stack_slot(std::cmp::max(size as u32, 1), Origin::synthetic());
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
        use rustc_middle::mir::Rvalue;
        for bb_data in mir.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                    let referenced_local = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            Some(place.local)
                        }
                        _ => None,
                    };
                    if let Some(local) = referenced_local {
                        if local.as_usize() == 0 {
                            continue;
                        }
                        if ctx.stack_locals.is_stack(local) {
                            continue;
                        }
                        let ty = monomorphize(mir.local_decls[local].ty);
                        let size = type_size(tcx, ty).unwrap_or(0);
                        if size == 0 {
                            continue;
                        }
                        let slot = ctx
                            .builder
                            .stack_slot(std::cmp::max(size as u32, 1), Origin::synthetic());
                        if let Some(prev) = ctx.locals.get(local) {
                            ctx.current_mem = ctx.builder.store(
                                prev.into(),
                                slot.into(),
                                std::cmp::min(size as u32, 8),
                                ctx.current_mem.into(),
                                Origin::synthetic(),
                            );
                            if let Some(meta) = ctx.fat_locals.get(local) {
                                let off8 = ctx.builder.iconst(8, Origin::synthetic());
                                let meta_addr = ctx.builder.ptradd(
                                    slot.into(),
                                    off8.into(),
                                    0,
                                    Origin::synthetic(),
                                );
                                ctx.current_mem = ctx.builder.store(
                                    meta.into(),
                                    meta_addr.into(),
                                    8,
                                    ctx.current_mem.into(),
                                    Origin::synthetic(),
                                );
                            }
                        }
                        ctx.locals.set(local, slot);
                        ctx.stack_locals.mark(local);
                    }
                }
            }
        }
    }

    // Pre-allocate stack slots for i128/u128 locals.
    for local in mir.local_decls.indices() {
        if local.as_usize() == 0 || (local.as_usize() > 0 && local.as_usize() <= mir.arg_count) {
            continue;
        }
        if ctx.stack_locals.is_stack(local) {
            continue;
        }
        let ty = monomorphize(mir.local_decls[local].ty);
        if matches!(
            ty.kind(),
            ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128)
        ) {
            let slot = ctx.builder.stack_slot(16, Origin::synthetic());
            ctx.locals.set(local, slot);
            ctx.stack_locals.mark(local);
        }
    }

    // Pre-allocate a stack slot for the return place (_0) when it is a
    // multi-word type (9-16 bytes, e.g. &str, &[T]).
    if !use_sret {
        let ret_local = mir::Local::from_usize(0);
        let ret_ty = monomorphize(mir.local_decls[ret_local].ty);
        let ret_size = type_size(tcx, ret_ty).unwrap_or(0);
        if ret_size > 8 && ret_size <= 16 && !ctx.stack_locals.is_stack(ret_local) {
            let slot = ctx.builder.stack_slot(ret_size as u32, Origin::synthetic());
            ctx.locals.set(ret_local, slot);
            ctx.stack_locals.mark(ret_local);
        }
    }

    // Translate each basic block.
    for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
        let ir_block = ctx.block_map.get(bb);
        ctx.builder.switch_to_block(ir_block);
        if bb.as_usize() != 0 {
            ctx.current_mem = ctx.block_mem_args[bb.as_usize()];
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

    ctx.builder.exit_region();

    // Destructure ctx to release the borrow on `func` (held by builder).
    let TranslationCtx {
        symbols,
        static_data,
        abi_metadata,
        referenced_instances,
        ..
    } = ctx;

    Some(TranslationResult {
        func,
        symbols,
        static_data,
        abi_metadata,
        referenced_instances,
    })
}
