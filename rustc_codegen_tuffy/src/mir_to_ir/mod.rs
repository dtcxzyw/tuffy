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
    let ret_size = type_size(tcx, ret_mir_ty).unwrap_or(0);
    let needs_sret = ret_size > 16;

    // For SRET functions, the return type becomes Ptr (the SRET pointer is
    // returned in RAX per SysV ABI). Otherwise, use the semantic return type.
    let (ret_ty, ret_ann) = if needs_sret {
        (Some(Type::Ptr(0)), None)
    } else {
        let ty = translate_ty(tcx, ret_mir_ty).filter(|t| !matches!(t, Type::Unit));
        (ty, translate_annotation(ret_mir_ty))
    };

    let mut symbols = SymbolTable::new();
    let func_sym = symbols.intern(&name);

    // Build all-args name map first, then filter to match params.
    let all_names = extract_param_names(mir, &mut symbols);
    let mut param_names = Vec::new();

    // For SRET, prepend a hidden Ptr parameter (the return slot pointer).
    if needs_sret {
        params.push(Type::Ptr(0));
        param_anns.push(None);
        param_names.push(None);
    }

    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = monomorphize(mir.local_decls[local].ty);
        match translate_ty(tcx, ty) {
            Some(Type::Unit) | None => continue,
            Some(ir_ty) => {
                let sz = type_size(tcx, ty).unwrap_or(0);
                // For >16 byte parameters, the caller passes a pointer per x86-64 ABI.
                let param_ty = if sz > 16 { Type::Ptr(0) } else { ir_ty };
                // For composite types of 9–16 bytes that contain no floats
                // and are passed as an integer (not a pointer), annotate as
                // Unsigned(128) so the legalizer splits the param into two
                // 8-byte slots — matching the x86-64 SysV ABI which passes
                // such values in two integer registers.
                let param_ann = if sz > 16 { None } else { composite_param_annotation(tcx, ty) };
                params.push(param_ty);
                param_anns.push(param_ann);
                param_names.push(all_names.get(i).copied().flatten());
                // Fat pointer types (&str, &[T], &dyn Trait) are passed
                // as two register-sized values: data pointer + metadata
                // (length or vtable pointer).  Add a second Int param.
                if is_fat_ptr(tcx, ty) {
                    params.push(Type::Int);
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
        current_mem: initial_mem,
        cast_fat_meta: FatLocalMap::new(),
        referenced_instances: Vec::new(),
        data_counter,
        sret_ptr: None,
    };

    // Emit params into the entry block.
    if needs_sret {
        // Param 0 is the hidden SRET pointer. Capture it and assign to _0.
        let sret = ctx.builder.param(0, Type::Ptr(0), None, Origin::synthetic());
        ctx.sret_ptr = Some(sret);
        let ret_local = mir::Local::from_usize(0);
        ctx.locals.set(ret_local, sret);
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
                            ctx.promote_local_to_stack(local, size);
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
                                ctx.promote_local_to_stack(local, size);
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
                        ctx.promote_local_to_stack(local, size);
                    }
                }
            }
        }

        // Allocate stack slots for all >8 byte composite locals (arrays, structs).
        // These must be stored in memory for proper argument decomposition.
        for local in mir.local_decls.indices() {
            if !ctx.stack_locals.is_stack(local) {
                let ty = ctx.monomorphize(mir.local_decls[local].ty);
                let size = type_size(ctx.tcx, ty).unwrap_or(0);
                if size > 8 && matches!(ty.kind(), ty::Array(..) | ty::Adt(..)) {
                    ctx.promote_local_to_stack(local, size);
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
                    let ty = ctx.monomorphize(mir.local_decls[local].ty);
                    let size = type_size(ctx.tcx, ty).unwrap_or(0);
                    if size > 0 {
                        let slot_size = (size as u32).max(1);
                        let slot = ctx.builder.stack_slot(slot_size, Origin::synthetic());
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
                        if local.as_usize() == 0 {
                            continue;
                        }
                        if ctx.stack_locals.is_stack(local) {
                            continue;
                        }
                        let ty = ctx.monomorphize(mir.local_decls[local].ty);
                        let size = type_size(ctx.tcx, ty).unwrap_or(0);
                        if size == 0 {
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
                        let slot = ctx
                            .builder
                            .stack_slot((size as u32).max(1), Origin::synthetic());
                        if let Some(prev) = ctx.locals.get(local) {
                            // For fat pointer ScalarPairs (&str, &[T], &dyn Trait), only
                            // store the first word (data pointer); the second word
                            // (metadata) is handled below via fat_locals.
                            // For non-fat-ptr ScalarPairs (e.g. (char, i64)), store the
                            // full size so the legalizer can emit both lo and hi stores.
                            // Scalar and Memory types store the full size.
                            let store_bytes = if is_fat_ptr(ctx.tcx, ty) { 8 } else { size as u32 };
                            ctx.current_mem = ctx.builder.store(
                                prev.into(),
                                slot.into(),
                                store_bytes,
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

    // Pre-allocate a stack slot for the return place (_0) when it is a
    // multi-word type (9-16 bytes, e.g. &str, &[T]).
    {
        let ret_local = mir::Local::from_usize(0);
        let ret_ty = ctx.monomorphize(mir.local_decls[ret_local].ty);
        let ret_size = type_size(ctx.tcx, ret_ty).unwrap_or(0);
        if ret_size > 8
            && ret_size <= 16
            && !ctx.stack_locals.is_stack(ret_local)
            && !matches!(repr_kind(ctx.tcx, ret_ty), ReprKind::Scalar)
        {
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
