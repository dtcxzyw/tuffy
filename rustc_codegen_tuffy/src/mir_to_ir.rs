//! MIR → tuffy IR translation.
//!
//! Translates rustc MIR into tuffy IR, supporting basic arithmetic,
//! control flow (branches, SwitchInt), and comparison operations.

use std::collections::HashMap;

use rustc_middle::mir::{self, BasicBlock, BinOp, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Instance, TyCtxt};

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{ICmpOp, Origin};
use tuffy_ir::types::{Annotation, Type};
use tuffy_ir::value::{BlockRef, ValueRef};

/// Result of MIR → IR translation.
pub struct TranslationResult {
    pub func: Function,
    /// Maps IR instruction index → callee symbol name for Call instructions.
    pub call_targets: HashMap<u32, String>,
    /// Maps IR instruction index → static data symbol name (for address loads).
    pub static_refs: HashMap<u32, String>,
    /// Static data blobs to emit in .rodata.
    pub static_data: Vec<(String, Vec<u8>)>,
    /// Maps IR instruction index → () for values that should capture RDX
    /// (the second return value from the preceding call).
    pub rdx_captures: HashMap<u32, ()>,
    /// Maps IR instruction index → source value index for explicit RDX moves.
    /// Used to move a fat return component into RDX before ret.
    pub rdx_moves: HashMap<u32, u32>,
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Option<TranslationResult> {
    let inst_ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
    if !inst_ty.is_fn() {
        return None;
    }

    let mir = tcx.instance_mir(instance.def);
    let name = tcx.symbol_name(instance).name.to_string();
    let sig = inst_ty.fn_sig(tcx);
    let sig = tcx.normalize_erasing_late_bound_regions(ty::TypingEnv::fully_monomorphized(), sig);

    let params: Vec<Type> = sig
        .inputs()
        .iter()
        .filter_map(|ty| translate_ty(*ty))
        .collect();
    let param_anns: Vec<Option<Annotation>> = sig
        .inputs()
        .iter()
        .filter_map(|ty| translate_ty(*ty).map(|_| translate_annotation(*ty)))
        .collect();
    let ret_ty = translate_ty(sig.output());
    let ret_ann = translate_annotation(sig.output());

    let mut func = Function::new(&name, params, param_anns, ret_ty, ret_ann);
    let mut builder = Builder::new(&mut func);
    let mut locals = LocalMap::new(mir.local_decls.len());
    let mut fat_locals = FatLocalMap::new();
    let mut call_targets: HashMap<u32, String> = HashMap::new();
    let mut static_refs: HashMap<u32, String> = HashMap::new();
    let mut static_data: Vec<(String, Vec<u8>)> = Vec::new();
    let mut rdx_captures: HashMap<u32, ()> = HashMap::new();
    let mut rdx_moves: HashMap<u32, u32> = HashMap::new();

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    // Create IR blocks for all MIR basic blocks upfront so branches can
    // reference target blocks before they are translated.
    let mut block_map = BlockMap::new(mir.basic_blocks.len());
    for (bb, _) in mir.basic_blocks.iter_enumerated() {
        let ir_block = builder.create_block();
        block_map.set(bb, ir_block);
    }

    // Emit params into the entry block.
    let entry = block_map.get(BasicBlock::from_u32(0));
    builder.switch_to_block(entry);
    translate_params(mir, &mut builder, &mut locals, &mut fat_locals);

    // Translate each basic block.
    for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
        let ir_block = block_map.get(bb);
        builder.switch_to_block(ir_block);

        for stmt in &bb_data.statements {
            translate_statement(
                tcx, stmt, &mut builder, &mut locals, &mut fat_locals,
                &mut static_refs, &mut static_data,
            );
        }
        if let Some(ref term) = bb_data.terminator {
            translate_terminator(
                tcx, term, &mut builder, &mut locals, &mut fat_locals,
                &block_map, &mut call_targets, &mut static_refs, &mut static_data,
                &mut rdx_captures, &mut rdx_moves,
            );
        }
    }

    builder.exit_region();

    Some(TranslationResult {
        func,
        call_targets,
        static_refs,
        static_data,
        rdx_captures,
        rdx_moves,
    })
}

struct LocalMap {
    values: Vec<Option<ValueRef>>,
}

impl LocalMap {
    fn new(count: usize) -> Self {
        Self {
            values: vec![None; count],
        }
    }

    fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values[local.as_usize()] = Some(val);
    }

    fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values[local.as_usize()]
    }
}

/// Tracks the "high" component of fat pointer locals (e.g., length for &str).
struct FatLocalMap {
    /// Maps MIR local index → high ValueRef (e.g., slice length).
    values: HashMap<usize, ValueRef>,
}

impl FatLocalMap {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    fn set(&mut self, local: mir::Local, val: ValueRef) {
        self.values.insert(local.as_usize(), val);
    }

    fn get(&self, local: mir::Local) -> Option<ValueRef> {
        self.values.get(&local.as_usize()).copied()
    }
}

fn translate_ty(ty: ty::Ty<'_>) -> Option<Type> {
    match ty.kind() {
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) | ty::Bool => Some(Type::Byte(1)),
        ty::Int(ty::IntTy::I16) | ty::Uint(ty::UintTy::U16) => Some(Type::Int),
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) | ty::Char => Some(Type::Int),
        ty::Int(ty::IntTy::I64)
        | ty::Uint(ty::UintTy::U64)
        | ty::Int(ty::IntTy::I128)
        | ty::Uint(ty::UintTy::U128)
        | ty::Int(ty::IntTy::Isize)
        | ty::Uint(ty::UintTy::Usize) => Some(Type::Int),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Type::Ptr(0)),
        ty::Tuple(fields) if fields.is_empty() => Some(Type::Int),
        ty::FnDef(..) => Some(Type::Int),
        ty::Never => Some(Type::Int),
        ty::Adt(..) | ty::Tuple(..) | ty::Array(..) | ty::Slice(..) | ty::Str => Some(Type::Int),
        _ => None,
    }
}

fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
    match ty.kind() {
        ty::Bool => Some(Annotation::Unsigned(8)),
        ty::Int(ty::IntTy::I8) => Some(Annotation::Signed(8)),
        ty::Uint(ty::UintTy::U8) => Some(Annotation::Unsigned(8)),
        ty::Int(ty::IntTy::I16) => Some(Annotation::Signed(16)),
        ty::Uint(ty::UintTy::U16) => Some(Annotation::Unsigned(16)),
        ty::Int(ty::IntTy::I32) | ty::Char => Some(Annotation::Signed(32)),
        ty::Uint(ty::UintTy::U32) => Some(Annotation::Unsigned(32)),
        ty::Int(ty::IntTy::I64) | ty::Int(ty::IntTy::Isize) => Some(Annotation::Signed(64)),
        ty::Uint(ty::UintTy::U64) | ty::Uint(ty::UintTy::Usize) => Some(Annotation::Unsigned(64)),
        ty::Int(ty::IntTy::I128) => Some(Annotation::Signed(128)),
        ty::Uint(ty::UintTy::U128) => Some(Annotation::Unsigned(128)),
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => Some(Annotation::Unsigned(64)),
        _ => None,
    }
}

fn translate_params(
    mir: &mir::Body<'_>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
) {
    let mut abi_idx: u32 = 0;
    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = mir.local_decls[local].ty;
        let ann = translate_annotation(ty);
        let val = builder.param(abi_idx, Type::Int, ann, Origin::synthetic());
        locals.set(local, val);
        abi_idx += 1;

        // Fat pointer types (&str, &[T]) occupy two ABI registers (ptr + metadata).
        if is_fat_ptr(ty) {
            let meta_val = builder.param(abi_idx, Type::Int, None, Origin::synthetic());
            fat_locals.set(local, meta_val);
            abi_idx += 1;
        }
    }
}

/// Check if a type is a fat pointer (e.g., &str, &[T]) that uses two registers at ABI level.
fn is_fat_ptr(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            matches!(inner.kind(), ty::Str | ty::Slice(..))
        }
        _ => false,
    }
}

/// Map from MIR BasicBlock to IR BlockRef.
struct BlockMap {
    blocks: Vec<Option<BlockRef>>,
}

impl BlockMap {
    fn new(count: usize) -> Self {
        Self {
            blocks: vec![None; count],
        }
    }

    fn set(&mut self, bb: BasicBlock, block: BlockRef) {
        self.blocks[bb.as_usize()] = Some(block);
    }

    fn get(&self, bb: BasicBlock) -> BlockRef {
        self.blocks[bb.as_usize()].expect("block not mapped")
    }
}

fn translate_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    stmt: &mir::Statement<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            if let Some(val) = translate_rvalue(
                tcx, rvalue, builder, locals, fat_locals,
                static_refs, static_data,
            ) {
                locals.set(place.local, val);
            }
            // Check if the rvalue produces a fat pointer (e.g., &str from ConstValue::Slice).
            if let Some(fat_val) = extract_fat_component(
                tcx, rvalue, builder, locals, fat_locals,
                static_refs, static_data,
            ) {
                fat_locals.set(place.local, fat_val);
            }
        }
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::Nop => {}
        _ => {}
    }
}

/// Extract the "high" component of a fat pointer rvalue.
///
/// Handles: ConstValue::Slice, Use/Cast of fat locals, and multi-field Aggregate.
fn extract_fat_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &FatLocalMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match rvalue {
        // Constant slice: extract the length metadata.
        Rvalue::Use(Operand::Constant(c)) => {
            if let mir::Const::Val(mir::ConstValue::Slice { alloc_id: _, meta }, _) = c.const_ {
                Some(builder.iconst(meta as i64, Origin::synthetic()))
            } else {
                None
            }
        }
        // Use of a fat local: propagate the fat component.
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            fat_locals.get(place.local)
        }
        // Cast (Transmute, PtrToPtr, etc.) of a fat local: propagate.
        Rvalue::Cast(_, operand, _) => {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    fat_locals.get(place.local)
                }
                _ => None,
            }
        }
        // Multi-field Aggregate: second field becomes the fat component.
        Rvalue::Aggregate(_, operands) if operands.len() >= 2 => {
            let second_op = operands.iter().nth(1).unwrap();
            translate_operand(tcx, second_op, builder, locals, static_refs, static_data)
        }
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    term: &mir::Terminator<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    block_map: &BlockMap,
    call_targets: &mut HashMap<u32, String>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
    rdx_captures: &mut HashMap<u32, ()>,
    rdx_moves: &mut HashMap<u32, u32>,
) {
    match &term.kind {
        TerminatorKind::Return => {
            let ret_local = mir::Local::from_usize(0);
            // If the return value has a fat component, emit a dummy iconst
            // that tells isel to move the fat value into RDX before ret.
            if let Some(fat_val) = fat_locals.get(ret_local) {
                let dummy = builder.iconst(0, Origin::synthetic());
                rdx_moves.insert(dummy.index(), fat_val.index());
            }
            let val = locals.values[ret_local.as_usize()];
            builder.ret(val.map(|v| v.into()), Origin::synthetic());
        }
        TerminatorKind::Goto { target } => {
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            translate_switch_int(
                tcx, discr, targets, builder, locals, block_map,
                static_refs, static_data,
            );
        }
        TerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } => {
            // Assert: if cond != expected, panic. For now, just branch to
            // the success target unconditionally (we'll add panic support later).
            let _ = (cond, expected);
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::Unreachable => {
            builder.ret(None, Origin::synthetic());
        }
        TerminatorKind::Drop { target, .. } => {
            // Skip drop glue for now — just branch to the target.
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::FalseEdge { real_target, .. } => {
            let target_block = block_map.get(*real_target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::FalseUnwind { real_target, .. } => {
            let target_block = block_map.get(*real_target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            // Resolve callee symbol name from the function operand's type.
            let callee_sym = resolve_call_symbol(tcx, func);

            // Translate arguments to IR operands, decomposing fat pointers.
            let mut ir_args: Vec<tuffy_ir::instruction::Operand> = Vec::new();
            for arg in args {
                if let Some(v) = translate_operand(
                    tcx, &arg.node, builder, locals,
                    static_refs, static_data,
                ) {
                    ir_args.push(v.into());
                    // If this arg is a Copy/Move of a fat local, also pass the high part.
                    if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                        if let Some(fat_v) = fat_locals.get(place.local) {
                            ir_args.push(fat_v.into());
                        }
                    }
                    // If this arg is a constant slice, the length was emitted
                    // right after the pointer. Check if it's in the constant.
                    if let Operand::Constant(c) = &arg.node {
                        if let mir::Const::Val(mir::ConstValue::Slice { meta, .. }, _) = c.const_ {
                            let len_val = builder.iconst(meta as i64, Origin::synthetic());
                            ir_args.push(len_val.into());
                        }
                    }
                }
            }

            // Emit a Call IR instruction. The callee operand is a dummy const
            // (the actual symbol is tracked in call_targets).
            let callee_val = builder.iconst(0, Origin::synthetic());
            let call_vref = builder.call(
                callee_val.into(),
                ir_args,
                Type::Int,
                None,
                Origin::synthetic(),
            );

            // Record the mapping from instruction index to symbol name.
            if let Some(sym) = callee_sym {
                call_targets.insert(call_vref.index(), sym);
            }

            // Store result in destination local.
            locals.set(destination.local, call_vref);

            // Capture RDX (second return value) for fat pointer returns.
            // Many std functions return two-register structs (e.g., fmt::Arguments).
            let rdx_val = builder.iconst(0, Origin::synthetic());
            rdx_captures.insert(rdx_val.index(), ());
            fat_locals.set(destination.local, rdx_val);

            // Branch to the continuation block if present.
            if let Some(target_bb) = target {
                let target_block = block_map.get(*target_bb);
                builder.br(target_block, vec![], Origin::synthetic());
            }
        }
        _ => {}
    }
}

fn translate_switch_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    discr: &Operand<'tcx>,
    targets: &mir::SwitchTargets,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    block_map: &BlockMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) {
    let discr_val = match translate_operand(tcx, discr, builder, locals, static_refs, static_data) {
        Some(v) => v,
        None => return,
    };

    let all_targets: Vec<_> = targets.iter().collect();
    let otherwise = targets.otherwise();

    if all_targets.len() == 1 {
        // Two-way branch: compare discriminant with the single value.
        let (test_val, target_bb) = all_targets[0];
        let const_val = builder.iconst(test_val as i64, Origin::synthetic());
        let cmp = builder.icmp(
            ICmpOp::Eq,
            discr_val.into(),
            const_val.into(),
            Origin::synthetic(),
        );
        let then_block = block_map.get(target_bb);
        let else_block = block_map.get(otherwise);
        builder.brif(
            cmp.into(),
            then_block,
            vec![],
            else_block,
            vec![],
            Origin::synthetic(),
        );
    } else {
        // Multi-way: chain of brif comparisons, fallthrough to otherwise.
        for (test_val, target_bb) in &all_targets {
            let const_val = builder.iconst(*test_val as i64, Origin::synthetic());
            let cmp = builder.icmp(
                ICmpOp::Eq,
                discr_val.into(),
                const_val.into(),
                Origin::synthetic(),
            );
            let then_block = block_map.get(*target_bb);
            let otherwise_block = block_map.get(otherwise);
            builder.brif(
                cmp.into(),
                then_block,
                vec![],
                otherwise_block,
                vec![],
                Origin::synthetic(),
            );
        }
        // Final fallthrough to otherwise.
        let otherwise_block = block_map.get(otherwise);
        builder.br(otherwise_block, vec![], Origin::synthetic());
    }
}

fn translate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    fat_locals: &mut FatLocalMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match rvalue {
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            let l = translate_operand(tcx, lhs, builder, locals, static_refs, static_data)?;
            let r = translate_operand(tcx, rhs, builder, locals, static_refs, static_data)?;
            let val = match op {
                BinOp::Add | BinOp::AddWithOverflow => {
                    builder.add(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::Sub | BinOp::SubWithOverflow => {
                    builder.sub(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::Mul | BinOp::MulWithOverflow => {
                    builder.mul(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::Eq => builder.icmp(ICmpOp::Eq, l.into(), r.into(), Origin::synthetic()),
                BinOp::Ne => builder.icmp(ICmpOp::Ne, l.into(), r.into(), Origin::synthetic()),
                BinOp::Lt => builder.icmp(ICmpOp::Slt, l.into(), r.into(), Origin::synthetic()),
                BinOp::Le => builder.icmp(ICmpOp::Sle, l.into(), r.into(), Origin::synthetic()),
                BinOp::Gt => builder.icmp(ICmpOp::Sgt, l.into(), r.into(), Origin::synthetic()),
                BinOp::Ge => builder.icmp(ICmpOp::Sge, l.into(), r.into(), Origin::synthetic()),
                BinOp::Shl | BinOp::ShlUnchecked => {
                    builder.shl(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::BitOr => {
                    builder.or(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::BitAnd => {
                    builder.and(l.into(), r.into(), None, Origin::synthetic())
                }
                BinOp::BitXor => {
                    builder.xor(l.into(), r.into(), None, Origin::synthetic())
                }
                _ => return None,
            };
            Some(val)
        }
        Rvalue::Use(operand) => translate_operand(tcx, operand, builder, locals, static_refs, static_data),
        Rvalue::Cast(_kind, operand, _ty) => {
            // For now, treat all casts as bitwise moves.
            translate_operand(tcx, operand, builder, locals, static_refs, static_data)
        }
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            // Taking a reference or raw pointer to a local.
            // Return the local's value (address) if available.
            locals.get(place.local)
        }
        Rvalue::Aggregate(_, operands) => {
            if operands.is_empty() {
                Some(builder.iconst(0, Origin::synthetic()))
            } else if let Some(first_op) = operands.iter().next() {
                translate_operand(tcx, first_op, builder, locals, static_refs, static_data)
            } else {
                Some(builder.iconst(0, Origin::synthetic()))
            }
        }
        Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand) => {
            // Extract metadata (e.g., slice length) from a fat pointer.
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    fat_locals.get(place.local)
                }
                _ => None,
            }
        }
        Rvalue::UnaryOp(mir::UnOp::Neg, operand) => {
            let v = translate_operand(tcx, operand, builder, locals, static_refs, static_data)?;
            let zero = builder.iconst(0, Origin::synthetic());
            Some(builder.sub(zero.into(), v.into(), None, Origin::synthetic()))
        }
        Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
            let v = translate_operand(tcx, operand, builder, locals, static_refs, static_data)?;
            let ones = builder.iconst(-1, Origin::synthetic());
            Some(builder.xor(v.into(), ones.into(), None, Origin::synthetic()))
        }
        Rvalue::Discriminant(place) => {
            locals.get(place.local)
        }
        _ => None,
    }
}

fn translate_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => locals.get(place.local),
        Operand::Constant(constant) => {
            translate_const(tcx, constant, builder, static_refs, static_data)
        }
        _ => None,
    }
}

fn translate_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
    builder: &mut Builder<'_>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    let mir::Const::Val(val, ty) = constant.const_ else {
        return None;
    };
    match val {
        mir::ConstValue::Scalar(scalar) => {
            translate_scalar(scalar, ty, builder)
        }
        mir::ConstValue::ZeroSized => Some(builder.iconst(0, Origin::synthetic())),
        mir::ConstValue::Slice { alloc_id, meta } => {
            translate_const_slice(tcx, alloc_id, meta, builder, static_refs, static_data)
        }
        _ => None,
    }
}

fn translate_scalar(
    scalar: mir::interpret::Scalar,
    ty: ty::Ty<'_>,
    builder: &mut Builder<'_>,
) -> Option<ValueRef> {
    let mir::interpret::Scalar::Int(int) = scalar else {
        return None;
    };
    let bits = int.to_bits(int.size());
    match ty.kind() {
        ty::Int(_) => {
            let val = bits as i128 as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Uint(_) => {
            let val = bits as i64;
            Some(builder.iconst(val, Origin::synthetic()))
        }
        ty::Bool => {
            let val = if bits != 0 { 1 } else { 0 };
            Some(builder.iconst(val, Origin::synthetic()))
        }
        _ => None,
    }
}

/// Translate a ConstValue::Slice (e.g., a string literal `&str`).
///
/// Emits the data bytes to .rodata and returns an IR constant whose index
/// is recorded in `static_refs` so that isel emits a RIP-relative LEA.
fn translate_const_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: rustc_middle::mir::interpret::AllocId,
    meta: u64,
    builder: &mut Builder<'_>,
    static_refs: &mut HashMap<u32, String>,
    static_data: &mut Vec<(String, Vec<u8>)>,
) -> Option<ValueRef> {
    let alloc = tcx.global_alloc(alloc_id).unwrap_memory();
    let alloc = alloc.inner();
    let bytes: Vec<u8> = alloc
        .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
        .to_vec();

    // Create a unique symbol name for this data blob.
    let sym = format!(".Lstr.{}", static_data.len());
    static_data.push((sym.clone(), bytes));

    // Emit a dummy constant whose index we record as a static ref.
    // Isel will emit LEA rip-relative for this value.
    let ptr_val = builder.iconst(0, Origin::synthetic());
    static_refs.insert(ptr_val.index(), sym);

    // Emit the length as a separate constant.
    let len_val = builder.iconst(meta as i64, Origin::synthetic());

    // Store both components. The "value" of this slice is the pointer;
    // the length is stored as the next local via the fat_locals mechanism.
    // For now, we return the pointer and rely on the caller to handle
    // the fat pointer decomposition.
    //
    // We use a convention: for a &str local, we store the pointer in
    // locals[local] and the length in fat_locals[local].
    let _ = len_val;

    // Return pointer; the caller must also retrieve the length.
    Some(ptr_val)
}

/// Resolve the callee symbol name from a Call terminator's function operand.
fn resolve_call_symbol<'tcx>(tcx: TyCtxt<'tcx>, func_op: &Operand<'tcx>) -> Option<String> {
    let ty = match func_op {
        Operand::Constant(c) => c.ty(),
        Operand::Copy(place) | Operand::Move(place) => {
            // Indirect call through a local — we can't resolve statically.
            let _ = place;
            return None;
        }
        _ => return None,
    };
    match ty.kind() {
        ty::FnDef(def_id, args) => {
            let instance =
                Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), *def_id, args)
                    .ok()
                    .flatten()?;
            Some(tcx.symbol_name(instance).name.to_string())
        }
        _ => None,
    }
}
