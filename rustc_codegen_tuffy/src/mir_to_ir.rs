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
}

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Option<TranslationResult> {
    let def_id = instance.def_id();
    if !def_id.is_local() {
        return None;
    }

    let inst_ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
    if !inst_ty.is_fn() {
        return None;
    }

    let mir = tcx.optimized_mir(def_id);
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
    let mut call_targets: HashMap<u32, String> = HashMap::new();

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
    translate_params(mir, &mut builder, &mut locals);

    // Translate each basic block.
    for (bb, bb_data) in mir.basic_blocks.iter_enumerated() {
        let ir_block = block_map.get(bb);
        builder.switch_to_block(ir_block);

        for stmt in &bb_data.statements {
            translate_statement(stmt, &mut builder, &mut locals);
        }
        if let Some(ref term) = bb_data.terminator {
            translate_terminator(
                tcx, term, &mut builder, &mut locals, &block_map, &mut call_targets,
            );
        }
    }

    builder.exit_region();

    Some(TranslationResult {
        func,
        call_targets,
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

fn translate_ty(ty: ty::Ty<'_>) -> Option<Type> {
    match ty.kind() {
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) => Some(Type::Int),
        _ => None,
    }
}

fn translate_annotation(ty: ty::Ty<'_>) -> Option<Annotation> {
    match ty.kind() {
        ty::Int(ty::IntTy::I32) => Some(Annotation::Signed(32)),
        ty::Uint(ty::UintTy::U32) => Some(Annotation::Unsigned(32)),
        _ => None,
    }
}

fn translate_params(mir: &mir::Body<'_>, builder: &mut Builder<'_>, locals: &mut LocalMap) {
    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = mir.local_decls[local].ty;
        let ann = translate_annotation(ty);
        let val = builder.param(i as u32, Type::Int, ann, Origin::synthetic());
        locals.set(local, val);
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

fn translate_statement(
    stmt: &mir::Statement<'_>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            if let Some(val) = translate_rvalue(rvalue, builder, locals) {
                locals.set(place.local, val);
            }
        }
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::Nop => {}
        _ => {}
    }
}

fn translate_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    term: &mir::Terminator<'tcx>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    block_map: &BlockMap,
    call_targets: &mut HashMap<u32, String>,
) {
    match &term.kind {
        TerminatorKind::Return => {
            let ret_local = mir::Local::from_usize(0);
            let val = locals.values[ret_local.as_usize()];
            builder.ret(val.map(|v| v.into()), Origin::synthetic());
        }
        TerminatorKind::Goto { target } => {
            let target_block = block_map.get(*target);
            builder.br(target_block, vec![], Origin::synthetic());
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            translate_switch_int(discr, targets, builder, locals, block_map);
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
            // Emit a trap-like return for now.
            builder.ret(None, Origin::synthetic());
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

            // Translate arguments to IR operands.
            let ir_args: Vec<tuffy_ir::instruction::Operand> = args
                .iter()
                .filter_map(|arg| {
                    translate_operand(&arg.node, builder, locals)
                        .map(|v| v.into())
                })
                .collect();

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

            // Branch to the continuation block if present.
            if let Some(target_bb) = target {
                let target_block = block_map.get(*target_bb);
                builder.br(target_block, vec![], Origin::synthetic());
            }
        }
        _ => {}
    }
}

fn translate_switch_int(
    discr: &Operand<'_>,
    targets: &mir::SwitchTargets,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
    block_map: &BlockMap,
) {
    let discr_val = match translate_operand(discr, builder, locals) {
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

fn translate_rvalue(
    rvalue: &Rvalue<'_>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
) -> Option<ValueRef> {
    match rvalue {
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            let l = translate_operand(lhs, builder, locals)?;
            let r = translate_operand(rhs, builder, locals)?;
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
                _ => return None,
            };
            Some(val)
        }
        Rvalue::Use(operand) => translate_operand(operand, builder, locals),
        _ => None,
    }
}

fn translate_operand(
    operand: &Operand<'_>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
) -> Option<ValueRef> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => locals.get(place.local),
        Operand::Constant(constant) => translate_const(constant, builder),
        _ => None,
    }
}

fn translate_const(constant: &mir::ConstOperand<'_>, builder: &mut Builder<'_>) -> Option<ValueRef> {
    let mir::Const::Val(val, ty) = constant.const_ else {
        return None;
    };
    match val {
        mir::ConstValue::Scalar(scalar) => {
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
        mir::ConstValue::ZeroSized => Some(builder.iconst(0, Origin::synthetic())),
        _ => None,
    }
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
                Instance::resolve(tcx, ty::TypingEnv::fully_monomorphized(), *def_id, args)
                    .ok()
                    .flatten()?;
            Some(tcx.symbol_name(instance).name.to_string())
        }
        _ => None,
    }
}
