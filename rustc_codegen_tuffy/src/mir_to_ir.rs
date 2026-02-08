//! Minimal MIR → tuffy IR translation.
//!
//! Only handles the subset needed for:
//!   fn add(a: i32, b: i32) -> i32 { a + b }

use rustc_middle::mir::{self, BinOp, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Instance, TyCtxt};

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::Origin;
use tuffy_ir::types::Type;
use tuffy_ir::value::ValueRef;

/// Translate a single MIR function instance to tuffy IR.
pub fn translate_function<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Option<Function> {
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
    let ret_ty = translate_ty(sig.output());

    let mut func = Function::new(&name, params, ret_ty);
    let mut builder = Builder::new(&mut func);
    let mut locals = LocalMap::new(mir.local_decls.len());

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    translate_params(mir, &mut builder, &mut locals);
    translate_body(mir, &mut builder, &mut locals);

    builder.exit_region();

    Some(func)
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

fn bit_width(ty: ty::Ty<'_>) -> Option<u32> {
    match ty.kind() {
        ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) => Some(32),
        _ => None,
    }
}

fn translate_params(mir: &mir::Body<'_>, builder: &mut Builder<'_>, locals: &mut LocalMap) {
    for i in 0..mir.arg_count {
        let local = mir::Local::from_usize(i + 1);
        let ty = mir.local_decls[local].ty;
        let val = builder.param(i as u32, Type::Int, Origin::synthetic());
        let bits = bit_width(ty).unwrap_or(32);
        let val = builder.assert_sext(val, bits, Origin::synthetic());
        locals.set(local, val);
    }
}

fn translate_body(mir: &mir::Body<'_>, builder: &mut Builder<'_>, locals: &mut LocalMap) {
    for (_bb_idx, bb_data) in mir.basic_blocks.iter_enumerated() {
        for stmt in &bb_data.statements {
            translate_statement(stmt, builder, locals);
        }
        if let Some(ref term) = bb_data.terminator {
            translate_terminator(term, builder, locals);
        }
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

fn translate_terminator(
    term: &mir::Terminator<'_>,
    builder: &mut Builder<'_>,
    locals: &mut LocalMap,
) {
    match &term.kind {
        TerminatorKind::Return => {
            let ret_local = mir::Local::from_usize(0);
            let val = locals.values[ret_local.as_usize()];
            builder.ret(val, Origin::synthetic());
        }
        TerminatorKind::Goto { .. } => {}
        _ => {}
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
                BinOp::Add | BinOp::AddWithOverflow => builder.add(l, r, Origin::synthetic()),
                BinOp::Sub | BinOp::SubWithOverflow => builder.sub(l, r, Origin::synthetic()),
                BinOp::Mul | BinOp::MulWithOverflow => builder.mul(l, r, Origin::synthetic()),
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
