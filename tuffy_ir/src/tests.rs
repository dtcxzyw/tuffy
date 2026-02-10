//! Tests for the tuffy IR builder and display.

use crate::builder::Builder;
use crate::function::{Function, RegionKind};
use crate::instruction::{AtomicRmwOp, ICmpOp, Op, Operand, Origin};
use crate::module::{Module, SymbolTable};
use crate::types::{Annotation, FloatType, FpRewriteFlags, MemoryOrdering, Type};

#[test]
fn build_add_function() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(sum.into()), Origin::synthetic());

    builder.exit_region();

    assert_eq!(func.instructions.len(), 4);
    assert_eq!(func.blocks.len(), 1);
    assert_eq!(func.block_insts(entry).len(), 4);

    assert!(matches!(func.instructions[0].op, Op::Param(0)));
    assert!(matches!(func.instructions[1].op, Op::Param(1)));
    assert!(matches!(func.instructions[2].op, Op::Add(_, _)));
    assert!(matches!(func.instructions[3].op, Op::Ret(Some(_))));
}

#[test]
fn build_with_annotations() {
    let s32 = Some(Annotation::Signed(32));
    let mut st = SymbolTable::new();
    let name = st.intern("add_i32");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![s32, s32],
        Some(Type::Int),
        s32,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, s32, Origin::synthetic());
    let b = builder.param(1, Type::Int, s32, Origin::synthetic());
    let sum = builder.add(
        Operand::annotated(a, Annotation::Signed(32)),
        Operand::annotated(b, Annotation::Signed(32)),
        s32,
        Origin::synthetic(),
    );
    builder.ret(
        Some(Operand::annotated(sum, Annotation::Signed(32))),
        Origin::synthetic(),
    );

    builder.exit_region();

    assert_eq!(func.instructions.len(), 4);
    assert_eq!(
        func.instructions[0].result_annotation,
        Some(Annotation::Signed(32))
    );
}

#[test]
fn display_add_function() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(sum.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @add(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = add v0, v1\n\
         \x20\x20\x20\x20ret v2\n\
         }"
    );
}

#[test]
fn display_multi_block_branch() {
    let mut st = SymbolTable::new();
    let name = st.intern("max");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let bb0 = builder.create_block();
    let bb1 = builder.create_block();
    let bb2 = builder.create_block();

    builder.switch_to_block(bb0);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Gt, a.into(), b.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    builder.switch_to_block(bb1);
    builder.ret(Some(a.into()), Origin::synthetic());

    builder.switch_to_block(bb2);
    builder.ret(Some(b.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @max(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = icmp.gt v0, v1\n\
         \x20\x20\x20\x20brif v2, bb1, bb2\n\
         \n\
         \x20\x20bb1:\n\
         \x20\x20\x20\x20ret v0\n\
         \n\
         \x20\x20bb2:\n\
         \x20\x20\x20\x20ret v1\n\
         }"
    );
}

#[test]
fn display_nested_loop_region() {
    let mut st = SymbolTable::new();
    let name = st.intern("factorial");
    let mut func = Function::new(name, vec![Type::Int], vec![], Some(Type::Int), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let bb0 = builder.create_block();

    let loop_region = builder.create_region(RegionKind::Loop);
    builder.enter_region(loop_region);
    let bb1 = builder.create_block();
    let bb2 = builder.create_block();
    builder.exit_region();

    let bb3 = builder.create_block();

    // bb0: entry
    builder.switch_to_block(bb0);
    let n = builder.param(0, Type::Int, None, Origin::synthetic());
    let one = builder.iconst(1, Origin::synthetic());
    let init_acc = builder.iconst(1, Origin::synthetic());
    builder.br(bb1, vec![init_acc.into(), one.into()], Origin::synthetic());

    // bb1: loop header with block args
    let acc = builder.add_block_arg(bb1, Type::Int);
    let i = builder.add_block_arg(bb1, Type::Int);
    builder.switch_to_block(bb1);
    let cmp = builder.icmp(ICmpOp::Le, i.into(), n.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb2, vec![], bb3, vec![], Origin::synthetic());

    // bb2: loop body
    builder.switch_to_block(bb2);
    let new_acc = builder.mul(acc.into(), i.into(), None, Origin::synthetic());
    let new_i = builder.sub(i.into(), one.into(), None, Origin::synthetic());
    builder.continue_(vec![new_acc.into(), new_i.into()], Origin::synthetic());

    // bb3: after loop
    builder.switch_to_block(bb3);
    builder.ret(Some(acc.into()), Origin::synthetic());

    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @factorial(int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = iconst 1\n\
         \x20\x20\x20\x20v2 = iconst 1\n\
         \x20\x20\x20\x20br bb1(v2, v1)\n\
         \n\
         \x20\x20region loop {\n\
         \x20\x20\x20\x20bb1(v4: int, v5: int):\n\
         \x20\x20\x20\x20\x20\x20v6 = icmp.le v5, v0\n\
         \x20\x20\x20\x20\x20\x20brif v6, bb2, bb3\n\
         \n\
         \x20\x20\x20\x20bb2:\n\
         \x20\x20\x20\x20\x20\x20v8 = mul v4, v5\n\
         \x20\x20\x20\x20\x20\x20v9 = sub v5, v1\n\
         \x20\x20\x20\x20\x20\x20continue v8, v9\n\
         \x20\x20}\n\
         \n\
         \x20\x20bb3:\n\
         \x20\x20\x20\x20ret v4\n\
         }"
    );
}

#[test]
fn build_bitwise_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("bitwise");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let v_and = builder.and(a.into(), b.into(), None, Origin::synthetic());
    let v_or = builder.or(a.into(), b.into(), None, Origin::synthetic());
    let v_xor = builder.xor(v_and.into(), v_or.into(), None, Origin::synthetic());
    builder.ret(Some(v_xor.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 6);
    assert!(matches!(func.instructions[2].op, Op::And(_, _)));
    assert!(matches!(func.instructions[3].op, Op::Or(_, _)));
    assert!(matches!(func.instructions[4].op, Op::Xor(_, _)));
}

#[test]
fn display_shift_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("shifts");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let _v_shl = builder.shl(a.into(), b.into(), None, Origin::synthetic());
    let v_shr = builder.shr(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(v_shr.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @shifts(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = shl v0, v1\n\
         \x20\x20\x20\x20v3 = shr v0, v1\n\
         \x20\x20\x20\x20ret v3\n\
         }"
    );
}

#[test]
fn display_division_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("divs");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let v_div = builder.div(a.into(), b.into(), None, Origin::synthetic());
    let v_rem = builder.rem(a.into(), b.into(), None, Origin::synthetic());
    let v_add = builder.add(v_div.into(), v_rem.into(), None, Origin::synthetic());
    builder.ret(Some(v_add.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @divs(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = div v0, v1\n\
         \x20\x20\x20\x20v3 = rem v0, v1\n\
         \x20\x20\x20\x20v4 = add v2, v3\n\
         \x20\x20\x20\x20ret v4\n\
         }"
    );
}

#[test]
fn build_ptradd() {
    let mut st = SymbolTable::new();
    let name = st.intern("ptr_arith");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Int],
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let off = builder.param(1, Type::Int, None, Origin::synthetic());
    let result = builder.ptradd(ptr.into(), off.into(), 0, Origin::synthetic());
    builder.ret(Some(result.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 4);
    assert!(matches!(func.instructions[2].op, Op::PtrAdd(_, _)));
    assert_eq!(func.instructions[2].ty, Type::Ptr(0));
}

#[test]
fn display_pointer_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("ptr_ops");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Ptr(0), Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let p1 = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let p2 = builder.param(1, Type::Ptr(0), None, Origin::synthetic());
    let i = builder.param(2, Type::Int, None, Origin::synthetic());
    let _pa = builder.ptradd(p1.into(), i.into(), 0, Origin::synthetic());
    let _pd = builder.ptrdiff(p1.into(), p2.into(), Origin::synthetic());
    let _pi = builder.ptrtoint(p1.into(), Origin::synthetic());
    let _addr = builder.ptrtoaddr(p2.into(), Origin::synthetic());
    let _ip = builder.inttoptr(i.into(), 0, Origin::synthetic());
    builder.ret(Some(_pi.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @ptr_ops(ptr, ptr, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = param 2\n\
         \x20\x20\x20\x20v3 = ptradd v0, v2\n\
         \x20\x20\x20\x20v4 = ptrdiff v0, v1\n\
         \x20\x20\x20\x20v5 = ptrtoint v0\n\
         \x20\x20\x20\x20v6 = ptrtoaddr v1\n\
         \x20\x20\x20\x20v7 = inttoptr v2\n\
         \x20\x20\x20\x20ret v5\n\
         }"
    );
}

#[test]
fn build_float_binary_ops() {
    let f32_ty = Type::Float(FloatType::F32);
    let mut st = SymbolTable::new();
    let name = st.intern("float_bin");
    let mut func = Function::new(
        name,
        vec![f32_ty.clone(), f32_ty.clone()],
        vec![],
        Some(f32_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, f32_ty.clone(), None, Origin::synthetic());
    let b = builder.param(1, f32_ty.clone(), None, Origin::synthetic());
    let flags = FpRewriteFlags::default();
    let v_fadd = builder.fadd(
        a.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fsub = builder.fsub(
        a.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fmul = builder.fmul(
        v_fadd.into(),
        v_fsub.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_fdiv = builder.fdiv(
        v_fmul.into(),
        b.into(),
        flags,
        f32_ty.clone(),
        Origin::synthetic(),
    );
    let v_csign = builder.copysign(v_fdiv.into(), a.into(), f32_ty.clone(), Origin::synthetic());
    let v_neg = builder.fneg(v_csign.into(), f32_ty.clone(), Origin::synthetic());
    let v_abs = builder.fabs(v_neg.into(), f32_ty.clone(), Origin::synthetic());
    builder.ret(Some(v_abs.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 10);
    assert!(matches!(func.instructions[2].op, Op::FAdd(_, _, _)));
    assert!(matches!(func.instructions[3].op, Op::FSub(_, _, _)));
    assert!(matches!(func.instructions[4].op, Op::FMul(_, _, _)));
    assert!(matches!(func.instructions[5].op, Op::FDiv(_, _, _)));
    assert!(matches!(func.instructions[6].op, Op::CopySign(_, _)));
    assert!(matches!(func.instructions[7].op, Op::FNeg(_)));
    assert!(matches!(func.instructions[8].op, Op::FAbs(_)));
    assert_eq!(func.instructions[2].ty, f32_ty);
}

#[test]
fn display_float_ops() {
    let f64_ty = Type::Float(FloatType::F64);
    let mut st = SymbolTable::new();
    let name = st.intern("float_ops");
    let mut func = Function::new(
        name,
        vec![f64_ty.clone(), f64_ty.clone()],
        vec![],
        Some(f64_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, f64_ty.clone(), None, Origin::synthetic());
    let b = builder.param(1, f64_ty.clone(), None, Origin::synthetic());
    let flags = FpRewriteFlags::default();
    let _v_fadd = builder.fadd(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fsub = builder.fsub(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fmul = builder.fmul(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_fdiv = builder.fdiv(
        a.into(),
        b.into(),
        flags,
        f64_ty.clone(),
        Origin::synthetic(),
    );
    let _v_neg = builder.fneg(a.into(), f64_ty.clone(), Origin::synthetic());
    let _v_abs = builder.fabs(a.into(), f64_ty.clone(), Origin::synthetic());
    let _v_cs = builder.copysign(a.into(), b.into(), f64_ty.clone(), Origin::synthetic());
    builder.ret(Some(_v_cs.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @float_ops(f64, f64) -> f64 {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = fadd v0, v1\n\
         \x20\x20\x20\x20v3 = fsub v0, v1\n\
         \x20\x20\x20\x20v4 = fmul v0, v1\n\
         \x20\x20\x20\x20v5 = fdiv v0, v1\n\
         \x20\x20\x20\x20v6 = fneg v0\n\
         \x20\x20\x20\x20v7 = fabs v0\n\
         \x20\x20\x20\x20v8 = copysign v0, v1\n\
         \x20\x20\x20\x20ret v8\n\
         }"
    );
}

#[test]
fn build_atomic_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_test");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, Type::Int, None, Origin::synthetic());

    let v_la = builder.load_atomic(
        ptr.into(),
        Type::Int,
        MemoryOrdering::Acquire,
        Origin::synthetic(),
    );
    builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        Origin::synthetic(),
    );
    let _v_rmw = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::SeqCst,
        Origin::synthetic(),
    );
    let v_cx = builder.atomic_cmpxchg(
        ptr.into(),
        v_la.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        Origin::synthetic(),
    );
    builder.fence(MemoryOrdering::SeqCst, Origin::synthetic());
    builder.ret(Some(v_cx.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 8);
    assert!(matches!(func.instructions[2].op, Op::LoadAtomic(_, _)));
    assert!(matches!(func.instructions[3].op, Op::StoreAtomic(_, _, _)));
    assert!(matches!(func.instructions[4].op, Op::AtomicRmw(_, _, _, _)));
    assert!(matches!(
        func.instructions[5].op,
        Op::AtomicCmpXchg(_, _, _, _, _)
    ));
    assert!(matches!(func.instructions[6].op, Op::Fence(_)));
}

#[test]
fn display_atomic_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_ops");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, Type::Int, None, Origin::synthetic());
    let _la = builder.load_atomic(
        ptr.into(),
        Type::Int,
        MemoryOrdering::Acquire,
        Origin::synthetic(),
    );
    builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        Origin::synthetic(),
    );
    let _rmw = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::SeqCst,
        Origin::synthetic(),
    );
    let _cx = builder.atomic_cmpxchg(
        ptr.into(),
        _la.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        Origin::synthetic(),
    );
    builder.fence(MemoryOrdering::SeqCst, Origin::synthetic());
    builder.ret(Some(_cx.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @atomic_ops(ptr, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = load.atomic.acquire v0\n\
         \x20\x20\x20\x20store.atomic.release v1, v0\n\
         \x20\x20\x20\x20v4 = rmw.add.seqcst v0, v1\n\
         \x20\x20\x20\x20v5 = cmpxchg.acqrel.acquire v0, v2, v1\n\
         \x20\x20\x20\x20fence.seqcst\n\
         \x20\x20\x20\x20ret v5\n\
         }"
    );
}

#[test]
fn build_select_and_bool_to_int() {
    let mut st = SymbolTable::new();
    let name = st.intern("select_test");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Gt, a.into(), b.into(), Origin::synthetic());
    let sel = builder.select(
        cmp.into(),
        a.into(),
        b.into(),
        Type::Int,
        Origin::synthetic(),
    );
    let b2i = builder.bool_to_int(cmp.into(), Origin::synthetic());
    let _sum = builder.add(sel.into(), b2i.into(), None, Origin::synthetic());
    builder.ret(Some(sel.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions[2].ty, Type::Bool);
    assert_eq!(func.instructions[3].ty, Type::Int);
    assert_eq!(func.instructions[4].ty, Type::Int);
    assert!(matches!(
        func.instructions[2].op,
        Op::ICmp(ICmpOp::Gt, _, _)
    ));
    assert!(matches!(func.instructions[3].op, Op::Select(_, _, _)));
    assert!(matches!(func.instructions[4].op, Op::BoolToInt(_)));
}

#[test]
fn display_select_and_bool_to_int() {
    let mut st = SymbolTable::new();
    let name = st.intern("sel");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Lt, a.into(), b.into(), Origin::synthetic());
    let _sel = builder.select(
        cmp.into(),
        a.into(),
        b.into(),
        Type::Int,
        Origin::synthetic(),
    );
    let b2i = builder.bool_to_int(cmp.into(), Origin::synthetic());
    builder.ret(Some(b2i.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @sel(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = icmp.lt v0, v1\n\
         \x20\x20\x20\x20v3 = select v2, v0, v1\n\
         \x20\x20\x20\x20v4 = bool_to_int v2\n\
         \x20\x20\x20\x20ret v4\n\
         }"
    );
}

#[test]
fn symbol_table_intern_and_resolve() {
    let mut st = SymbolTable::new();
    let id1 = st.intern("malloc");
    let id2 = st.intern("free");
    let id3 = st.intern("malloc"); // duplicate

    assert_eq!(id1, id3);
    assert_ne!(id1, id2);
    assert_eq!(st.resolve(id1), "malloc");
    assert_eq!(st.resolve(id2), "free");
    assert_eq!(st.len(), 2);
}

#[test]
fn build_symbol_addr() {
    let mut module = Module::new("test");
    let malloc_sym = module.intern("malloc");
    let caller_sym = module.intern("caller");

    let mut func = Function::new(
        caller_sym,
        vec![Type::Int],
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let size = builder.param(0, Type::Int, None, Origin::synthetic());
    let addr = builder.symbol_addr(malloc_sym, Origin::synthetic());
    let result = builder.call(
        addr.into(),
        vec![size.into()],
        Type::Ptr(0),
        None,
        Origin::synthetic(),
    );
    builder.ret(Some(result.into()), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 4);
    assert!(matches!(func.instructions[1].op, Op::SymbolAddr(_)));
    assert_eq!(func.instructions[1].ty, Type::Ptr(0));

    module.add_function(func);
    let output = format!("{module}");
    assert!(output.contains("symbol_addr @malloc"));
}

#[test]
fn display_symbol_addr_without_symbols() {
    let mut st = SymbolTable::new();
    let sym = st.intern("puts");
    let test_sym = st.intern("test");

    let mut func = Function::new(test_sym, vec![], vec![], None, None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    builder.symbol_addr(sym, Origin::synthetic());
    builder.ret(None, Origin::synthetic());
    builder.exit_region();

    // Without module context, SymbolAddr and function name show raw ids
    let output = format!("{func}");
    assert!(output.contains("symbol_addr $0"));
    assert!(output.contains("func $1"));
}

#[test]
fn module_static_data() {
    let mut module = Module::new("test_module");
    let sym = module.intern(".Lstr.0");
    module.add_static_data(sym, b"hello".to_vec());

    assert_eq!(module.static_data.len(), 1);
    assert_eq!(module.resolve(module.static_data[0].name), ".Lstr.0");
    assert_eq!(module.static_data[0].data, b"hello");
}
