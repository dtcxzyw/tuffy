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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());

    builder.exit_region();

    assert_eq!(func.instructions.len(), 4);
    assert_eq!(func.blocks.len(), 1);
    assert_eq!(func.block_insts(entry).len(), 4);

    assert!(matches!(func.instructions[0].op, Op::Param(0)));
    assert!(matches!(func.instructions[1].op, Op::Param(1)));
    assert!(matches!(func.instructions[2].op, Op::Add(_, _)));
    assert!(matches!(func.instructions[3].op, Op::Ret(Some(_), _)));
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
        vec![],
        Some(Type::Int),
        s32,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
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
        mem0.into(),
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @add(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = add v1, v2\n\
         \x20\x20\x20\x20ret v3, v0\n\
         }"
    );
}

#[test]
fn display_named_params() {
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let a_sym = st.intern("a");
    let b_sym = st.intern("b");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        vec![Some(a_sym), Some(b_sym)],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @add(%a: int, %b: int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param %a\n\
         \x20\x20\x20\x20v2 = param %b\n\
         \x20\x20\x20\x20v3 = add v1, v2\n\
         \x20\x20\x20\x20ret v3, v0\n\
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
    let mem0 = builder.add_block_arg(bb0, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Gt, a.into(), b.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    builder.switch_to_block(bb1);
    builder.ret(Some(a.into()), mem0.into(), Origin::synthetic());

    builder.switch_to_block(bb2);
    builder.ret(Some(b.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @max(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = icmp.gt v1, v2\n\
         \x20\x20\x20\x20brif v3, bb1, bb2\n\
         \n\
         \x20\x20bb1:\n\
         \x20\x20\x20\x20ret v1, v0\n\
         \n\
         \x20\x20bb2:\n\
         \x20\x20\x20\x20ret v2, v0\n\
         }"
    );
}

#[test]
fn display_nested_loop_region() {
    let mut st = SymbolTable::new();
    let name = st.intern("factorial");
    let mut func = Function::new(name, vec![Type::Int], vec![], vec![], Some(Type::Int), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let bb0 = builder.create_block();
    let mem0 = builder.add_block_arg(bb0, Type::Mem);

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
    builder.ret(Some(acc.into()), mem0.into(), Origin::synthetic());

    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @factorial(int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = iconst 1\n\
         \x20\x20\x20\x20v3 = iconst 1\n\
         \x20\x20\x20\x20br bb1(v3, v2)\n\
         \n\
         \x20\x20region loop {\n\
         \x20\x20\x20\x20bb1(v5: int, v6: int):\n\
         \x20\x20\x20\x20\x20\x20v7 = icmp.le v6, v1\n\
         \x20\x20\x20\x20\x20\x20brif v7, bb2, bb3\n\
         \n\
         \x20\x20\x20\x20bb2:\n\
         \x20\x20\x20\x20\x20\x20v9 = mul v5, v6\n\
         \x20\x20\x20\x20\x20\x20v10 = sub v6, v2\n\
         \x20\x20\x20\x20\x20\x20continue v9, v10\n\
         \x20\x20}\n\
         \n\
         \x20\x20bb3:\n\
         \x20\x20\x20\x20ret v5, v0\n\
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let v_and = builder.and(a.into(), b.into(), None, Origin::synthetic());
    let v_or = builder.or(a.into(), b.into(), None, Origin::synthetic());
    let v_xor = builder.xor(v_and.into(), v_or.into(), None, Origin::synthetic());
    builder.ret(Some(v_xor.into()), mem0.into(), Origin::synthetic());
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let _v_shl = builder.shl(a.into(), b.into(), None, Origin::synthetic());
    let v_shr = builder.shr(a.into(), b.into(), None, Origin::synthetic());
    builder.ret(Some(v_shr.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @shifts(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = shl v1, v2\n\
         \x20\x20\x20\x20v4 = shr v1, v2\n\
         \x20\x20\x20\x20ret v4, v0\n\
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let v_div = builder.div(a.into(), b.into(), None, Origin::synthetic());
    let v_rem = builder.rem(a.into(), b.into(), None, Origin::synthetic());
    let v_add = builder.add(v_div.into(), v_rem.into(), None, Origin::synthetic());
    builder.ret(Some(v_add.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @divs(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = div v1, v2\n\
         \x20\x20\x20\x20v4 = rem v1, v2\n\
         \x20\x20\x20\x20v5 = add v3, v4\n\
         \x20\x20\x20\x20ret v5, v0\n\
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
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let off = builder.param(1, Type::Int, None, Origin::synthetic());
    let result = builder.ptradd(ptr.into(), off.into(), 0, Origin::synthetic());
    builder.ret(Some(result.into()), mem0.into(), Origin::synthetic());
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let p1 = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let p2 = builder.param(1, Type::Ptr(0), None, Origin::synthetic());
    let i = builder.param(2, Type::Int, None, Origin::synthetic());
    let _pa = builder.ptradd(p1.into(), i.into(), 0, Origin::synthetic());
    let _pd = builder.ptrdiff(p1.into(), p2.into(), Origin::synthetic());
    let _pi = builder.ptrtoint(p1.into(), Origin::synthetic());
    let _addr = builder.ptrtoaddr(p2.into(), Origin::synthetic());
    let _ip = builder.inttoptr(i.into(), 0, Origin::synthetic());
    builder.ret(Some(_pi.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @ptr_ops(ptr, ptr, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = param 2\n\
         \x20\x20\x20\x20v4 = ptradd v1, v3\n\
         \x20\x20\x20\x20v5 = ptrdiff v1, v2\n\
         \x20\x20\x20\x20v6 = ptrtoint v1\n\
         \x20\x20\x20\x20v7 = ptrtoaddr v2\n\
         \x20\x20\x20\x20v8 = inttoptr v3\n\
         \x20\x20\x20\x20ret v6, v0\n\
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
        vec![],
        Some(f32_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
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
    builder.ret(Some(v_abs.into()), mem0.into(), Origin::synthetic());
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
        vec![],
        Some(f64_ty.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
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
    builder.ret(Some(_v_cs.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @float_ops(f64, f64) -> f64 {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = fadd v1, v2\n\
         \x20\x20\x20\x20v4 = fsub v1, v2\n\
         \x20\x20\x20\x20v5 = fmul v1, v2\n\
         \x20\x20\x20\x20v6 = fdiv v1, v2\n\
         \x20\x20\x20\x20v7 = fneg v1\n\
         \x20\x20\x20\x20v8 = fabs v1\n\
         \x20\x20\x20\x20v9 = copysign v1, v2\n\
         \x20\x20\x20\x20ret v9, v0\n\
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, Type::Int, None, Origin::synthetic());

    let (mem1, v_la) = builder.load_atomic(
        ptr.into(),
        Type::Int,
        MemoryOrdering::Acquire,
        mem0.into(),
        Origin::synthetic(),
    );
    let mem2 = builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        mem1.into(),
        Origin::synthetic(),
    );
    let (mem3, _v_rmw) = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::SeqCst,
        mem2.into(),
        Origin::synthetic(),
    );
    let (mem4, v_cx) = builder.atomic_cmpxchg(
        ptr.into(),
        v_la.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        mem3.into(),
        Origin::synthetic(),
    );
    let mem5 = builder.fence(MemoryOrdering::SeqCst, mem4.into(), Origin::synthetic());
    builder.ret(Some(v_cx.into()), mem5.into(), Origin::synthetic());
    builder.exit_region();

    assert_eq!(func.instructions.len(), 8);
    assert!(matches!(func.instructions[2].op, Op::LoadAtomic(_, _, _)));
    assert!(matches!(
        func.instructions[3].op,
        Op::StoreAtomic(_, _, _, _)
    ));
    assert!(matches!(
        func.instructions[4].op,
        Op::AtomicRmw(_, _, _, _, _)
    ));
    assert!(matches!(
        func.instructions[5].op,
        Op::AtomicCmpXchg(_, _, _, _, _, _)
    ));
    assert!(matches!(func.instructions[6].op, Op::Fence(_, _)));
}

#[test]
fn display_atomic_ops() {
    let mut st = SymbolTable::new();
    let name = st.intern("atomic_ops");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0), Type::Int],
        vec![],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let ptr = builder.param(0, Type::Ptr(0), None, Origin::synthetic());
    let val = builder.param(1, Type::Int, None, Origin::synthetic());
    let (mem1, _la) = builder.load_atomic(
        ptr.into(),
        Type::Int,
        MemoryOrdering::Acquire,
        mem0.into(),
        Origin::synthetic(),
    );
    let mem2 = builder.store_atomic(
        val.into(),
        ptr.into(),
        MemoryOrdering::Release,
        mem1.into(),
        Origin::synthetic(),
    );
    let (mem3, _rmw) = builder.atomic_rmw(
        AtomicRmwOp::Add,
        ptr.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::SeqCst,
        mem2.into(),
        Origin::synthetic(),
    );
    let (mem4, _cx) = builder.atomic_cmpxchg(
        ptr.into(),
        _la.into(),
        val.into(),
        Type::Int,
        MemoryOrdering::AcqRel,
        MemoryOrdering::Acquire,
        mem3.into(),
        Origin::synthetic(),
    );
    let mem5 = builder.fence(MemoryOrdering::SeqCst, mem4.into(), Origin::synthetic());
    builder.ret(Some(_cx.into()), mem5.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @atomic_ops(ptr, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3, v4 = load.atomic.acquire v1, v0\n\
         \x20\x20\x20\x20v5 = store.atomic.release v2, v1, v3\n\
         \x20\x20\x20\x20v6, v7 = rmw.add.seqcst v1, v2, v5\n\
         \x20\x20\x20\x20v8, v9 = cmpxchg.acqrel.acquire v1, v4, v2, v6\n\
         \x20\x20\x20\x20v10 = fence.seqcst v8\n\
         \x20\x20\x20\x20ret v9, v10\n\
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
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
    builder.ret(Some(sel.into()), mem0.into(), Origin::synthetic());
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
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
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
    builder.ret(Some(b2i.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @sel(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = icmp.lt v1, v2\n\
         \x20\x20\x20\x20v4 = select v3, v1, v2\n\
         \x20\x20\x20\x20v5 = bool_to_int v3\n\
         \x20\x20\x20\x20ret v5, v0\n\
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
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let size = builder.param(0, Type::Int, None, Origin::synthetic());
    let addr = builder.symbol_addr(malloc_sym, Origin::synthetic());
    let (mem1, Some(result)) = builder.call(
        addr.into(),
        vec![size.into()],
        Type::Ptr(0),
        mem0.into(),
        None,
        Origin::synthetic(),
    ) else {
        panic!("expected non-void call result");
    };
    builder.ret(Some(result.into()), mem1.into(), Origin::synthetic());
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

    let mut func = Function::new(test_sym, vec![], vec![], vec![], None, None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    builder.symbol_addr(sym, Origin::synthetic());
    builder.ret(None, mem0.into(), Origin::synthetic());
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

// ---------------------------------------------------------------------------
// Verifier tests
// ---------------------------------------------------------------------------

use crate::verifier::{verify_function, verify_module};

/// Helper: build a valid "add" function and verify it passes.
fn build_valid_add_module() -> Module {
    let mut module = Module::new("test");
    let name = module.intern("add");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    let mem0 = b.add_block_arg(bb, Type::Mem);
    let a = b.param(0, Type::Int, None, Origin::synthetic());
    let p1 = b.param(1, Type::Int, None, Origin::synthetic());
    let sum = b.add(a.into(), p1.into(), None, Origin::synthetic());
    b.ret(Some(sum.into()), mem0.into(), Origin::synthetic());
    b.exit_region();
    module.add_function(func);
    module
}

#[test]
fn verify_valid_add_function() {
    let module = build_valid_add_module();
    let result = verify_module(&module);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_valid_multi_block() {
    let mut st = SymbolTable::new();
    let name = st.intern("max");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let bb1 = b.create_block();
    let bb2 = b.create_block();

    b.switch_to_block(bb0);
    let mem0 = b.add_block_arg(bb0, Type::Mem);
    let a = b.param(0, Type::Int, None, Origin::synthetic());
    let p1 = b.param(1, Type::Int, None, Origin::synthetic());
    let cmp = b.icmp(ICmpOp::Gt, a.into(), p1.into(), Origin::synthetic());
    b.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    b.switch_to_block(bb1);
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());

    b.switch_to_block(bb2);
    b.ret(Some(p1.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_valid_loop_region() {
    let mut st = SymbolTable::new();
    let name = st.intern("factorial");
    let mut func = Function::new(name, vec![Type::Int], vec![], vec![], Some(Type::Int), None);
    let mut b = Builder::new(&mut func);

    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let mem0 = b.add_block_arg(bb0, Type::Mem);
    let loop_region = b.create_region(RegionKind::Loop);
    b.enter_region(loop_region);
    let bb1 = b.create_block();
    let bb2 = b.create_block();
    b.exit_region();
    let bb3 = b.create_block();

    b.switch_to_block(bb0);
    let n = b.param(0, Type::Int, None, Origin::synthetic());
    let one = b.iconst(1, Origin::synthetic());
    let init = b.iconst(1, Origin::synthetic());
    b.br(bb1, vec![init.into(), one.into()], Origin::synthetic());

    let acc = b.add_block_arg(bb1, Type::Int);
    let i = b.add_block_arg(bb1, Type::Int);
    b.switch_to_block(bb1);
    let cmp = b.icmp(ICmpOp::Le, i.into(), n.into(), Origin::synthetic());
    b.brif(cmp.into(), bb2, vec![], bb3, vec![], Origin::synthetic());

    b.switch_to_block(bb2);
    let new_acc = b.mul(acc.into(), i.into(), None, Origin::synthetic());
    let new_i = b.sub(i.into(), one.into(), None, Origin::synthetic());
    b.continue_(vec![new_acc.into(), new_i.into()], Origin::synthetic());

    b.switch_to_block(bb3);
    b.ret(Some(acc.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}

#[test]
fn verify_detects_wrong_arith_operand_type() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_add");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem);
    let a = b.param(0, Type::Int, None, Origin::synthetic());
    let p1 = b.param(1, Type::Int, None, Origin::synthetic());
    // icmp returns Bool — passing it to Add should be flagged.
    let cmp = b.icmp(ICmpOp::Gt, a.into(), p1.into(), Origin::synthetic());
    b.add(cmp.into(), p1.into(), None, Origin::synthetic());
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("int arith lhs")),
        "should flag Bool operand in Add: {result}"
    );
}

#[test]
fn verify_detects_missing_terminator() {
    let mut st = SymbolTable::new();
    let name = st.intern("no_term");
    let mut func = Function::new(name, vec![Type::Int], vec![], vec![], Some(Type::Int), None);
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    b.param(0, Type::Int, None, Origin::synthetic());
    // No terminator
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("terminator")),
        "should flag missing terminator: {result}"
    );
}

#[test]
fn verify_detects_load_non_ptr() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_load");
    let mut func = Function::new(name, vec![Type::Int], vec![], vec![], Some(Type::Int), None);
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);

    let mem0 = b.add_block_arg(bb, Type::Mem);
    let a = b.param(0, Type::Int, None, Origin::synthetic());
    // Load from Int instead of Ptr — should be flagged.
    let v = b.load(
        a.into(),
        4,
        Type::Int,
        mem0.into(),
        None,
        Origin::synthetic(),
    );
    b.ret(Some(v.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("expected Ptr")),
        "should flag non-Ptr load operand: {result}"
    );
}

#[test]
fn verify_detects_branch_arg_count_mismatch() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_br");
    let mut func = Function::new(name, vec![Type::Int], vec![], vec![], Some(Type::Int), None);
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);

    let bb0 = b.create_block();
    let bb1 = b.create_block();
    let _arg = b.add_block_arg(bb1, Type::Int);

    b.switch_to_block(bb0);
    let mem0 = b.add_block_arg(bb0, Type::Mem);
    let a = b.param(0, Type::Int, None, Origin::synthetic());
    // Branch to bb1 which expects 1 arg, but pass 0.
    b.br(bb1, vec![], Origin::synthetic());

    b.switch_to_block(bb1);
    b.ret(Some(a.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("passes 0 args, expected 1")),
        "should flag branch arg count mismatch: {result}"
    );
}

#[test]
fn verify_detects_annotation_on_non_int() {
    let mut st = SymbolTable::new();
    let name = st.intern("bad_ann");
    let mut func = Function::new(
        name,
        vec![Type::Ptr(0)],
        vec![Some(Annotation::Signed(32))],
        vec![],
        Some(Type::Ptr(0)),
        None,
    );
    let mut b = Builder::new(&mut func);
    let root = b.create_region(RegionKind::Function);
    b.enter_region(root);
    let bb = b.create_block();
    b.switch_to_block(bb);
    let mem0 = b.add_block_arg(bb, Type::Mem);
    let p = b.param(0, Type::Ptr(0), None, Origin::synthetic());
    b.ret(Some(p.into()), mem0.into(), Origin::synthetic());
    b.exit_region();

    let result = verify_function(&func, &st);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("integer annotation on non-Int")),
        "should flag annotation on Ptr: {result}"
    );
}

#[test]
fn verify_detects_duplicate_function_names() {
    let mut module = Module::new("test");
    let name = module.intern("dup");
    let func1 = Function::new(name, vec![], vec![], vec![], None, None);
    let func2 = Function::new(name, vec![], vec![], vec![], None, None);
    module.add_function(func1);
    module.add_function(func2);

    let result = verify_module(&module);
    assert!(!result.is_ok(), "expected errors");
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message.contains("duplicate function name")),
        "should flag duplicate names: {result}"
    );
}

#[test]
fn display_min_max() {
    let mut st = SymbolTable::new();
    let name = st.intern("minmax");
    let mut func = Function::new(
        name,
        vec![Type::Int, Type::Int],
        vec![],
        vec![],
        Some(Type::Int),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem);
    let a = builder.param(0, Type::Int, None, Origin::synthetic());
    let b = builder.param(1, Type::Int, None, Origin::synthetic());
    let v_min = builder.min(a.into(), b.into(), None, Origin::synthetic());
    let v_max = builder.max(a.into(), b.into(), None, Origin::synthetic());
    let _sum = builder.add(v_min.into(), v_max.into(), None, Origin::synthetic());
    builder.ret(Some(_sum.into()), mem0.into(), Origin::synthetic());
    builder.exit_region();

    assert!(matches!(func.instructions[2].op, Op::Min(_, _)));
    assert!(matches!(func.instructions[3].op, Op::Max(_, _)));
    assert_eq!(func.instructions[2].ty, Type::Int);
    assert_eq!(func.instructions[3].ty, Type::Int);

    let output = format!("{}", func.display(&st));
    assert_eq!(
        output,
        "func @minmax(int, int) -> int {\n\
         \x20\x20bb0(v0: mem):\n\
         \x20\x20\x20\x20v1 = param 0\n\
         \x20\x20\x20\x20v2 = param 1\n\
         \x20\x20\x20\x20v3 = min v1, v2\n\
         \x20\x20\x20\x20v4 = max v1, v2\n\
         \x20\x20\x20\x20v5 = add v3, v4\n\
         \x20\x20\x20\x20ret v5, v0\n\
         }"
    );

    // Verify passes
    let result = verify_function(&func, &st);
    assert!(result.is_ok(), "expected no errors: {result}");
}
