//! Tests for the tuffy IR builder and display.

use crate::builder::Builder;
use crate::function::{Function, RegionKind};
use crate::instruction::{ICmpOp, Op, Operand, Origin};
use crate::types::{Annotation, Type};

#[test]
fn build_add_function() {
    let mut func = Function::new(
        "add",
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
    let mut func = Function::new(
        "add_i32",
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
    let mut func = Function::new(
        "add",
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

    let output = format!("{func}");
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
    let mut func = Function::new(
        "max",
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
    let cmp = builder.icmp(ICmpOp::Sgt, a.into(), b.into(), Origin::synthetic());
    builder.brif(cmp.into(), bb1, vec![], bb2, vec![], Origin::synthetic());

    builder.switch_to_block(bb1);
    builder.ret(Some(a.into()), Origin::synthetic());

    builder.switch_to_block(bb2);
    builder.ret(Some(b.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{func}");
    assert_eq!(
        output,
        "func @max(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = icmp.sgt v0, v1\n\
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
    let mut func = Function::new("factorial", vec![Type::Int], vec![], Some(Type::Int), None);
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
    let cmp = builder.icmp(ICmpOp::Sle, i.into(), n.into(), Origin::synthetic());
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

    let output = format!("{func}");
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
         \x20\x20\x20\x20\x20\x20v6 = icmp.sle v5, v0\n\
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
    let mut func = Function::new(
        "bitwise",
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
    let mut func = Function::new(
        "shifts",
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
    let v_shl = builder.shl(a.into(), b.into(), None, Origin::synthetic());
    let v_lshr = builder.lshr(a.into(), b.into(), None, Origin::synthetic());
    let v_ashr = builder.ashr(v_shl.into(), v_lshr.into(), None, Origin::synthetic());
    builder.ret(Some(v_ashr.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{func}");
    assert_eq!(
        output,
        "func @shifts(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = shl v0, v1\n\
         \x20\x20\x20\x20v3 = lshr v0, v1\n\
         \x20\x20\x20\x20v4 = ashr v2, v3\n\
         \x20\x20\x20\x20ret v4\n\
         }"
    );
}

#[test]
fn display_division_ops() {
    let mut func = Function::new(
        "divs",
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
    let v_sdiv = builder.sdiv(a.into(), b.into(), None, Origin::synthetic());
    let v_udiv = builder.udiv(a.into(), b.into(), None, Origin::synthetic());
    let v_add = builder.add(v_sdiv.into(), v_udiv.into(), None, Origin::synthetic());
    builder.ret(Some(v_add.into()), Origin::synthetic());
    builder.exit_region();

    let output = format!("{func}");
    assert_eq!(
        output,
        "func @divs(int, int) -> int {\n\
         \x20\x20bb0:\n\
         \x20\x20\x20\x20v0 = param 0\n\
         \x20\x20\x20\x20v1 = param 1\n\
         \x20\x20\x20\x20v2 = sdiv v0, v1\n\
         \x20\x20\x20\x20v3 = udiv v0, v1\n\
         \x20\x20\x20\x20v4 = add v2, v3\n\
         \x20\x20\x20\x20ret v4\n\
         }"
    );
}

#[test]
fn build_ptradd() {
    let mut func = Function::new(
        "ptr_arith",
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
    let mut func = Function::new(
        "ptr_ops",
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

    let output = format!("{func}");
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
