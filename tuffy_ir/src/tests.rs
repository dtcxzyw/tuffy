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
