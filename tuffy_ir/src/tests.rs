//! Tests for the tuffy IR builder.

use crate::builder::Builder;
use crate::function::Function;
use crate::instruction::{Op, Origin};
use crate::types::Type;

#[test]
fn build_add_function() {
    let mut func = Function::new("add", vec![Type::Int, Type::Int], Some(Type::Int));
    let mut builder = Builder::new(&mut func);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, Origin::synthetic());
    let b = builder.param(1, Type::Int, Origin::synthetic());
    let sum = builder.add(a, b, Origin::synthetic());
    builder.ret(Some(sum), Origin::synthetic());

    assert_eq!(func.instructions.len(), 4);
    assert_eq!(func.blocks.len(), 1);
    assert_eq!(func.block_insts(entry).len(), 4);

    assert!(matches!(func.instructions[0].op, Op::Param(0)));
    assert!(matches!(func.instructions[1].op, Op::Param(1)));
    assert!(matches!(func.instructions[2].op, Op::Add(_, _)));
    assert!(matches!(func.instructions[3].op, Op::Ret(Some(_))));
}

#[test]
fn build_with_assert_sext() {
    let mut func = Function::new("add_i32", vec![Type::Int, Type::Int], Some(Type::Int));
    let mut builder = Builder::new(&mut func);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, Origin::synthetic());
    let b = builder.param(1, Type::Int, Origin::synthetic());
    let a32 = builder.assert_sext(a, 32, Origin::synthetic());
    let b32 = builder.assert_sext(b, 32, Origin::synthetic());
    let sum = builder.add(a32, b32, Origin::synthetic());
    let result = builder.assert_sext(sum, 32, Origin::synthetic());
    builder.ret(Some(result), Origin::synthetic());

    assert_eq!(func.instructions.len(), 7);
    assert!(matches!(func.instructions[2].op, Op::AssertSext(_, 32)));
}
