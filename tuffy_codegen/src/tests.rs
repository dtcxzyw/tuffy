//! Tests for instruction selection, encoding, and ELF emission.

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{ICmpOp, Operand, Origin};
use tuffy_ir::types::{Annotation, Type};

use crate::encode;
use crate::isel;

#[test]
fn isel_add_function() {
    let func = build_add_func();
    let result = isel::isel(&func).expect("isel should succeed for add");

    assert_eq!(result.name, "add");
    // Expected: label; mov eax, edi; add eax, esi; ret
    assert_eq!(result.insts.len(), 4);
}

#[test]
fn encode_add_function() {
    let func = build_add_func();
    let result = isel::isel(&func).expect("isel should succeed for add");
    let code = encode::encode_function(&result.insts);

    // mov eax, edi  => 89 f8
    // add eax, esi  => 01 f0
    // ret           => c3
    assert_eq!(code, vec![0x89, 0xf8, 0x01, 0xf0, 0xc3]);
}

#[test]
fn emit_elf_valid() {
    let func = build_add_func();
    let result = isel::isel(&func).expect("isel should succeed for add");
    let code = encode::encode_function(&result.insts);
    let elf = crate::emit::emit_elf(&result.name, &code);

    // Verify ELF magic number.
    assert_eq!(&elf[..4], b"\x7fELF");
}

fn build_add_func() -> Function {
    let s32 = Some(Annotation::Signed(32));
    let mut func = Function::new(
        "add",
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

    func
}

#[test]
fn isel_branch_function() {
    let func = build_branch_func();
    let result = isel::isel(&func).expect("isel should succeed for branch");
    assert_eq!(result.name, "max");

    // Verify we can encode it without panicking and get valid bytes.
    let code = encode::encode_function(&result.insts);
    assert!(!code.is_empty());
}

#[test]
fn encode_branch_labels_resolved() {
    let func = build_branch_func();
    let result = isel::isel(&func).expect("isel should succeed for branch");
    let code = encode::encode_function(&result.insts);

    // The encoded output should not contain any unresolved zero-filled jump targets
    // at positions where jumps exist. We just verify it doesn't panic and produces
    // non-trivial output.
    assert!(code.len() > 10);
}

/// Build: fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
///
/// entry:
///   %0 = param 0
///   %1 = param 1
///   %2 = icmp sgt %0, %1
///   brif %2, then_bb(), else_bb()
/// then_bb:
///   ret %0
/// else_bb:
///   ret %1
fn build_branch_func() -> Function {
    let s32 = Some(Annotation::Signed(32));
    let mut func = Function::new(
        "max",
        vec![Type::Int, Type::Int],
        vec![s32, s32],
        Some(Type::Int),
        s32,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    let then_bb = builder.create_block();
    let else_bb = builder.create_block();

    builder.switch_to_block(entry);
    let a = builder.param(0, Type::Int, s32, Origin::synthetic());
    let b = builder.param(1, Type::Int, s32, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Sgt, a.into(), b.into(), Origin::synthetic());
    builder.brif(
        cmp.into(),
        then_bb,
        vec![],
        else_bb,
        vec![],
        Origin::synthetic(),
    );

    builder.switch_to_block(then_bb);
    builder.ret(Some(a.into()), Origin::synthetic());

    builder.switch_to_block(else_bb);
    builder.ret(Some(b.into()), Origin::synthetic());

    builder.exit_region();

    func
}
