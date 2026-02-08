//! Tests for instruction selection, encoding, and ELF emission.

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{Operand, Origin};
use tuffy_ir::types::{Annotation, Type};

use crate::encode;
use crate::isel;

#[test]
fn isel_add_function() {
    let func = build_add_func();
    let result = isel::isel(&func).expect("isel should succeed for add");

    assert_eq!(result.name, "add");
    // Expected: mov eax, edi; add eax, esi; ret (annotations don't generate machine insts)
    assert_eq!(result.insts.len(), 3);
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
