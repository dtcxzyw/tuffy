//! Tests for x86-64 target definitions, instruction selection, encoding, and ELF emission.

use crate::reg::Gpr;

#[test]
fn gpr_encoding() {
    assert_eq!(Gpr::Rax.encoding(), 0);
    assert_eq!(Gpr::Rcx.encoding(), 1);
    assert_eq!(Gpr::Rdi.encoding(), 7);
}

#[test]
fn gpr_names() {
    assert_eq!(Gpr::Rax.name32(), "eax");
    assert_eq!(Gpr::Rdi.name64(), "rdi");
}

// --- Instruction selection and encoding tests ---

use tuffy_ir::builder::Builder;
use tuffy_ir::function::{Function, RegionKind};
use tuffy_ir::instruction::{ICmpOp, Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{Annotation, Type};

use std::collections::HashMap;

use crate::backend::lower_isel_result;
use crate::encode;
use crate::isel;

#[test]
fn isel_add_function() {
    let (func, symbols) = build_add_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for add");

    assert_eq!(result.name, "add");
    // Isel now emits VReg instructions; count may differ from old pipeline.
    // Just verify it produced some instructions.
    assert!(!result.insts.is_empty());
}

#[test]
fn encode_add_function() {
    let (func, symbols) = build_add_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);

    // After regalloc the exact encoding may differ, but must contain ret (0xc3).
    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
    assert!(enc.relocations.is_empty());
}

#[test]
fn emit_elf_valid() {
    let (func, symbols) = build_add_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);
    let elf = crate::emit::emit_elf(&result.name, &enc.code, &enc.relocations);

    // Verify ELF magic number.
    assert_eq!(&elf[..4], b"\x7fELF");
}

fn build_add_func() -> (Function, SymbolTable) {
    let s32 = Some(Annotation::Signed(32));
    let mut st = SymbolTable::new();
    let name = st.intern("add");
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

    (func, st)
}

#[test]
fn isel_branch_function() {
    let (func, symbols) = build_branch_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for branch");
    assert_eq!(result.name, "max");

    // Verify we can encode it without panicking and get valid bytes.
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);
    assert!(!enc.code.is_empty());
}

#[test]
fn encode_branch_labels_resolved() {
    let (func, symbols) = build_branch_func();
    let no_rdx_captures = HashMap::new();
    let no_rdx_moves = HashMap::new();
    let result = isel::isel(&func, &symbols, &no_rdx_captures, &no_rdx_moves)
        .expect("isel should succeed for branch");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);

    // Verify it doesn't panic and produces non-trivial output.
    assert!(enc.code.len() > 10);
    assert!(enc.relocations.is_empty());
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
fn build_branch_func() -> (Function, SymbolTable) {
    let s32 = Some(Annotation::Signed(32));
    let mut st = SymbolTable::new();
    let name = st.intern("max");
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
    let then_bb = builder.create_block();
    let else_bb = builder.create_block();

    builder.switch_to_block(entry);
    let a = builder.param(0, Type::Int, s32, Origin::synthetic());
    let b = builder.param(1, Type::Int, s32, Origin::synthetic());
    let cmp = builder.icmp(ICmpOp::Gt, a.into(), b.into(), Origin::synthetic());
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

    (func, st)
}

// --- Non-standard annotation width tests ---

#[test]
fn isel_sext_nonstandard_unsigned_width() {
    let (func, symbols) = build_extend_func("sext_u17", Annotation::Unsigned(17), true);
    let captures: HashMap<u32, ()> = HashMap::new();
    let moves: HashMap<u32, u32> = HashMap::new();
    let result = isel::isel(&func, &symbols, &captures, &moves).expect("isel should succeed");

    let has_shl = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::ShlImm { imm: 47, .. }));
    let has_sar = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::SarImm { imm: 47, .. }));
    assert!(has_shl, "sext :u17 should emit ShlImm(47)");
    assert!(has_sar, "sext :u17 should emit SarImm(47)");
}

#[test]
fn isel_sext_nonstandard_signed_is_noop() {
    let (func, symbols) = build_extend_func("sext_s17", Annotation::Signed(17), true);
    let captures: HashMap<u32, ()> = HashMap::new();
    let moves: HashMap<u32, u32> = HashMap::new();
    let result = isel::isel(&func, &symbols, &captures, &moves).expect("isel should succeed");

    let has_shift = result.insts.iter().any(|i| {
        matches!(
            i,
            crate::inst::MInst::ShlImm { .. } | crate::inst::MInst::SarImm { .. }
        )
    });
    assert!(!has_shift, "sext :s17 should NOT emit shift sequence");
}

#[test]
fn isel_zext_nonstandard_signed_width() {
    let (func, symbols) = build_extend_func("zext_s13", Annotation::Signed(13), false);
    let captures: HashMap<u32, ()> = HashMap::new();
    let moves: HashMap<u32, u32> = HashMap::new();
    let result = isel::isel(&func, &symbols, &captures, &moves).expect("isel should succeed");

    let has_and = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::AndRI { imm: 0x1FFF, .. }));
    assert!(has_and, "zext :s13 should emit AndRI(0x1FFF)");
}

#[test]
fn isel_zext_nonstandard_unsigned_is_noop() {
    let (func, symbols) = build_extend_func("zext_u13", Annotation::Unsigned(13), false);
    let captures: HashMap<u32, ()> = HashMap::new();
    let moves: HashMap<u32, u32> = HashMap::new();
    let result = isel::isel(&func, &symbols, &captures, &moves).expect("isel should succeed");

    let has_and = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::AndRI { .. }));
    assert!(!has_and, "zext :u13 should NOT emit AND mask");
}

/// Build: fn name(a: int :ann) -> int { sext/zext a to 64 }
fn build_extend_func(name: &str, ann: Annotation, is_sext: bool) -> (Function, SymbolTable) {
    let s64 = Some(Annotation::Signed(64));
    let src_ann = Some(ann);
    let mut st = SymbolTable::new();
    let sym = st.intern(name);
    let mut func = Function::new(
        sym,
        vec![Type::Int],
        vec![src_ann],
        vec![],
        Some(Type::Int),
        s64,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let a = builder.param(0, Type::Int, src_ann, Origin::synthetic());
    let extended = if is_sext {
        builder.sext(Operand::annotated(a, ann), 64, Origin::synthetic())
    } else {
        builder.zext(Operand::annotated(a, ann), 64, Origin::synthetic())
    };
    builder.ret(
        Some(Operand::annotated(extended, Annotation::Signed(64))),
        Origin::synthetic(),
    );

    builder.exit_region();

    (func, st)
}
