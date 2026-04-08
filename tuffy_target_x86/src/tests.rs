//! Tests for x86-64 target definitions, instruction selection, encoding, and ELF emission.

use crate::reg::Gpr;
use tuffy_ir::types::Annotation;

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
use tuffy_ir::instruction::{ICmpOp, Op, Operand, Origin};
use tuffy_ir::module::SymbolTable;
use tuffy_ir::types::{FloatType, IntAnnotation, IntSignedness, Type};
use tuffy_ir::value::ValueRef;
use tuffy_target::legality::{LegalityInfo, LegalizeAction};

const I64: IntAnnotation = IntAnnotation {
    bit_width: 64,
    signedness: IntSignedness::Unsigned,
};

use crate::backend::{X86Backend, lower_isel_result};
use crate::encode;
use crate::isel;
use crate::legality::X86LegalityInfo;
use tuffy_target::backend::Backend;

#[test]
fn legality_uses_expand_for_divrem_wider_than_double_width() {
    let lhs = Operand::new(ValueRef::inst_result(0));
    let rhs = Operand::new(ValueRef::inst_result(1));
    let div = Op::Div(lhs.clone().into(), rhs.clone().into());
    let rem = Op::Rem(lhs.into(), rhs.into());
    let legality = X86LegalityInfo;

    assert_eq!(
        legality.legalize_action(&div, Some(128)),
        LegalizeAction::LibCall("__udivti3")
    );
    assert_eq!(
        legality.legalize_action(&rem, Some(128)),
        LegalizeAction::LibCall("__umodti3")
    );
    assert_eq!(
        legality.legalize_action(&div, Some(160)),
        LegalizeAction::Expand
    );
    assert_eq!(
        legality.legalize_action(&rem, Some(160)),
        LegalizeAction::Expand
    );
}

#[test]
fn isel_add_function() {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");

    assert_eq!(result.name, "add");
    // Isel now emits VReg instructions; count may differ from old pipeline.
    // Just verify it produced some instructions.
    assert!(!result.insts.is_empty());
}

#[test]
fn encode_add_function() {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);

    // After regalloc the exact encoding may differ, but must contain ret (0xc3).
    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
    assert!(enc.relocations.is_empty());
}

#[test]
fn encode_f64_const_return_function() {
    let (func, symbols) = build_f64_const_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for f64 const");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);

    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
}

#[test]
fn encode_f16_const_return_function() {
    let (func, symbols) = build_f16_const_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for f16 const");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);

    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
}

#[test]
fn emit_elf_valid() {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);
    let elf = crate::emit::emit_elf(&result.name, &enc.code, &enc.relocations);

    // Verify ELF magic number.
    assert_eq!(&elf[..4], b"\x7fELF");
}

#[test]
fn isel_unsupported_continue_returns_error() {
    let (func, symbols) = build_continue_func();
    let err = match isel::isel(&func, &symbols) {
        Ok(_) => panic!("isel should fail for continue"),
        Err(err) => err,
    };
    assert!(err.contains("instruction selection failed"));
    assert!(err.contains("Continue"));
}

#[test]
fn backend_compile_function_propagates_isel_error() {
    let (func, symbols) = build_continue_func();
    let err = match X86Backend.compile_function(&func, &symbols) {
        Ok(_) => panic!("backend should fail fast on unsupported IR"),
        Err(err) => err,
    };
    assert!(err.contains("instruction selection failed"));
    assert!(err.contains("Continue"));
}

fn build_add_func() -> (Function, SymbolTable) {
    let i32_type = Type::Int;
    let mut st = SymbolTable::new();
    let name = st.intern("add");
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), i32_type.clone()],
        vec![None, None],
        vec![],
        Some(i32_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i32_type.clone(), None, Origin::synthetic());
    let b = builder.param(1, i32_type.clone(), None, Origin::synthetic());
    let sum = builder.add(a.into(), b.into(), I64, Origin::synthetic());
    builder.ret(Some(sum.into()), None, mem0.into(), Origin::synthetic());

    builder.exit_region();

    (func, st)
}

fn build_f64_const_func() -> (Function, SymbolTable) {
    let f64_type = Type::Float(FloatType::F64);
    let mut st = SymbolTable::new();
    let name = st.intern("const_f64");
    let mut func = Function::new(name, vec![], vec![], vec![], Some(f64_type.clone()), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let value = builder.fconst(
        FloatType::F64,
        0x3ff8_0000_0000_0000_u128,
        Origin::synthetic(),
    );
    builder.ret(Some(value.into()), None, mem0.into(), Origin::synthetic());

    builder.exit_region();

    (func, st)
}

fn build_f16_const_func() -> (Function, SymbolTable) {
    let f16_type = Type::Float(FloatType::F16);
    let mut st = SymbolTable::new();
    let name = st.intern("const_f16");
    let mut func = Function::new(name, vec![], vec![], vec![], Some(f16_type.clone()), None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let value = builder.fconst(FloatType::F16, 0x3c00_u128, Origin::synthetic());
    builder.ret(Some(value.into()), None, mem0.into(), Origin::synthetic());

    builder.exit_region();

    (func, st)
}

fn build_continue_func() -> (Function, SymbolTable) {
    let mut st = SymbolTable::new();
    let name = st.intern("continue_fail");
    let mut func = Function::new(name, vec![], vec![], vec![], None, None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);
    builder.continue_(vec![], Origin::synthetic());

    builder.exit_region();

    (func, st)
}

#[test]
fn isel_branch_function() {
    let (func, symbols) = build_branch_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for branch");
    assert_eq!(result.name, "max");

    // Verify we can encode it without panicking and get valid bytes.
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts);
    assert!(!enc.code.is_empty());
}

#[test]
fn encode_branch_labels_resolved() {
    let (func, symbols) = build_branch_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for branch");
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
    let i32_type = Type::Int;
    let mut st = SymbolTable::new();
    let name = st.intern("max");
    let mut func = Function::new(
        name,
        vec![i32_type.clone(), i32_type.clone()],
        vec![None, None],
        vec![],
        Some(i32_type.clone()),
        None,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    let then_bb = builder.create_block();
    let else_bb = builder.create_block();

    builder.switch_to_block(entry);
    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, i32_type.clone(), None, Origin::synthetic());
    let b = builder.param(1, i32_type, None, Origin::synthetic());
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
    builder.ret(Some(a.into()), None, mem0.into(), Origin::synthetic());

    builder.switch_to_block(else_bb);
    builder.ret(Some(b.into()), None, mem0.into(), Origin::synthetic());

    builder.exit_region();

    (func, st)
}

// --- Non-standard annotation width tests ---

#[test]
fn isel_sext_nonstandard_unsigned_width() {
    let (func, symbols) = build_extend_func(
        "sext_u17",
        IntAnnotation {
            bit_width: 17,
            signedness: IntSignedness::Unsigned,
        },
        true,
    );
    let result = isel::isel(&func, &symbols).expect("isel should succeed");

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
    let (func, symbols) = build_extend_func(
        "sext_s17",
        IntAnnotation {
            bit_width: 17,
            signedness: IntSignedness::Signed,
        },
        true,
    );
    let result = isel::isel(&func, &symbols).expect("isel should succeed");

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
    let (func, symbols) = build_extend_func(
        "zext_s13",
        IntAnnotation {
            bit_width: 13,
            signedness: IntSignedness::Signed,
        },
        false,
    );
    let result = isel::isel(&func, &symbols).expect("isel should succeed");

    let has_and = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::AndRI { imm: 0x1FFF, .. }));
    assert!(has_and, "zext :s13 should emit AndRI(0x1FFF)");
}

#[test]
fn isel_zext_nonstandard_unsigned_is_noop() {
    let (func, symbols) = build_extend_func(
        "zext_u13",
        IntAnnotation {
            bit_width: 13,
            signedness: IntSignedness::Unsigned,
        },
        false,
    );
    let result = isel::isel(&func, &symbols).expect("isel should succeed");

    let has_and = result
        .insts
        .iter()
        .any(|i| matches!(i, crate::inst::MInst::AndRI { .. }));
    assert!(!has_and, "zext :u13 should NOT emit AND mask");
}

#[test]
fn isel_call_uses_rdx_for_double_width_annotation() {
    let (func, symbols) = build_annotated_wide_call_func();
    let result = isel::isel(&func, &symbols)
        .expect("isel should succeed for exact-double-width-annotated call");

    let saw_call_with_ret2 = result.insts.iter().any(|inst| {
        matches!(
            inst,
            crate::inst::MInst::CallSym {
                name,
                ret: Some(_),
                ret2: Some(_),
                ..
            } if name == "callee_wide"
        )
    });
    assert!(
        saw_call_with_ret2,
        "exact-double-width-annotated call should reserve both RAX and RDX"
    );
}

fn build_annotated_wide_call_func() -> (Function, SymbolTable) {
    let mut st = SymbolTable::new();
    let caller = st.intern("caller_wide");
    let callee = st.intern("callee_wide");

    let ret_type = Type::Int;
    let wide_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 128,
        signedness: IntSignedness::Unsigned,
    }));
    let mut func = Function::new(
        caller,
        vec![],
        vec![],
        vec![],
        Some(ret_type.clone()),
        wide_ann.clone(),
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let callee_addr = builder.symbol_addr(callee, Origin::synthetic());
    let (call_mem, call_data) = builder.call(
        callee_addr.into(),
        vec![],
        ret_type,
        mem0.into(),
        None,
        wide_ann.clone(),
        Origin::synthetic(),
    );
    let call_data = call_data.expect("non-void call should produce data result");

    builder.ret(
        Some(call_data.into()),
        None,
        call_mem.into(),
        Origin::synthetic(),
    );

    builder.exit_region();

    (func, st)
}

/// Build: fn name(a: int :ann) -> int { sext/zext a to 64 }
fn build_extend_func(name: &str, ann: IntAnnotation, is_sext: bool) -> (Function, SymbolTable) {
    let src_type = Type::Int;
    let i64_type = Type::Int;
    let mut st = SymbolTable::new();
    let sym = st.intern(name);
    let src_ann = Some(Annotation::Int(ann));
    let i64_ann = Some(Annotation::Int(IntAnnotation {
        bit_width: 64,
        signedness: IntSignedness::Signed,
    }));
    let mut func = Function::new(
        sym,
        vec![src_type.clone()],
        vec![src_ann.clone()],
        vec![],
        Some(i64_type.clone()),
        i64_ann,
    );
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);

    let entry = builder.create_block();
    builder.switch_to_block(entry);

    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let a = builder.param(0, src_type, src_ann.clone(), Origin::synthetic());
    let extended = if is_sext {
        builder.sext(Operand::new(a).into(), 64, Origin::synthetic())
    } else {
        builder.zext(Operand::new(a).into(), 64, Origin::synthetic())
    };
    builder.ret(
        Some(Operand::new(extended.raw())),
        None,
        mem0.into(),
        Origin::synthetic(),
    );

    builder.exit_region();

    (func, st)
}
