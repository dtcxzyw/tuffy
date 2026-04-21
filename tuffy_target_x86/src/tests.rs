//! Tests for x86-64 target definitions, instruction selection, encoding, and ELF emission.

use crate::inst::{MInst, OpSize};
use crate::reg::Gpr;
use object::{Object, ObjectSection};
use tuffy_ir::debug::{
    DebugSource, DebugVariable, DebugVariableKind, FunctionDebugInfo, SourceLocation,
};
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
use tuffy_ir::parser::parse_module;
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
use tuffy_target::types::{
    CompiledDebugInfo, CompiledFunction, DebugLineRecord, DebugLocation, DebugVariableRange,
};

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
fn isel_ptradd_uses_lea_indexed() {
    let module = parse_module(
        r#"
func @ptradd_indexed(ptr, int:u64) -> ptr {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: ptr = ptradd v1, v2
    ret v3, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed for ptradd");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::LeaIndexed { scale: 1, .. })),
        "ptradd should lower to indexed lea: {:?}",
        result.insts
    );
    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::AddRR { .. })),
        "ptradd should no longer lower as mov+add: {:?}",
        result.insts
    );
}

#[test]
fn isel_ptradd_const_uses_lea_offset() {
    let module = parse_module(
        r#"
func @ptradd_const(ptr) -> ptr {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u4 = iconst 8
    v3: ptr = ptradd v1, v2
    ret v3, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed for ptradd");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::Lea { offset: 8, .. })),
        "constant ptradd should lower to lea with displacement: {:?}",
        result.insts
    );
    assert!(
        !result.insts.iter().any(|inst| matches!(
            inst,
            MInst::MovRI { imm: 8, .. } | MInst::MovRI64 { imm: 8, .. }
        )),
        "constant ptradd displacement should not materialize a separate constant register: {:?}",
        result.insts
    );
}

#[test]
fn isel_ptradd_shl_offset_uses_scaled_lea_without_shift() {
    let module = parse_module(
        r#"
func @ptradd_scaled(ptr, int:u64) -> ptr {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: int:u2 = iconst 3
    v4: int:u64 = shl v2, v3
    v5: ptr = ptradd v1, v4
    ret v5, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::LeaIndexed { scale: 8, .. })),
        "scaled ptradd should use lea with scale 8: {:?}",
        result.insts
    );
    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::ShlImm { imm: 3, .. } | MInst::ShlRCL { .. })),
        "scaled ptradd should not materialize a separate shift: {:?}",
        result.insts
    );
}

#[test]
fn isel_ptradd_mul_scale_uses_scaled_lea_without_mul() {
    let module = parse_module(
        r#"
func @ptradd_mul_scale(ptr, int:u64) -> ptr {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: int:u64 = param 1
    v3: int:u4 = iconst 8
    v4: int:u64 = mul v2, v3
    v5: ptr = ptradd v1, v4
    ret v5, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::LeaIndexed { scale: 8, .. })),
        "mul-scaled ptradd should use lea with scale 8: {:?}",
        result.insts
    );
    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::ImulRR { .. })),
        "mul-scaled ptradd should not materialize a separate multiply: {:?}",
        result.insts
    );
}

#[test]
fn isel_shl_const_uses_imm_shift() {
    let module = parse_module(
        r#"
func @shl_const(int:u64) -> int:u64 {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u2 = iconst 3
    v3: int:u64 = shl v1, v2
    ret v3, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::ShlImm { imm: 3, .. })),
        "constant shl should lower to shl imm: {:?}",
        result.insts
    );
    assert!(
        !result.insts.iter().any(|inst| matches!(
            inst,
            MInst::MovRI { imm: 3, .. } | MInst::MovRI64 { imm: 3, .. }
        )),
        "constant shift amount should not materialize a separate register: {:?}",
        result.insts
    );
}

#[test]
fn isel_shr_const_uses_imm_shift() {
    let module = parse_module(
        r#"
func @shr_const(int:u64) -> int:u64 {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u2 = iconst 3
    v3: int:u64 = shr v1, v2
    ret v3, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::ShrImm { imm: 3, .. })),
        "constant shr should lower to shr imm: {:?}",
        result.insts
    );
    assert!(
        !result.insts.iter().any(|inst| matches!(
            inst,
            MInst::MovRI { imm: 3, .. } | MInst::MovRI64 { imm: 3, .. }
        )),
        "constant shift amount should not materialize a separate register: {:?}",
        result.insts
    );
}

#[test]
fn encode_add_function() {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);

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
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);

    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
}

#[test]
fn encode_f16_const_return_function() {
    let (func, symbols) = build_f16_const_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for f16 const");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);

    assert!(!enc.code.is_empty());
    assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
}

#[test]
fn encode_count_ops_support_16bit_operands() {
    for inst in [
        MInst::Popcnt {
            size: OpSize::S16,
            dst: Gpr::Rax,
            src: Gpr::Rcx,
        },
        MInst::Lzcnt {
            size: OpSize::S16,
            dst: Gpr::Rax,
            src: Gpr::Rcx,
        },
        MInst::Tzcnt {
            size: OpSize::S16,
            dst: Gpr::Rax,
            src: Gpr::Rcx,
        },
    ] {
        let insts = vec![inst, MInst::Ret];
        let enc = encode::encode_function(&insts, &vec![None; insts.len()]);
        assert!(
            !enc.code.is_empty(),
            "narrow count op should encode without panicking"
        );
        assert!(enc.code.contains(&0xc3), "expected ret in encoded output");
    }
}

#[test]
fn emit_elf_valid() {
    let (func, symbols) = build_add_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for add");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);
    let elf = crate::emit::emit_elf(&result.name, &enc.code, &enc.relocations);

    // Verify ELF magic number.
    assert_eq!(&elf[..4], b"\x7fELF");
}

#[test]
fn encode_function_deduplicates_line_records() {
    let insts = vec![
        MInst::MovRI {
            size: OpSize::S64,
            dst: Gpr::Rax,
            imm: 1,
        },
        MInst::MovRI {
            size: OpSize::S64,
            dst: Gpr::Rcx,
            imm: 2,
        },
        MInst::Ret,
    ];
    let encoded = encode::encode_function(&insts, &[Some(11), Some(11), Some(12)]);

    assert_eq!(
        encoded.line_records.len(),
        2,
        "adjacent instructions with the same source should share one line record"
    );
    assert_eq!(encoded.line_records[0].offset, 0);
    assert_eq!(encoded.line_records[0].source, 11);
    assert!(
        encoded.line_records[1].offset > encoded.line_records[0].offset,
        "a new source should start at a later machine-code offset"
    );
    assert_eq!(encoded.line_records[1].source, 12);
}

#[test]
fn emit_elf_uses_loclists_for_multi_range_variables() {
    let debug = CompiledDebugInfo {
        function: FunctionDebugInfo {
            declaration: Some(SourceLocation {
                file: "src/lib.rs".to_string(),
                line: 1,
                column: 1,
            }),
            sources: vec![DebugSource {
                location: SourceLocation {
                    file: "src/lib.rs".to_string(),
                    line: 1,
                    column: 1,
                },
            }],
            variables: vec![DebugVariable {
                name: "value".to_string(),
                kind: DebugVariableKind::Local,
                declaration: Some(SourceLocation {
                    file: "src/lib.rs".to_string(),
                    line: 1,
                    column: 5,
                }),
            }],
            bindings: vec![],
        },
        lines: vec![DebugLineRecord {
            offset: 0,
            source: 0,
        }],
        variables: vec![tuffy_target::types::CompiledDebugVariable {
            variable: 0,
            ranges: vec![
                DebugVariableRange {
                    start: 0,
                    end: 1,
                    location: DebugLocation::Register(0),
                },
                DebugVariableRange {
                    start: 1,
                    end: 3,
                    location: DebugLocation::FrameOffset(-8),
                },
            ],
        }],
    };
    let elf = crate::emit::emit_elf_multi(&[CompiledFunction {
        name: "debug_ranges".to_string(),
        code: vec![0x90, 0x90, 0xc3],
        relocations: vec![],
        debug: Some(debug),
        weak: false,
        local: false,
        has_frame_pointer: true,
        call_site_table: vec![],
        callee_saved_dwarf_regs: vec![],
        sub_amount: 0,
    }]);

    let obj = object::File::parse(&*elf).expect("emitted ELF should parse");
    let loclists = obj
        .section_by_name(".debug_loclists")
        .expect("multi-range debuginfo should emit .debug_loclists");
    assert!(
        !loclists
            .data()
            .expect("debug loclists section should be readable")
            .is_empty(),
        ".debug_loclists should contain encoded variable ranges"
    );
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

#[test]
fn isel_small_constant_memcopy_avoids_libcall() {
    let module = parse_module(
        r#"
func @small_memcopy(ptr, ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:u64 = iconst 4
    v4: mem = memcopy v1:align4, v2:align4, v3, v0
    ret v4
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed for small memcopy");

    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::CallSym { name, .. } if name == "memcpy")),
        "small constant memcopy should not call memcpy: {:?}",
        result.insts
    );
}

#[test]
fn isel_small_constant_memmove_avoids_libcall() {
    let module = parse_module(
        r#"
func @small_memmove(ptr, ptr) {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: int:u64 = iconst 4
    v4: mem = memmove v1:align4, v2:align4, v3, v0
    ret v4
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed for small memmove");

    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::CallSym { name, .. } if name == "memmove")),
        "small constant memmove should not call memmove: {:?}",
        result.insts
    );
}

#[test]
fn isel_small_direct_memcpy_call_avoids_libcall() {
    let module = parse_module(
        r#"
func @small_direct_memcpy(ptr, ptr) -> int:u64 {
  bb0(v0: mem):
    v1: ptr = param 0
    v2: ptr = param 1
    v3: ptr = symbol_addr @memcpy
    v4: int:u64 = iconst 4
    v5: mem, v6: int:u64 = call v3(v1, v2, v4), v0 -> int:u64
    ret v6, v5
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result =
        isel::isel(func, &module.symbols).expect("isel should succeed for direct memcpy call");

    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::CallSym { name, .. } if name == "memcpy")),
        "small direct memcpy call should not call memcpy: {:?}",
        result.insts
    );
}

#[test]
fn isel_branch_only_intified_bool_tree_stays_in_flags() {
    let module = parse_module(
        r#"
func @branch_ladder(int:s32, int:s32) {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = param 1
    v3: bool = icmp.lt v1, v2
    v4: int:s32 = iconst 1
    v5: int:s32 = iconst 0
    v6: int:s32 = select v3, v4, v5
    v7: int:s32 = iconst 0
    v8: bool = icmp.eq v6, v7
    brif v8, bb1(v0), bb2(v0)
  bb1(v10: mem):
    ret v10
  bb2(v11: mem):
    ret v11
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed for branch ladder");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::CmpRR { .. })),
        "branch ladder should emit a compare: {:?}",
        result.insts
    );
    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::Jcc { .. })),
        "branch ladder should emit a conditional jump: {:?}",
        result.insts
    );
    assert!(
        result
            .insts
            .windows(2)
            .any(|window| { matches!(window, [MInst::CmpRR { .. }, MInst::Jcc { .. }]) }),
        "branch ladder should finish with a recovered compare+jump pair: {:?}",
        result.insts
    );
}

#[test]
fn isel_branch_only_direct_icmp_stays_in_flags() {
    let module = parse_module(
        r#"
func @branch_direct_icmp(int:u64, int:u64) {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u64 = param 1
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0), bb2(v0)
  bb1(v4: mem):
    ret v4
  bb2(v5: mem):
    ret v5
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::CmpRR { .. })),
        "branch-only direct icmp should emit a compare: {:?}",
        result.insts
    );
    assert!(
        result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::Jcc { .. })),
        "branch-only direct icmp should emit a conditional jump: {:?}",
        result.insts
    );
    assert!(
        !result
            .insts
            .iter()
            .any(|inst| matches!(inst, MInst::SetCC { .. })),
        "branch-only direct icmp should not materialize a boolean register: {:?}",
        result.insts
    );
}

#[test]
fn isel_materializes_cmp_values_before_later_compares_clobber_flags() {
    let module = parse_module(
        r#"
func @cmp_value_reuse(int:u64, int:u64, int:u64, int:u64) -> int:u64 {
  bb0(v0: mem):
    v1: int:u64 = param 0
    v2: int:u64 = param 1
    v3: int:u64 = param 2
    v4: int:u64 = param 3
    v5: bool = icmp.lt v1, v2
    v6: bool = icmp.lt v3, v4
    v7: int:u64 = iconst 1
    v8: int:u64 = iconst 0
    v9: int:u64 = select v5, v7, v8
    v10: int:u64 = select v6, v7, v8
    v11: int:u64 = add v9, v10
    ret v11, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    let cmp_positions: Vec<_> = result
        .insts
        .iter()
        .enumerate()
        .filter_map(|(idx, inst)| matches!(inst, MInst::CmpRR { .. }).then_some(idx))
        .collect();
    assert!(
        cmp_positions.len() >= 2,
        "expected at least two compare instructions: {:?}",
        result.insts
    );
    let first_cmp = cmp_positions[0];
    let second_cmp = cmp_positions[1];
    assert!(
        result.insts[first_cmp + 1..second_cmp]
            .iter()
            .any(|inst| matches!(inst, MInst::SetCC { .. })),
        "first compare result must be materialized before the next compare clobbers flags: {:?}",
        result.insts
    );
}

#[test]
fn isel_icmp_uses_narrow_integer_width() {
    let module = parse_module(
        r#"
func @cmp_i32(int:s32, int:s32) -> bool {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = param 1
    v3: bool = icmp.lt v1, v2
    ret v3, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result.insts.iter().any(|inst| matches!(
            inst,
            MInst::CmpRR {
                size: OpSize::S32,
                ..
            }
        )),
        "narrow icmp should emit a 32-bit compare: {:?}",
        result.insts
    );
}

#[test]
fn isel_count_zero_ops_use_narrow_integer_width() {
    let module = parse_module(
        r#"
func @count_zeroes_i32(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = count_leading_zeros.32 v1
    v3: int:s32 = count_trailing_zeros v1
    v4: int:s32 = add v2, v3
    ret v4, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        result.insts.iter().any(|inst| matches!(
            inst,
            MInst::Lzcnt {
                size: OpSize::S32,
                ..
            }
        )),
        "count_leading_zeros on i32 should emit a 32-bit lzcnt: {:?}",
        result.insts
    );
    assert!(
        result.insts.iter().any(|inst| matches!(
            inst,
            MInst::Tzcnt {
                size: OpSize::S32,
                ..
            }
        )),
        "count_trailing_zeros on i32 should emit a 32-bit tzcnt: {:?}",
        result.insts
    );
}

#[test]
fn count_ops_on_u8_widen_before_encoding() {
    let module = parse_module(
        r#"
func @count_u8(int:u8) -> int:u8 {
  bb0(v0: mem):
    v1: int:u8 = param 0
    v2: int:u8 = count_ones v1
    v3: int:u8 = count_leading_zeros.8 v1
    v4: int:u8 = count_trailing_zeros v1
    v5: int:u8 = add v2, v3
    v6: int:u8 = add v5, v4
    ret v6, v0
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");

    assert!(
        !result.insts.iter().any(|inst| matches!(
            inst,
            MInst::Popcnt {
                size: OpSize::S8,
                ..
            } | MInst::Lzcnt {
                size: OpSize::S8,
                ..
            } | MInst::Tzcnt {
                size: OpSize::S8,
                ..
            }
        )),
        "8-bit count ops must be widened before encoding: {:?}",
        result.insts
    );
    assert!(
        result
            .insts
            .iter()
            .filter(|inst| matches!(inst, MInst::MovzxB { .. }))
            .count()
            >= 3,
        "8-bit count ops should materialize zero-extended inputs: {:?}",
        result.insts
    );

    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);
    assert!(
        !enc.code.is_empty(),
        "widened 8-bit count ops should encode successfully"
    );
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
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);
    assert!(!enc.code.is_empty());
}

#[test]
fn encode_branch_labels_resolved() {
    let (func, symbols) = build_branch_func();
    let result = isel::isel(&func, &symbols).expect("isel should succeed for branch");
    let pinsts = lower_isel_result(&result);
    let enc = encode::encode_function(&pinsts, &vec![None; pinsts.len()]);

    // Verify it doesn't panic and produces non-trivial output.
    assert!(enc.code.len() > 10);
    assert!(enc.relocations.is_empty());
}

#[test]
fn lower_removes_fallthrough_jump() {
    let module = parse_module(
        r#"
func @fallthrough_jump() {
  bb0(v0: mem):
    br bb1(v0)
  bb1(v1: mem):
    ret v1
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");
    let pinsts = lower_isel_result(&result);

    assert!(
        !pinsts.iter().any(|inst| matches!(inst, MInst::Jmp { .. })),
        "fallthrough jump should be removed: {:?}",
        pinsts
    );
}

#[test]
fn lower_keeps_non_fallthrough_jump() {
    let module = parse_module(
        r#"
func @backedge_jump() {
  bb0(v0: mem):
    br bb1(v0)
  bb1(v1: mem):
    br bb0(v1)
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");
    let pinsts = lower_isel_result(&result);

    assert!(
        pinsts.iter().any(|inst| matches!(inst, MInst::Jmp { .. })),
        "non-fallthrough backedge jump should remain: {:?}",
        pinsts
    );
}

#[test]
fn lower_brif_falls_through_next_then_block() {
    let module = parse_module(
        r#"
func @brif_then_fallthrough(int:s32, int:s32) {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = param 1
    v3: bool = icmp.lt v1, v2
    brif v3, bb1(v0), bb2(v0)
  bb1(v4: mem):
    ret v4
  bb2(v5: mem):
    ret v5
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");
    let pinsts = lower_isel_result(&result);

    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jcc { .. }))
            .count(),
        1,
        "brif should keep one conditional jump: {:?}",
        pinsts
    );
    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jmp { .. }))
            .count(),
        0,
        "brif with next then-block should not need an unconditional jump: {:?}",
        pinsts
    );
}

#[test]
fn lower_brif_falls_through_next_else_block() {
    let module = parse_module(
        r#"
func @brif_else_fallthrough(int:s32, int:s32) {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = param 1
    v3: bool = icmp.lt v1, v2
    brif v3, bb2(v0), bb1(v0)
  bb1(v4: mem):
    ret v4
  bb2(v5: mem):
    ret v5
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");
    let pinsts = lower_isel_result(&result);

    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jcc { .. }))
            .count(),
        1,
        "brif should keep one conditional jump: {:?}",
        pinsts
    );
    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jmp { .. }))
            .count(),
        0,
        "brif with next else-block should not need an unconditional jump: {:?}",
        pinsts
    );
}

#[test]
fn lower_reorders_dead_forwarder_blocks_out_of_hot_path() {
    let module = parse_module(
        r#"
func @entry_dead_forwarder(bool) {
  bb0(v0: mem):
    v1: bool = param 0
    brif v1, bb3(v0), bb2(v0)
  bb1(v4: mem):
    br bb3(v4)
  bb2(v5: mem):
    ret v5
  bb3(v6: mem):
    ret v6
}
"#,
    )
    .expect("module should parse");
    let func = &module.functions[0];
    let result = isel::isel(func, &module.symbols).expect("isel should succeed");
    let pinsts = lower_isel_result(&result);

    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jcc { .. }))
            .count(),
        1,
        "entry branch should stay conditional: {:?}",
        pinsts
    );
    assert_eq!(
        pinsts
            .iter()
            .filter(|inst| matches!(inst, MInst::Jmp { .. }))
            .count(),
        1,
        "only the dead forwarder itself should keep a jump: {:?}",
        pinsts
    );
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

#[test]
fn isel_cleanup_call_materializes_stack_slot_args_defined_in_later_blocks() {
    let mut symbols = SymbolTable::new();
    let caller = symbols.intern("late_stack_slot_call");
    let callee = symbols.intern("callee");
    let mut func = Function::new(caller, vec![], vec![], vec![], None, None);
    let mut builder = Builder::new(&mut func);

    let root = builder.create_region(RegionKind::Function);
    builder.enter_region(root);
    let entry = builder.create_block();
    let call_block = builder.create_block();
    let slot_block = builder.create_block();
    let cleanup = builder.create_block();

    builder.switch_to_block(slot_block);
    let slot_mem = builder.add_block_arg(slot_block, Type::Mem, None);
    let late_slot = builder.stack_slot(8, 8, Origin::synthetic());
    let _ = builder.br(call_block, vec![slot_mem.into()], Origin::synthetic());

    builder.switch_to_block(entry);
    let mem0 = builder.add_block_arg(entry, Type::Mem, None);
    let callee_addr = builder.symbol_addr(callee, Origin::synthetic());
    let _ = builder.br(call_block, vec![mem0.into()], Origin::synthetic());

    builder.switch_to_block(call_block);
    let call_mem = builder.add_block_arg(call_block, Type::Mem, None);
    let (call_mem, None) = builder.call(
        callee_addr.into(),
        vec![late_slot.into()],
        Type::Unit,
        call_mem.into(),
        Some(cleanup.index()),
        None,
        Origin::synthetic(),
    ) else {
        panic!("expected void cleanup call");
    };
    builder.ret(None, None, call_mem.into(), Origin::synthetic());

    builder.switch_to_block(cleanup);
    let cleanup_mem = builder.add_block_arg(cleanup, Type::Mem, None);
    let _ = builder.landing_pad(Origin::synthetic());
    builder.ret(None, None, cleanup_mem.into(), Origin::synthetic());
    builder.exit_region();

    isel::isel(&func, &symbols).expect("cleanup call should materialize late-defined stack slots");
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
