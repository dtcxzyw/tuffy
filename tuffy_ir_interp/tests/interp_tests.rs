//! Integration tests for the tuffy IR interpreter.
//!
//! Tests parse IR text → Module → Interpreter → check results.

use tuffy_ir::parser::parse_module;
use tuffy_ir_interp::{ExecMode, InterpResult, Interpreter, Value};

/// Helper: parse IR, run `main`, return InterpResult.
fn run(ir: &str) -> InterpResult {
    let module = parse_module(ir).unwrap_or_else(|e| panic!("parse error: {e}"));
    let mut interp = Interpreter::new(&module, ExecMode::Strict);
    interp.run("main")
}

/// Extract the integer value from an InterpResult::Ok.
fn unwrap_int(r: InterpResult) -> i64 {
    match r {
        InterpResult::Ok(Some(Value::Int(n))) => n.try_into().unwrap(),
        other => panic!("expected Ok(Int), got: {other}"),
    }
}

/// Assert that the result is UB.
fn assert_ub(r: InterpResult) {
    match r {
        InterpResult::Ub(_) => {}
        other => panic!("expected Ub, got: {other}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Basic arithmetic
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_iconst_return() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    ret v1, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_add() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 10
    v2: int:s32 = iconst 32
    v3: int:s32 = add v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_sub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 50
    v2: int:s32 = iconst 8
    v3: int:s32 = sub v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_mul() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 6
    v2: int:s32 = iconst 7
    v3: int:s32 = mul v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_div() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 84
    v2: int:s32 = iconst 2
    v3: int:s32 = div v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_rem() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 47
    v2: int:s32 = iconst 5
    v3: int:s32 = rem v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 2);
}

#[test]
fn test_negative_iconst() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst -10
    v2: int:s32 = iconst 52
    v3: int:s32 = add v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

// ──────────────────────────────────────────────────────────────────────
// Bitwise operations
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_bitwise_and() {
    let r = run("func @main() -> int:u8 {
  bb0(v0: mem):
    v1: int:u8 = iconst 0xFF
    v2: int:u8 = iconst 0x0F
    v3: int:u8 = and v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 0x0F);
}

#[test]
fn test_bitwise_or() {
    let r = run("func @main() -> int:u8 {
  bb0(v0: mem):
    v1: int:u8 = iconst 0xF0
    v2: int:u8 = iconst 0x0F
    v3: int:u8 = or v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 0xFF);
}

#[test]
fn test_bitwise_xor() {
    let r = run("func @main() -> int:u8 {
  bb0(v0: mem):
    v1: int:u8 = iconst 0xFF
    v2: int:u8 = iconst 0xF0
    v3: int:u8 = xor v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 0x0F);
}

#[test]
fn test_shl() {
    let r = run("func @main() -> int:u32 {
  bb0(v0: mem):
    v1: int:u32 = iconst 1
    v2: int:u32 = iconst 5
    v3: int:u32 = shl v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 32);
}

#[test]
fn test_shr() {
    let r = run("func @main() -> int:u32 {
  bb0(v0: mem):
    v1: int:u32 = iconst 64
    v2: int:u32 = iconst 3
    v3: int:u32 = shr v1, v2
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 8);
}

// ──────────────────────────────────────────────────────────────────────
// Boolean operations
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_bconst_true() {
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: bool = bconst true
    ret v1, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

#[test]
fn test_band_bor() {
    // true BAND false = false, false BOR true = true
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: bool = bconst true
    v2: bool = bconst false
    v3: bool = band v1, v2
    v4: bool = bor v3, v1
    ret v4, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Comparisons
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_icmp_eq() {
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    v2: int:s32 = iconst 42
    v3: bool = icmp.eq v1, v2
    ret v3, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

#[test]
fn test_icmp_ne() {
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 2
    v3: bool = icmp.ne v1, v2
    ret v3, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

#[test]
fn test_icmp_slt() {
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: int:s32 = iconst -1
    v2: int:s32 = iconst 1
    v3: bool = icmp.lt v1, v2
    ret v3, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

#[test]
fn test_icmp_ult() {
    let r = run("func @main() -> bool {
  bb0(v0: mem):
    v1: int:u32 = iconst 1
    v2: int:u32 = iconst 100
    v3: bool = icmp.lt v1, v2
    ret v3, v0
}");
    match r {
        InterpResult::Ok(Some(Value::Bool(b))) => assert!(b),
        other => panic!("expected Ok(Bool(true)), got: {other}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Select
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_select_true() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: bool = bconst true
    v2: int:s32 = iconst 42
    v3: int:s32 = iconst 0
    v4: int:s32 = select v1, v2, v3
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_select_false() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: bool = bconst false
    v2: int:s32 = iconst 0
    v3: int:s32 = iconst 42
    v4: int:s32 = select v1, v2, v3
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

// ──────────────────────────────────────────────────────────────────────
// Control flow: branches
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_br() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    br bb1

  bb1:
    ret v1, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_brif_true_branch() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: bool = bconst true
    v2: int:s32 = iconst 42
    v3: int:s32 = iconst 0
    brif v1, bb1(v2), bb1(v3)

  bb1(v4: int:s32):
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_brif_false_branch() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: bool = bconst false
    v2: int:s32 = iconst 0
    v3: int:s32 = iconst 42
    brif v1, bb1(v2), bb1(v3)

  bb1(v4: int:s32):
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_br_with_block_args() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 10
    v2: int:s32 = iconst 32
    br bb1(v1, v2)

  bb1(v3: int:s32, v4: int:s32):
    v5: int:s32 = add v3, v4
    ret v5, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

// ──────────────────────────────────────────────────────────────────────
// Memory operations
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_stack_slot_store_load() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = iconst 42
    v3: mem = store.4 v2, v1, v0
    v4: int:s32 = load.4 v1, v3
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_store_load_8byte() {
    let r = run("func @main() -> int:s64 {
  bb0(v0: mem):
    v1: ptr = stack_slot 8
    v2: int:s64 = iconst 1234567890
    v3: mem = store.8 v2, v1, v0
    v4: int:s64 = load.8 v1, v3
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 1234567890);
}

#[test]
fn test_ptradd() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 8
    v2: int:s64 = iconst 4
    v3: ptr = ptradd v1, v2
    v4: int:s32 = iconst 99
    v5: mem = store.4 v4, v3, v0
    v6: int:s32 = load.4 v3, v5
    ret v6, v0
}");
    assert_eq!(unwrap_int(r), 99);
}

// ──────────────────────────────────────────────────────────────────────
// Poison semantics
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_div_by_zero_is_poison() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    v2: int:s32 = iconst 0
    v3: int:s32 = div v1, v2
    ret v3, v0
}");
    assert_ub(r);
}

#[test]
fn test_div_by_zero_poison_not_observed() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    v2: int:s32 = iconst 0
    v3: int:s32 = div v1, v2
    v4: int:s32 = iconst 99
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 99);
}

#[test]
fn test_poison_propagates_through_add() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    v2: int:s32 = iconst 0
    v3: int:s32 = div v1, v2
    v4: int:s32 = iconst 1
    v5: int:s32 = add v3, v4
    ret v5, v0
}");
    assert_ub(r);
}

#[test]
fn test_branch_on_poison_is_ub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 0
    v3: int:s32 = div v1, v2
    v4: bool = icmp.eq v3, v1
    brif v4, bb1, bb1

  bb1:
    v5: int:s32 = iconst 0
    ret v5, v0
}");
    assert_ub(r);
}

// ──────────────────────────────────────────────────────────────────────
// UB: unreachable, trap
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_unreachable_is_ub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    unreachable
}");
    assert_ub(r);
}

#[test]
fn test_trap_is_ub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    trap
}");
    assert_ub(r);
}

// ──────────────────────────────────────────────────────────────────────
// Type conversions
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_sext() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s8 = iconst -1
    v2: int:s32 = sext v1, 8
    ret v2, v0
}");
    assert_eq!(unwrap_int(r), -1);
}

#[test]
fn test_zext() {
    let r = run("func @main() -> int:u32 {
  bb0(v0: mem):
    v1: int:u8 = iconst 255
    v2: int:u32 = zext v1, 8
    ret v2, v0
}");
    assert_eq!(unwrap_int(r), 255);
}

// ──────────────────────────────────────────────────────────────────────
// Annotation enforcement
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_signed_annotation_truncation() {
    let r = run("func @main() -> int:s8 {
  bb0(v0: mem):
    v1: int:s8 = iconst 200
    ret v1, v0
}");
    assert_ub(r);
}

#[test]
fn test_dontcare_annotation_truncation() {
    let r = run("func @main() -> int:i8 {
  bb0(v0: mem):
    v1: int:i8 = iconst 256
    ret v1, v0
}");
    assert_eq!(unwrap_int(r), 0);
}

#[test]
fn test_unsigned_annotation() {
    let r = run("func @main() -> int:u8 {
  bb0(v0: mem):
    v1: int:u8 = iconst 255
    ret v1, v0
}");
    assert_eq!(unwrap_int(r), 255);
}

// ──────────────────────────────────────────────────────────────────────
// Loops (region loop with continue)
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_simple_loop() {
    // Sum 1..5 = 15 using a loop
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 0
    v2: int:s32 = iconst 1
    br bb1(v1, v2)

  region loop {
    bb1(v3: int:s32, v4: int:s32):
      v5: int:s32 = iconst 6
      v6: bool = icmp.lt v4, v5
      brif v6, bb2, bb3

    bb2:
      v7: int:s32 = add v3, v4
      v8: int:s32 = iconst 1
      v9: int:s32 = add v4, v8
      continue v7, v9

    bb3:
      region_yield v3
  }

  bb4(v10: int:s32):
    ret v10, v0
}");
    assert_eq!(unwrap_int(r), 15);
}

// ──────────────────────────────────────────────────────────────────────
// Function calls
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_function_call() {
    let r = run("func @add_one(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: int:s32 = add v1, v2
    ret v3, v0
}

func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = symbol_addr @add_one
    v2: int:s32 = iconst 41
    v3: mem, v4: int:s32 = call v1(v2), v0 -> int:s32
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

#[test]
fn test_recursive_function() {
    let r = run("func @fact(int:s32) -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = param 0
    v2: int:s32 = iconst 1
    v3: bool = icmp.le v1, v2
    brif v3, bb1, bb2

  bb1:
    ret v2, v0

  bb2:
    v4: int:s32 = sub v1, v2
    v5: ptr = symbol_addr @fact
    v6: mem, v7: int:s32 = call v5(v4), v0 -> int:s32
    v8: int:s32 = mul v1, v7
    ret v8, v0
}

func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = symbol_addr @fact
    v2: int:s32 = iconst 5
    v3: mem, v4: int:s32 = call v1(v2), v0 -> int:s32
    ret v4, v0
}");
    assert_eq!(unwrap_int(r), 120);
}

// ──────────────────────────────────────────────────────────────────────
// OOB memory access
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_oob_load_is_ub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 2
    v2: int:s32 = load.4 v1, v0
    ret v2, v0
}");
    assert_ub(r);
}

#[test]
fn test_oob_store_is_ub() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 2
    v2: int:s32 = iconst 42
    v3: mem = store.4 v2, v1, v0
    v4: int:s32 = iconst 0
    ret v4, v0
}");
    assert_ub(r);
}

// ──────────────────────────────────────────────────────────────────────
// Uninitialized memory
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_uninit_load_is_poison() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = load.4 v1, v0
    ret v2, v0
}");
    assert_ub(r);
}

#[test]
fn test_uninit_not_observed_ok() {
    let r = run("func @main() -> int:s32 {
  bb0(v0: mem):
    v1: ptr = stack_slot 4
    v2: int:s32 = load.4 v1, v0
    v3: int:s32 = iconst 42
    ret v3, v0
}");
    assert_eq!(unwrap_int(r), 42);
}

// ──────────────────────────────────────────────────────────────────────
// Void function return
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_void_return() {
    let r = run("func @main() {
  bb0(v0: mem):
    ret v0
}");
    match r {
        InterpResult::Ok(_) => {}
        other => panic!("expected Ok, got: {other}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Function not found
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_function_not_found() {
    let r = run("func @foo() {
  bb0(v0: mem):
    ret v0
}");
    match r {
        InterpResult::FunctionNotFound(name) => assert_eq!(name, "main"),
        other => panic!("expected FunctionNotFound, got: {other}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Count operations
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_count_ones() {
    let r = run("func @main() -> int:u32 {
  bb0(v0: mem):
    v1: int:u32 = iconst 0xFF
    v2: int:u32 = count_ones v1
    ret v2, v0
}");
    assert_eq!(unwrap_int(r), 8);
}

// ──────────────────────────────────────────────────────────────────────
// Normal mode: poison as warning
// ──────────────────────────────────────────────────────────────────────

#[test]
fn test_normal_mode_warns_on_poison() {
    let ir = "func @main() -> int:s32 {
  bb0(v0: mem):
    v1: int:s32 = iconst 42
    v2: int:s32 = iconst 0
    v3: int:s32 = div v1, v2
    ret v3, v0
}";
    let module = parse_module(ir).unwrap();
    let mut interp = Interpreter::new(&module, ExecMode::Normal);
    let result = interp.run("main");
    match result {
        InterpResult::Ok(Some(Value::Poison)) => {
            assert!(!interp.warnings.is_empty());
        }
        other => panic!("expected Ok(Poison) with warnings, got: {other}"),
    }
}
