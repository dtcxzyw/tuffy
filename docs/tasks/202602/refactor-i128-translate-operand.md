# Refactor translate_operand to return Type::Int for i128/u128

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-03-01
- Parent: N/A

## Description

Currently, i128/u128 locals are marked as stack-allocated in `ctx.rs:311` because they exceed 8 bytes. As a result, `translate_operand` returns a `Type::Ptr` (pointer to the stack slot) instead of a `Type::Int` value. This forces every consumer site (BinOp, Cast, UnaryOp, SwitchInt, function calls, intrinsics, etc.) to check `is_i128_or_u128` and manually load the value from the stack slot before operating on it.

The goal is to make `translate_operand` automatically load i128/u128 values from their stack slots, returning `Type::Int` directly — the same representation as all other integer types. This will eliminate most `is_i128_or_u128` special cases scattered across mir_to_ir.

### Current behavior

1. `ctx.rs` — i128/u128 locals are marked in `stack_locals` (line 311)
2. `translate_operand` — for stack locals, only loads values when `size <= 8` and `slot_size <= 8` (rvalue.rs:2054-2057), so i128 (16 bytes) falls through and returns the raw Ptr
3. Every consumer must check `is_i128_or_u128` and load manually

### Target behavior

1. `translate_operand` — extend the stack-local load path to handle i128/u128 (size=16): emit a 16-byte load as `Type::Int`
2. Remove downstream `is_i128_or_u128` load-from-ptr checks that become redundant

### Sites with i128 special handling to audit

Each site must be evaluated: some checks are about the Ptr→Int load (removable), others are about ABI/legalization semantics (must keep).

**Likely removable** (load-from-ptr workarounds):
- `rvalue.rs:948-973` — BinOp operand load from stack slot
- `rvalue.rs:1189-1193` — Cast source load from stack slot
- `rvalue.rs:1934` — UnaryOp load from stack slot
- `terminator.rs:485` — SwitchInt operand load
- `intrinsic.rs:101` — intrinsic operand load

**Likely must keep** (ABI/legalization semantics):
- `mod.rs:145-151` — parameter slot count (i128 is 1 slot, not 2 like two-reg structs)
- `mod.rs:448-457` — stack slot store width (16 bytes for i128)
- `mod.rs:496-499` — return value handling (i128 doesn't use sret)
- `ctx.rs:311` — i128 must remain stack-allocated (value exceeds register width)
- `call.rs:907-911` — argument annotation for legalization
- `call.rs:1045-1047` — return annotation for legalization
- `call.rs:1094` — sret exclusion for i128

## Subtasks

1. Extend `translate_operand` stack-local load path to handle size=16 i128/u128
2. Audit and remove redundant `is_i128_or_u128` load-from-ptr checks at consumer sites
3. Verify `cargo test` and `cargo clippy` pass
4. Run rustlantis fuzzing seeds to confirm no regressions

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir/rvalue.rs` — translate_operand fix + BinOp/Cast/UnaryOp cleanup
- `rustc_codegen_tuffy/src/mir_to_ir/terminator.rs` — SwitchInt cleanup
- `rustc_codegen_tuffy/src/mir_to_ir/intrinsic.rs` — intrinsic operand cleanup
- `rustc_codegen_tuffy/src/mir_to_ir/mod.rs` — review parameter/return handling (likely keep)
- `rustc_codegen_tuffy/src/mir_to_ir/ctx.rs` — review stack_locals marking (likely keep)
- `rustc_codegen_tuffy/src/mir_to_ir/call.rs` — review annotation logic (likely keep)
