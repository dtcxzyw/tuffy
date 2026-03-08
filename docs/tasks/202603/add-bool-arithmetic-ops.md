# Task: Add Boolean Arithmetic Operations (band/bor/bxor)

**Status:** Not Started
**Created:** 2026-03-08
**Completed:** N/A

## Title

Add `band`, `bor`, and `bxor` IR instructions for boolean arithmetic operations

## Description

Implement boolean-specific arithmetic operations in the IR to support logical AND, OR, and XOR operations on boolean types. These operations are distinct from bitwise operations on integers and provide type-safe boolean arithmetic.

The three operations to add:
- `band` (boolean AND) - logical conjunction
- `bor` (boolean OR) - logical disjunction
- `bxor` (boolean XOR) - logical exclusive or

## Affected Modules

- `lean/TuffyLean/IR/` - Lean IR definition (source of truth)
  - Update instruction definitions
  - Add semantic rules for new operations
- `tuffy_ir/` - Rust IR implementation
  - Add new instruction variants
  - Update instruction builders and visitors
- `rustc_codegen_tuffy/` - MIR to IR translation
  - Map Rust boolean operations to new IR instructions
  - Update codegen for boolean binary operations
- `tuffy_target_x86/` - x86 backend
  - Add instruction selection patterns for band/bor/bxor
  - Generate appropriate x86 instructions
- Tests
  - Add codegen tests in `rustc_codegen_tuffy/tests/codegen/`
  - Add regression tests for boolean operations

## Implementation Steps

1. Define instructions in Lean IR (`lean/TuffyLean/IR/Instruction.lean`)
2. Implement in Rust IR (`tuffy_ir/src/instruction.rs`)
3. Update MIR-to-IR translation in `rustc_codegen_tuffy/src/mir_to_ir.rs`
4. Add instruction selection patterns in target backend
5. Add codegen tests and verify output
6. Update documentation if needed

## Notes

These operations should only accept boolean operands (i1 type) and produce boolean results. They are semantically distinct from bitwise operations on integers.
