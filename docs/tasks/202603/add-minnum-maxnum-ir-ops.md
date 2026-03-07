# Add MinNum/MaxNum IR Operations

- Status: Draft
- Created: 2026-03-07
- Completed: N/A
- Parent: N/A

## Description

Currently, Rust MIR's `minnumf32/minnumf64/maxnumf32/maxnumf64` intrinsics are translated to IR using `fcmp` + `select` simulation in `rustc_codegen_tuffy`. This approach does not correctly handle IEEE 754-2008 minNum/maxNum semantics, particularly NaN propagation behavior.

### IEEE 754-2008 minNum/maxNum Semantics

- **NaN Handling (NaN-suppressing)**: If one operand is a quiet NaN and the other is a finite number, return the numeric operand (not the NaN)
- **Signaling NaN**: If input contains sNaN, return qNaN
- **Signed Zero**: Implementation-defined behavior for operations like `maxNum(+0, -0)`. LLVM treats -0.0 as less than +0.0

### Current Implementation Problem

The current `fcmp OLt/OGt + select` approach:
- Uses ordered comparison (OLt/OGt) which returns false when either operand is NaN
- When `a` is NaN and `b` is numeric: `fcmp OLt NaN, b` → false → select returns `b` (correct for minnum)
- When `b` is NaN and `a` is numeric: `fcmp OLt a, NaN` → false → select returns `NaN` (incorrect, should return `a`)

This asymmetric NaN handling violates IEEE 754-2008 semantics.

## Subtasks

1. Add `FMinNum` and `FMaxNum` operations to `tuffy_ir::instruction::Op`
2. Update Lean IR definition in `lean/TuffyLean/IR/` to include MinNum/MaxNum operations
3. Update `rustc_codegen_tuffy/src/mir_to_ir/intrinsic.rs` to emit `FMinNum`/`FMaxNum` instead of fcmp+select
4. Add codegen support in `tuffy_target_x86` for MinNum/MaxNum (map to appropriate x86 instructions or library calls)
5. Update IR printer/parser to handle new operations
6. Add regression tests for NaN handling edge cases

## Affected Modules

- `tuffy_ir/src/instruction.rs` - Add FMinNum/FMaxNum to Op enum
- `lean/TuffyLean/IR/` - Update Lean IR definition (source of truth)
- `docs/spec/` - Update IR specification to document MinNum/MaxNum semantics
- `rustc_codegen_tuffy/src/mir_to_ir/intrinsic.rs` - Replace fcmp+select with direct IR ops
- `tuffy_target_x86/src/` - Add codegen for new operations
- `rustc_codegen_tuffy/tests/codegen/intrinsic/float_minmax.rs` - Update test expectations

## References

- [IEEE 754-2008 minNum/maxNum specification](https://en.wikipedia.org/wiki/IEEE_754)
- [LLVM minnum/maxnum intrinsics](https://llvm.org/docs/LangRef.html#llvm-minnum-intrinsic)
- IEEE 754-2019 removed minNum/maxNum due to non-associativity issues, replacing with minimumNumber/maximumNumber and minimum/maximum
