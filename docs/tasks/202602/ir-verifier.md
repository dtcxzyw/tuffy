# Implement IR Verifier

- Status: Completed
- Created: 2026-02-10
- Completed: 2026-02-10
- Parent: N/A

## Description

Implement an IR verifier module for tuffy_ir that performs integrity and validity checks on the IR after construction (or before/after transformations).

Currently tuffy_ir lacks an explicit verification mechanism — IR correctness relies primarily on implicit guarantees from the Rust type system and arena storage. As IR complexity grows and optimization passes are introduced, an independent verifier is needed to catch illegal IR, aid debugging, and ensure transformation correctness.

### Goals

1. **Type consistency checks**: Verify that each instruction's operand types match the instruction semantics (per the Lean 4 semantic definitions).
2. **Value reference validity**: Ensure all ValueRef, BlockRef, RegionRef, and InstRef point to valid entities with no dangling references.
3. **SSA properties**: Verify that each value is defined exactly once and that all uses are dominated by their definitions.
4. **Control flow integrity**:
   - Each BasicBlock ends with exactly one terminator instruction.
   - Branch target blocks exist and block argument counts/types match.
   - Region SESE property: single entry, single exit.
5. **Region hierarchy**: Verify the region tree is well-formed, blocks belong to the correct regions, and nesting relationships are consistent.
6. **Function signature consistency**: Call instruction argument counts/types match the callee's signature; Ret instruction return types match the function declaration.
7. **Memory operation checks**: Load/Store operands must be Ptr type; atomic operation MemoryOrdering values must be valid.
8. **Annotation validity**: Annotations must be type-compatible with their associated values.
9. **Module-level checks**: No duplicate definitions in the symbol table; function names must be unique.

### Design Notes

- The verifier should collect all errors rather than stopping at the first one, enabling a single comprehensive report.
- Error messages should include sufficient context (function name, block index, instruction index, specific violation description).
- Provide two entry points: `Module::verify()` and `Function::verify()`.
- Verification rules should follow the Lean 4 definitions (`lean/TuffyLean/IR/`) as the source of truth.

## Subtasks

- Implement the base verifier framework (error collection and reporting)
- Implement type consistency checks
- Implement value reference validity checks
- Implement SSA dominance checks
- Implement control flow integrity checks
- Implement region hierarchy checks
- Implement function signature consistency checks
- Implement memory operation and annotation checks
- Implement module-level checks
- Add test cases

## Affected Modules

- `tuffy_ir` — Add verifier module; may require adding helper query methods to existing types
