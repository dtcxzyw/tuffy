# Move Floating-Point Operands to XMM Registers

- Status: Completed
- Created: 2026-03-03
- Completed: 2026-03-03
- Parent: register-bank-abstraction.md

## Description

Currently, floating-point operations in the x86 backend store operands in GPRs as bit patterns and move them through memory (red-zone) to perform XMM operations. This is inefficient and unnatural for FP operations.

### Current Architecture

```
FP Binary Op (e.g., fadd):
1. lhs (GPR) → [rsp-8]
2. rhs (GPR) → [rsp-16]
3. [rsp-8] → XMM0
4. XMM0 = XMM0 op [rsp-16]
5. XMM0 → [rsp-8]
6. [rsp-8] → dst (GPR)
```

This requires 6 memory operations for a single FP operation.

### Proposed Architecture

```
FP Binary Op (e.g., fadd):
1. dst (XMM) = lhs (XMM) op rhs (XMM)
```

Direct XMM register operations with no memory traffic.

## Requirements

1. **Instruction Definitions**: Update FP instructions to use XMM operands
   - `FpBinOp`: lhs/rhs/dst should be XMM registers
   - `FpCmp`: lhs/rhs should be XMM registers, dst remains GPR (boolean result)
   - `CvtFpToFp`: src/dst should be XMM registers
   - `CvtFpToInt`: src should be XMM, dst should be GPR
   - `CvtIntToFp`: src should be GPR, dst should be XMM

2. **Type System**: Distinguish between GPR and XMM operands in instruction types
   - Option A: Add separate XMM register type
   - Option B: Use context-dependent interpretation of Gpr enum
   - Option C: Add register class tags to instructions

3. **Instruction Selection**: Allocate XMM registers for FP values
   - FP constants → XMM registers
   - FP function parameters → XMM registers (per calling convention)
   - FP intermediate values → XMM registers

4. **Register Allocation**: Already supported via register bank abstraction
   - XMM registers use PReg class=1
   - Aliasing handled correctly

5. **Encoding**: Simplify FP operation encoding
   - Remove memory traffic for XMM-to-XMM operations
   - Direct XMM register encoding
   - Keep memory operations only for GPR↔XMM conversions

## Affected Modules

- `tuffy_target_x86/src/inst.rs` - Instruction definitions
- `tuffy_target_x86/src/isel.rs` - Instruction selection
- `tuffy_target_x86/src/encode.rs` - Encoding functions
- `tuffy_target_x86/src/regalloc_impl.rs` - Register operand tracking
- `tuffy_target_x86/src/backend.rs` - Instruction rewriting

## Implementation Plan

### Phase 1: Type System Design

Decide on approach for representing mixed GPR/XMM operands:
- Evaluate trade-offs of each option
- Choose approach that minimizes code changes
- Document design decision

### Phase 2: Instruction Definitions

Update instruction types in `inst.rs`:
- Add XMM operand fields to FP instructions
- Maintain backward compatibility where possible
- Update Display implementations

### Phase 3: Instruction Selection

Update `isel.rs` to allocate XMM registers:
- FP binary operations → XMM operands
- FP comparisons → XMM operands
- FP conversions → mixed GPR/XMM operands
- Update constraint generation for XMM registers

### Phase 4: Register Allocation Integration

Update `regalloc_impl.rs`:
- Track XMM register operands correctly
- Generate proper use/def information
- Handle mixed GPR/XMM instructions

### Phase 5: Encoding Simplification

Update `encode.rs`:
- Remove memory traffic from XMM-to-XMM operations
- Direct XMM register encoding
- Simplify FP operation sequences
- Keep memory operations only for conversions

### Phase 6: Testing

- Update existing tests
- Add tests for XMM register allocation
- Verify performance improvements
- Ensure correctness with floating-point edge cases

## Benefits

1. **Performance**: Eliminate unnecessary memory traffic
2. **Code Quality**: More natural representation of FP operations
3. **Maintainability**: Clearer separation between integer and FP operations
4. **Optimization**: Enable future FP-specific optimizations

## Risks

1. **Complexity**: Large refactoring touching multiple modules
2. **Calling Convention**: Must handle FP parameters/returns correctly
3. **Spilling**: XMM register spills need proper handling
4. **Testing**: Comprehensive testing required for correctness

## Notes

This task depends on the register bank abstraction (register-bank-abstraction.md) which provides the foundation for XMM register allocation and aliasing.

The refactoring should be done incrementally, with each phase tested independently to ensure correctness.
