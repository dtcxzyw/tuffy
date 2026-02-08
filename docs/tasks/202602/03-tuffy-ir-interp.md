# IR Interpreter (tuffy_ir_interp)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the tuffy IR interpreter based on the interpreter RFC (`docs/RFCs/202602/interpreter.md`). Miri-like execution engine with full UB detection.

Key deliverables:
- Value representation: Int(BigInt), Bytes, Ptr, Float, Double, Vec, Poison
- Memory model: arena-based allocations with four-state AbstractByte tracking
- Pointer provenance enforcement: allocation ID + offset, bounds checking
- Poison propagation and UB detection (assert violations, uninit reads, OOB, use-after-free)
- Execution modes: Normal, Strict, Differential, Reduce
- Differential testing support: compare pre/post optimization IR execution
- Hierarchical CFG walker (Region.Loop, Region.Branch, Region.Sequence)

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_ir_interp/src/` — interpreter implementation
