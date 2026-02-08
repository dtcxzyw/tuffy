# Minimal IR Data Structures

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Implement the minimum IR data structures needed to represent a simple function (`fn add(a: i32, b: i32) -> i32 { a + b }`). Not the full IR RFC — just enough for the first end-to-end test.

Key deliverables:
- Type system: `int`, `b32`, `ptr` (minimal subset)
- Instructions: `add`, `assertsext`, `bytecast`, `load`, `store`, `ret`
- Single BasicBlock (no regions needed yet)
- Function definition with parameters and return type
- Value and InstructionRef as opaque u32 handles
- Arena-based storage for instructions
- Builder API with mandatory origin (can use a dummy origin for now)

Not included in this task:
- Hierarchical CFG (regions)
- MemSSA
- At-use annotations (KnownBits, DemandedBits)
- Vector types
- Atomic operations

## Affected Modules

- `tuffy_ir/src/`
