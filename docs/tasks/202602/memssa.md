# Memory SSA

- Status: Draft
- Created: 2026-02-08
- Completed: N/A
- Parent: N/A

## Description

Add Memory SSA (MemSSA) support to the tuffy IR. MemSSA encodes memory dependencies
directly into the IR as memory version tokens on load/store operations, enabling
progressive refinement as alias analysis improves.

This task was deferred from the atomic operations implementation. The atomic operations
(`load.atomic`, `store.atomic`, `rmw`, `cmpxchg`, `fence`) are implemented as separate
Op variants without MemSSA tokens. When MemSSA is added, these operations will need to
be updated to carry memory version tokens.

### Goals

- Define a memory version token type in the IR
- Attach memory tokens to load, store, and atomic operations
- Implement a basic MemSSA construction pass (trivial: one memory version per block)
- Support progressive refinement as alias analysis improves
- Integrate with the optimizer for memory-aware transformations

### Design Considerations

- Memory tokens should be optional during early IR construction and required after
  MemSSA construction
- Atomic operations with ordering constraints impose additional ordering on memory
  tokens beyond simple data dependencies
- Fence operations create memory barriers that affect token ordering
- The MemSSA representation should support both may-alias and must-alias information

## Subtasks

- Define MemSSA token type in Lean formal model
- Add MemSSA token fields to Rust IR load/store/atomic operations
- Implement MemSSA construction pass
- Update display format to show memory tokens
- Add tests for MemSSA construction and refinement

## Affected Modules

- `lean/TuffyLean/IR/` — formal model for memory tokens
- `tuffy_ir/` — token type, instruction fields, builder, display
- `tuffy_opt/` — MemSSA construction pass
- `docs/spec.md` — specification update
