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

### Design

#### `mem` type

Introduce a new `mem` type as a first-class SSA value type, alongside `int`, `ptr`,
and `b<N>`. Memory tokens flow through the function as regular SSA values, using the
same mechanisms as other values: block parameters for phi, function entry parameter
for initial memory state, and return operand for function exit.

Single memory partition — no memory partitioning. Precision is recovered via alias
analysis backed refinement (clobber walking), not upfront partitioning. This follows
LLVM MemorySSA's design: precise partitioning is impractical and not worth the cost.

#### Instruction classification

MemoryDef — consumes a `mem` token, produces a new `mem` token:
- `store`
- `store.atomic`
- `load.atomic` (has ordering constraints, treated as def)
- `rmw`
- `cmpxchg`
- `fence`
- `call` (all calls, including readonly — conservative default)

MemoryUse — consumes a `mem` token, does not produce one:
- `load` (plain, non-atomic)

A `mem` def is allowed to have no uses (no artificial consumers needed).

Other external side effects beyond memory (e.g., I/O, system calls, inline assembly)
are also modeled as MemoryDef/MemoryUse, treated as accesses to inaccessible memory.
This unifies all side-effect ordering into the single `mem` token chain, so control
flow is the only dependency not captured by `mem` tokens.

#### Entry, exit, and phi

- Entry: the entry block receives the initial memory state as a block parameter of
  type `mem`.
- Exit: `ret` carries the final `mem` token as an operand. This prevents DCE from
  incorrectly eliminating stores.
- Phi: memory version merging at CFG join points uses regular block parameters of
  type `mem`, not a special `mem.phi` instruction.

#### Refinement as transformation

MemSSA refinement follows the "analysis is also a transformation" principle. When
alias analysis proves that an intervening MemoryDef does not clobber a load's memory
location, the load's `mem` operand is rewritten to point to an earlier def. This is
a regular IR transformation — no side tables, no special update protocol.

#### IR example

```
func @example() {
entry(%mem0: mem):
  %mem1 = store b32 %v, ptr %p, %mem0
  %x = load b32, ptr %q, %mem1
  %mem2, %y = load.atomic b32, ptr %r, acquire, %mem1
  %mem3 = store b32 %x, ptr %s, %mem2
  br cond, bb1, bb2

bb1:
  %mem4 = store b32 %a, ptr %t, %mem3
  br bb3(%mem4)

bb2:
  br bb3(%mem3)

bb3(%mem5: mem):
  ret %mem5
}
```

#### Reference

- [LLVM MemorySSA](https://llvm.org/docs/MemorySSA.html) — single partition design,
  MemoryDef/MemoryUse/MemoryPhi, clobber walker with alias analysis.

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
