# Core IR Implementation (tuffy_ir)

- Status: In Progress
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the core IR data structures based on the IR design RFC (`docs/RFCs/202602/ir-design.md`). This is the foundation crate that all other tuffy crates depend on.

Key deliverables:
- Type system: `int`, `b<N>`, `ptr<AS>`, `float`, `double`, `vec<vscale x N x T>`
- Instruction set: arithmetic, pointer ops (ptradd, ptrdiff, ptrtoint, ptrtoaddr, inttoptr), load/store, assert nodes, atomic ops, vector ops
- Hierarchical CFG: Region (Loop, Branch, Sequence), BasicBlock, Terminator
- Memory model: four-state AbstractByte, MemSSA tokens
- At-use annotations: UseAnnotation with demanded_bits, known_bits, dirty flag
- Origin chain: Origin struct on every instruction, mandatory in builder API
- Arena + index storage: opaque handles, contiguous BB instruction storage, tombstone + compaction
- IR builder API enforcing origin and type safety

## Subtasks

- N/A (leaf task)

## Affected Modules

- `tuffy_ir/src/` — all IR data structures and builder API
