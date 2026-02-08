# SOP: Modifying the Tuffy IR

- Created: 2026-02-08
- Status: Active

## Overview

This document describes the standard operating procedure for making changes to the Tuffy IR.
Because the IR is the core data structure shared across the entire compiler, changes must be
propagated to multiple components in a specific order.

## Guiding Principle

The Lean 4 formal definitions are the **source of truth**. All other artifacts (Rust code, spec
document) must conform to the Lean definitions. When in doubt, the Lean code is authoritative.

## Checklist

### 1. Lean 4 Formal Definitions (Source of Truth)

Update the formal model first. Depending on the nature of the change:

| What changed | File to update |
|---|---|
| Types, values, memory model | `lean/TuffyLean/IR/Types.lean` |
| Instruction semantics | `lean/TuffyLean/IR/Semantics.lean` |

After editing, verify with:

```bash
cd lean && lake build
```

If the change affects existing proofs, fix all proof breakages before proceeding.

### 2. Rust Implementation (`tuffy_ir`)

Translate the Lean changes into the Rust IR crate. Files to consider:

| What changed | File to update |
|---|---|
| Type system (new type or type change) | `tuffy_ir/src/types.rs` |
| New/modified instruction or opcode | `tuffy_ir/src/instruction.rs` |
| Reference handles (ValueRef, BlockRef, etc.) | `tuffy_ir/src/value.rs` |
| Function/block/region structure | `tuffy_ir/src/function.rs` |
| Builder API for constructing IR | `tuffy_ir/src/builder.rs` |
| Textual format / display | `tuffy_ir/src/display.rs` |

Run after changes:

```bash
cargo test -p tuffy_ir
cargo clippy -p tuffy_ir
```

### 3. Downstream Crates

IR changes typically break downstream consumers. Update in dependency order:

1. **Interpreter** (`tuffy_ir_interp/src/lib.rs`)
   — Add/update evaluation logic for new or changed instructions.

2. **Optimizer** (`tuffy_opt/`)
   — Update any passes that pattern-match on changed instructions.

3. **Code Generation** (`tuffy_codegen/`)
   — Update instruction selection (`src/isel.rs`), encoding (`src/encode.rs`),
     or emission (`src/emit.rs`) as needed.

4. **Trace / TV** (`tuffy_trace/`, `tuffy_tv/`)
   — Update if the change affects tracing or visualization.

### 4. Spec Document

Update the human-readable reference:

- `docs/spec.md`

Ensure the spec accurately reflects the new Lean definitions and Rust implementation.
The spec is not authoritative — it is documentation derived from the Lean model.

### 5. Tests

Add or update tests at every layer:

| Layer | Location |
|---|---|
| Rust unit tests | `tuffy_ir/src/tests.rs` |
| Interpreter tests | `tuffy_ir_interp/tests/` |
| Codegen tests | `tuffy_codegen/src/tests.rs` |
| UI tests | `tests/ui/` (run via `tests/run-ui-tests.sh`) |

### 6. Final Verification

Before committing, all of the following must pass:

```bash
cd lean && lake build
cargo test
cargo clippy
tests/run-ui-tests.sh
```

## Commit Strategy

Each component should be committed separately per the project's commit convention.
A typical IR change produces commits in this order:

1. `feat(lean): ...` — Lean formal definitions
2. `feat(ir): ...` — Rust `tuffy_ir` crate
3. `feat(interp): ...` / `feat(codegen): ...` — downstream crates
4. `docs: ...` — spec update

Every individual commit must pass all tests.
