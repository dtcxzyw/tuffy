# CLAUDE.md

Guidance for AI assistants working with this repository. When the user provides a common instruction or policy, update this file to capture it.

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust.

## Architecture

The IR definition in Lean 4 (`lean/TuffyLean/IR/`) is the **source of truth**. Rust (`tuffy_ir/`) and the spec (`docs/spec/`) must conform to Lean. When there is a conflict, Lean takes precedence.

`docs/initial.md` is frozen — new design discussions belong in `docs/RFCs/`.

Each component's architecture is documented in its `README.md`. Read the relevant README before modifying any component.

**Do not assume LLVM semantics.** Tuffy has its own design. Read `docs/spec/`, component READMEs, and Lean definitions before acting. If unclear, ask the user rather than guessing.

## Language Policy

Match the user's language in conversation. All committed content (code, comments, docs, commit messages) must be in English.

## Coding Rules

- No `static` mutable state (`AtomicU64`, `Mutex`, etc.). Session state belongs on context structs.
- **Generated files:** Files with "DO NOT EDIT" headers must not be edited manually — modify the generator instead (e.g., `tuffy_target_x86/src/isel_gen.rs`).
- **Component conventions:** Follow each component's `README.md`. Do not insert workarounds or special-case logic in the wrong component.
- **Wide integer lowering:** Derive split widths, limb widths, and ABI thresholds from target legality or backend abstractions. Do not hardcode `32`, `64`, or `128` for target-independent wide integer logic.
- **Comments:** Do not add comments that the code itself explains. Only comment non-obvious logic — comments should explain *why*, not *what*. Do not delete or modify comments in code you are not otherwise changing.

## Testing Policy

- Never delete or skip existing tests without explicit user authorization.
- After fixing a bug, add a regression test. For codegen bugs: add to `rustc_codegen_tuffy/tests/codegen`, use `update-codegen-test.sh` for check lines.
- **Bug-fix workflow:** Before fixing a bug, write tests that expose it and verify they fail. After applying the fix, verify the tests pass.

## Git Workflow

- All development on `main`. Linear history — use rebase, never merge.
- Never amend commits. Always create new commits.
- Commit logical units of work automatically — do not ask for permission.
- Separate commits for different components. Each commit must pass `cargo test` and `cargo clippy`.
- See [conventions.md](docs/agents/conventions.md#commit-convention) for commit message format.

## Pre-commit Checks

```
cargo test && cargo clippy
```

`rustc_codegen_tuffy/tests/run-ui-tests.sh` is CI-only — do not run locally before committing.

## Context Management

After context compaction, re-read:
1. This file (`CLAUDE.md`)
2. The `README.md` of any component being modified
3. Any previously referenced `docs/` files

## Problem Solving

Investigate root causes, not symptoms. Persist through debugging — no workarounds or premature surrender. Verify solutions with tests before claiming success. No placeholder implementations or TODO stubs unless explicitly requested.

**Ask the user** when: multiple valid approaches exist, requirements are ambiguous, changes affect APIs or architecture, or breaking changes may be needed.

**Proceed autonomously** when: the approach is clear from existing patterns, the change is internal and low-risk, or component docs provide explicit guidance.

## Task Workflow

Before starting a task, check `docs/SOPs/` for a matching procedure. Read relevant component READMEs and `docs/spec/`. Understand the problem fully before writing code. Do not assume you already know the design details — if unsure, ask the user rather than guessing.

## Detailed References

- [Build commands](docs/agents/build.md) — workspace, codegen backend, Lean
- [Conventions](docs/agents/conventions.md) — commits, documentation, dependencies, artifacts, SOPs
