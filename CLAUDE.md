# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Maintaining CLAUDE.md

When the user provides a common instruction or policy that applies broadly to future work in this repository, update this file to capture it. This ensures future sessions inherit the instruction without the user needing to repeat it.

## Problem Solving Policy

**IMPORTANT:** You have sufficient time to thoroughly analyze and debug problems. Do not choose temporary workarounds or give up due to perceived time constraints. When encountering bugs or issues:

- Investigate root causes systematically rather than documenting problems and moving on
- Persist through complex debugging sessions even if they take multiple attempts
- Avoid shortcuts or partial solutions when complete fixes are achievable
- Only escalate or defer issues when genuinely blocked by external factors

## Language Policy

**IMPORTANT:** When interacting with the user, you MUST match the language they are using. If the user writes in Chinese, respond in Chinese. If the user writes in English, respond in English.

Always use English when editing files (code, comments, documentation). All content committed to git must be in English — this includes code, comments, documentation, commit messages, and task/RFC documents.

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

Short-term goals and milestones belong in `docs/tasks/`, not in `README.md`. `README.md` should only contain long-term vision and project-level information.

## Development Environment

Development uses VS Code dev containers built on `mcr.microsoft.com/devcontainers/rust:latest`. The container includes cmake, ninja-build, gdb/gdbserver, and mounts the workspace at `/tuffy`. Cargo cache is persisted via a Docker volume.

To open the dev container, use the VS Code "Reopen in Container" command.

## Branching Strategy

All development happens on the `main` branch. Keep a linear history (no merge commits). Use `git rebase` instead of `git merge` when needed.

## Commit Convention

Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Common types: `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`, `ci`, `chore`. Append `!` before the colon for breaking changes.

Commit messages must include a body explaining what was changed and why. Do not write title-only commits.

Before committing, ensure `cargo test` and `cargo clippy` pass without errors. `rustc_codegen_tuffy/tests/run-ui-tests.sh` is only run in CI — do not run it before committing.

Before running UI tests (`run-ui-tests.sh`), always update the Rust nightly toolchain (`rustup update nightly`) and rebuild the codegen backend. The UI test suite is pulled from upstream rust-lang/rust and may use features only available in the latest nightly.

Changes to different components must be committed separately. Each individual commit must pass all existing tests (`cargo test`, `cargo clippy`, `rustc_codegen_tuffy/tests/run-ui-tests.sh`). Do not bundle unrelated component changes into a single commit.

Automatically decide when to commit based on logical units of work. Do not ask the user for permission to commit — just commit when a coherent change is complete.

Never amend previous commits (`git commit --amend`). Always create new commits to keep a linear, auditable history.

## Binary Files and Build Artifacts

Place binary outputs in `/tmp` or `scratch/` directory. Do not generate build artifacts in the working directory unless they follow established conventions.

For conventional build directories (e.g., Rust `target/`, Python `.venv/`, Lean `.lake/`), ensure they are listed in `.gitignore`.

**Never commit binary files to git unless explicitly authorized by the user.** This includes compiled executables, libraries (.so, .rlib, .a), object files, and other build artifacts.

## Build Commands

```
cargo build              # Debug build
cargo build --release    # Release build
cargo run                # Run debug build
cargo test               # Run all tests
cargo test <test_name>   # Run a single test
cargo clippy             # Lint
cargo fmt                # Format code
```

### rustc_codegen_tuffy (codegen backend)

`rustc_codegen_tuffy/` is **not** part of the Cargo workspace. It has its own `Cargo.toml` (crate-type `dylib`) and its own `target/` directory. Build it separately:

```
cargo build --manifest-path rustc_codegen_tuffy/Cargo.toml
```

The resulting `.so` is at `rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so`. Use it with rustc:

```
rustc +nightly -Z codegen-backend=rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so \
    -C llvm-args=dump-ir -o out input.rs
```

`cargo build` / `cargo test` / `cargo clippy` at the workspace root do **not** touch this crate.

### Lean 4 (formal verification)

```
cd lean && lake build    # Build Lean project
cd lean && lake clean    # Clean build artifacts
```

Lean 4 is managed via elan (toolchain manager). The Lean project is under `lean/` with Mathlib dependency.

`lean/TuffyLean/README.md` defines module-level conventions for the Lean codebase (directory roles and isel export conventions). Treat it as the canonical guide when modifying files under `lean/TuffyLean/`.

## Documentation

- `docs/tasks/` — task tracking documents
- `docs/RFCs/` — design proposals and RFCs

Documents are archived by year-month under their respective directories, written in Markdown. Each document must include: current status, created time, and completed time. Example path: `docs/tasks/202602/init.md`.

Task documents must additionally include: title, task description, and affected modules (modules expected to be modified).

When starting work on a task, update its status to `In Progress`. When the task is completed, update its status to `Completed` and fill in the completed date.

Templates are available for reference:
- `docs/tasks/template.md` — task document template
- `docs/RFCs/template.md` — RFC document template (based on Rust RFC format)

When the user provides reference documents, categorize and add them to `docs/references.md`. Download a local copy to `scratch/` when possible. Each reference entry should include a brief summary of key conclusions and their relevance to tuffy.

## Code Review Mode

When the user is reviewing code and providing feedback, record each piece of feedback as a task document in `docs/tasks/`. Do not modify code directly and do not enter plan mode during code review.

## Standard Operating Procedures

Before starting a task, check `docs/SOPs/` for a matching SOP. If one exists, follow the procedure defined in it.

## Tool Output Policy

When outputting content using tools, output in multiple smaller segments rather than one large block. Avoid writing excessively large amounts of content in a single tool call.

## Coding Rules

Do not use `static` global variables for mutable state (including `AtomicU64`, `Mutex`, etc.). Counters and other session state must live on a context struct, not at module scope. This ensures deterministic behavior and avoids cross-compilation-unit interference.

**Generated Files:** When encountering a file with "DO NOT EDIT" in its header comment, identify which command or tool generates it before making any changes. Never directly modify generated files — instead, modify the source or generator. For example, `tuffy_target_x86/src/isel_gen.rs` is generated and must not be edited manually.

**Component Conventions:** When modifying code in any component, you MUST follow the conventions and requirements defined in that component's `README.md`. Do not use workarounds or insert special-case logic in inappropriate components. Each component has its own architectural rules — respect them and implement changes in the correct location according to the component's design.

## Architecture

The IR definition in Lean 4 (`lean/TuffyLean/IR/`) is the **source of truth**. The Rust implementation (`tuffy_ir/`) and the spec (`docs/spec/`) must conform to the Lean definitions. When there is a conflict, the Lean code takes precedence.

`docs/initial.md` is frozen — it records early design decisions and must not be modified. New design discussions belong in `docs/RFCs/`.

Source code architecture overviews are documented in the `README.md` within each component's directory.
