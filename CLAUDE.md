# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Maintaining CLAUDE.md

When the user provides a common instruction or policy that applies broadly to future work in this repository, update this file to capture it. This ensures future sessions inherit the instruction without the user needing to repeat it.

## Language Policy

**IMPORTANT:** When interacting with the user, you MUST match the language they are using. If the user writes in Chinese, respond in Chinese. If the user writes in English, respond in English.

Always use English when editing files (code, comments, documentation).

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

Short-term goals and milestones belong in `docs/tasks/`, not in `README.md`. `README.md` should only contain long-term vision and project-level information.

## Development Environment

Development uses VS Code dev containers built on `mcr.microsoft.com/devcontainers/rust:latest`. The container includes cmake, ninja-build, gdb/gdbserver, and mounts the workspace at `/tuffy`. Cargo cache is persisted via a Docker volume.

To open the dev container, use the VS Code "Reopen in Container" command.

## Commit Convention

Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Common types: `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`, `ci`, `chore`. Append `!` before the colon for breaking changes.

Commit messages must include a body explaining what was changed and why. Do not write title-only commits.

Before committing, ensure `cargo test` and `cargo clippy` pass without errors.

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

### Lean 4 (formal verification)

```
cd lean && lake build    # Build Lean project
cd lean && lake clean    # Clean build artifacts
```

Lean 4 is managed via elan (toolchain manager). The Lean project is under `lean/` with Mathlib dependency.

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

## Architecture

The project is in the initial stage. The Rust project structure (Cargo.toml, src/) has not yet been initialized.

Project-related design discussions should be synced to `docs/initial.md`.

Source code architecture overviews are documented in the `README.md` within each component's directory.
