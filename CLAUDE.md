# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Maintaining CLAUDE.md

When the user provides a common instruction or policy that applies broadly to future work in this repository, update this file to capture it. This ensures future sessions inherit the instruction without the user needing to repeat it.

## Language Policy

**IMPORTANT:** When interacting with the user, you MUST match the language they are using. If the user writes in Chinese, respond in Chinese. If the user writes in English, respond in English.

Always use English when editing files (code, comments, documentation).

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

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

## Documentation

- `docs/tasks/` — task tracking documents
- `docs/RFCs/` — design proposals and RFCs

Documents are archived by year-month under their respective directories, written in Markdown. Each document must include: current status, created time, and completed time. Example path: `docs/tasks/202602/init.md`.

Task documents must additionally include: title, task description, and affected modules (modules expected to be modified).

Templates are available for reference:
- `docs/tasks/template.md` — task document template
- `docs/RFCs/template.md` — RFC document template (based on Rust RFC format)

## Architecture

The project is in early stages. The Rust project structure (Cargo.toml, src/) has not yet been initialized.

Source code architecture overviews are documented in the `README.md` within each component's directory.
