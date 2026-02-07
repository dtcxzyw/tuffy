# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Language Policy

Always use English when editing files (code, comments, documentation). When interacting with the user, match the language they are using.

## Project Overview

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

## Development Environment

Development uses VS Code dev containers built on `mcr.microsoft.com/devcontainers/rust:latest`. The container includes cmake, ninja-build, gdb/gdbserver, and mounts the workspace at `/tuffy`. Cargo cache is persisted via a Docker volume.

To open the dev container, use the VS Code "Reopen in Container" command.

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

## Architecture

The project is in early stages. The Rust project structure (Cargo.toml, src/) has not yet been initialized.
