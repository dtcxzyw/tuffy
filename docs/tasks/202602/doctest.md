# Rust Doctest Support

- Status: Draft
- Created: 2026-02-08
- Completed: N/A
- Parent: N/A

## Description

Add support for compiling and running Rust doctests (`cargo test --doc`) with tuffy as the codegen backend.

This is a later-stage task that depends on the hello-world milestone being completed first. Doctests require the compiler to extract code blocks from documentation comments, compile them as standalone programs, and execute them. This involves additional codegen backend hooks beyond what basic compilation requires.

## Subtasks

- (to be determined after hello-world milestone is complete)

## Affected Modules

- `rustc_codegen_tuffy/src/lib.rs` — CodegenBackend trait methods for doctest support
