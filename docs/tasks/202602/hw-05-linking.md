# Implement Linking

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/hello-world.md

## Description

The backend does not implement `CodegenBackend::link()`. Without linking, rustc cannot produce executables — only individual object files. The linker step must combine tuffy-generated objects with std/core/alloc rlibs and libc into a final ELF executable.

Key deliverables:
- Implement `link()` in `TuffyCodegenBackend` (or delegate to `rustc_codegen_ssa::back::link`)
- Invoke the system linker (cc/ld) with correct flags and library search paths
- Pass all object files, rlibs, and native libraries to the linker
- Handle `CrateType::Executable` entry point (`main` → lang_start → user main)
- Support `--crate-type lib` and `--crate-type bin` simultaneously

## Affected Modules

- `rustc_codegen_tuffy/src/lib.rs` — implement link(), handle CrateType dispatch
- `rustc_codegen_tuffy/Cargo.toml` — may need additional rustc_codegen_ssa dependencies
