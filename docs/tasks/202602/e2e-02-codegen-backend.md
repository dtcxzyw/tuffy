# CodegenBackend Entry Point

- Status: In Progress
- Created: 2026-02-08
- Completed: N/A
- Parent: docs/tasks/202602/e2e-pipeline.md

## Description

Implement the `CodegenBackend` trait so that rustc can load tuffy as a backend via `-Z codegen-backend`. This is the entry point that connects rustc to tuffy.

Key deliverables:
- Implement `CodegenBackend` trait (entry point)
- Implement `ExtraBackendMethods` (`codegen_crate` orchestration)
- Define associated types: `Value`, `BasicBlock`, `Type`, `Function` mapped to tuffy IR handles
- `CodegenCx` struct holding tuffy IR module context
- `Builder` struct implementing `BuilderMethods` (stub — actual translation in next task)
- Backend loadable via `rustc --edition 2021 -Z codegen-backend=path/to/libtuffy.so`

## Affected Modules

- `rustc_codegen_tuffy/src/`
