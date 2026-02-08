# Rustc Frontend Adapter (rustc_codegen_tuffy)

- Status: Draft
- Created: 2026-02-07
- Completed: N/A
- Parent: docs/tasks/202602/init.md

## Description

Implement the rustc frontend adapter that bridges rustc MIR to tuffy IR. Implements `rustc_codegen_ssa` traits to reuse existing MIR lowering code.

Key deliverables:
- `CodegenBackend` trait implementation (entry point)
- `ExtraBackendMethods` implementation (codegen_crate)
- `CodegenCx` (CodegenMethods): compilation unit context with tuffy IR types
- `Builder` (BuilderMethods): MIR-to-tuffy-IR instruction generation
- Associated types: Value, BasicBlock, Type, Function mapped to tuffy IR
- MIR translation: control flow structuralization, mem2reg, aggregate scalarization, type translation (fixed-width → int + assert nodes)
- `-Z codegen-backend` loading support
- Drop/unwind handling as CFG edges

## Subtasks

- N/A (leaf task)

## Affected Modules

- `rustc_codegen_tuffy/src/` — CodegenBackend, Builder, CodegenCx
