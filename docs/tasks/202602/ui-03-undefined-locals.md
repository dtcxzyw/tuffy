# Handle Undefined MIR Locals Gracefully

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-08
- Parent: docs/tasks/202602/ui-tests.md

## Description

The MIR translator panics at `mir_to_ir.rs:59` ("local not yet defined") when a MIR local is referenced before being assigned. This happens when:

- A local is assigned in a branch not yet translated (control flow)
- A local is assigned via an unsupported rvalue (translate_rvalue returns None)
- The return local `_0` is read but was never written (e.g., functions returning unit)

This is ~4% of UI test failures.

Key deliverables:
- Return `None` from `translate_function` instead of panicking when encountering unsupported locals
- Handle unit-returning functions (return local `_0` may never be assigned)
- Log or skip unsupported constructs instead of panicking

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — `LocalMap::get`, `translate_body`
