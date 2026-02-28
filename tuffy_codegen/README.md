# tuffy_codegen

Target-dispatching code generation facade.

## Purpose

Provides `CodegenSession`, the single entry point for all code generation. It selects the appropriate backend based on the target triple and delegates all calls through enum dispatch, so callers never need to know which backend is active.

## Design

### `CodegenSession`

Created from a target triple string (currently only `x86_64-*` is supported). Wraps the backend in an internal `CodegenInner` enum for static dispatch without trait objects.

API surface:
- `compile_function` — compile a single IR function to machine code.
- `emit_object` — emit compiled functions and static data as an object file.
- `generate_allocator_stubs` — generate allocator forwarding stubs.
- `generate_entry_point` — generate C `main` and `lang_start`.

### `AbiMetadataBox`

Target-agnostic wrapper for backend-specific ABI metadata. Allows the MIR translation layer to record ABI information (secondary return registers, wide returns) without knowing the target.

## Dependencies

- `tuffy_ir` — IR definitions
- `tuffy_target` — backend trait and shared types
- `tuffy_target_x86` — x86-64 backend implementation
