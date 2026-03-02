# Refactor Struct Parameter Handling in mir_to_ir

- Status: Completed
- Created: 2026-03-02
- Completed: 2026-03-02
- Parent: N/A

## Description

Refactor all special-case struct parameter handling in `mir_to_ir` to use the new `Struct` type and `extractvalue`/`insertvalue` instructions. Currently, struct parameters are decomposed manually with size-based branching (e.g., `size > 8` checks). This violates the boundary rule by embedding ABI logic in the frontend.

After refactoring, the frontend will emit struct parameters as single IR values with `Struct` type, and the backend legalize pass will handle ABI-specific expansion.

### Rationale

The new aggregate type support (Struct, Array, extractvalue, insertvalue) enables cleaner separation of concerns:

1. **Frontend (mir_to_ir)**: Emit high-level struct operations as single SSA values
2. **Backend (legalize)**: Expand structs into register-sized pieces based on target ABI

Current code has scattered special cases that should be consolidated:
- `call.rs:774-815` — struct parameter decomposition
- `terminator.rs:44-115` — stack-allocated return handling
- `rvalue.rs` — Aggregate construction/destructuring
- Various places with `size > 8` branching

### Design

**Changes to call.rs:**
- Replace struct parameter decomposition with single Struct-typed value
- Use `extractvalue` for field access instead of manual load/store
- Remove `size > 8` special cases

**Changes to terminator.rs:**
- Replace stack-allocated return handling with Struct type
- Use `extractvalue` to access return fields
- Remove size-based branching

**Changes to rvalue.rs:**
- Update Aggregate construction to emit Struct type
- Use `insertvalue` for field assignment

**Changes to types.rs:**
- Add helper to compute struct layout with explicit padding
- Ensure padding is represented as `[byte(8); N]` or `byte(N)` fields

**Changes to ctx.rs:**
- Add utilities for struct field access (extractvalue/insertvalue generation)

### Subtasks

1. Add struct layout computation helper in `types.rs`
2. Add struct field access utilities in `ctx.rs`
3. Refactor `call.rs` to emit Struct-typed parameters
4. Refactor `terminator.rs` to handle Struct-typed returns
5. Refactor `rvalue.rs` Aggregate handling
6. Remove all size-based struct special cases
7. Test with struct-passing functions
8. Verify no regressions in existing tests

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir/call.rs` — struct parameter passing
- `rustc_codegen_tuffy/src/mir_to_ir/terminator.rs` — struct returns
- `rustc_codegen_tuffy/src/mir_to_ir/rvalue.rs` — Aggregate construction
- `rustc_codegen_tuffy/src/mir_to_ir/types.rs` — struct layout helpers
- `rustc_codegen_tuffy/src/mir_to_ir/ctx.rs` — struct utilities
