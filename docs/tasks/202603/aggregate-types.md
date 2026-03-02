# Add Aggregate Type Support (Struct, Array) to Tuffy IR

- Status: Pending
- Created: 2026-03-02
- Completed: N/A
- Parent: N/A

## Description

Add `Struct` and `Array` type variants to `tuffy_ir::Type`, along with `ExtractValue` and `InsertValue` instructions for aggregate manipulation. This enables the frontend to emit struct/array parameters and operations without ABI-specific decomposition, keeping the boundary rule clean.

### Rationale

Currently struct parameters are decomposed in the frontend (`call.rs`), which violates the boundary rule that ABI details should be handled in the backend. Aggregate type support allows:

1. Frontend to emit struct/array params as single IR values
2. Frontend to use `extractvalue`/`insertvalue` for field/element access instead of load/store
3. Backend legalize to expand aggregates into register-sized pieces based on ABI
4. Cleaner separation of concerns between frontend and backend

### Design

**Type System:**
- Add `Type::Struct(Vec<Type>)` — struct with field types
- Add `Type::Array(Box<Type>, u32)` — array with element type and count
- Update `Type` display, verifier, and all pattern-matching code
- Ensure aggregate values can flow through IR (params, instructions, block args)

**Instructions:**
- Add `Op::ExtractValue(agg: Operand, indices: Vec<u32>)` — extract nested field/element
- Add `Op::InsertValue(agg: Operand, val: Operand, indices: Vec<u32>)` — insert value at indices
- Add builder methods: `extract_value()` and `insert_value()`
- Update verifier to validate index paths and result types

**Integration:**
- Update display formatting for aggregates
- Update isel/legalize to handle aggregate operations
- Add tests for basic aggregate construction/deconstruction

## Subtasks

1. Add `Struct` and `Array` variants to `tuffy_ir::types.rs`
2. Update `Type` display and verifier for new variants
3. Add `ExtractValue` and `InsertValue` to `tuffy_ir::instruction.rs`
4. Add builder methods in `tuffy_ir::builder.rs`
5. Update isel in `tuffy_target_x86::isel.rs` (or mark as unimplemented)
6. Update legalize in `tuffy_codegen::legalize.rs` (or mark as unimplemented)
7. Add tests in `tuffy_ir::tests.rs`
8. Update frontend (`rustc_codegen_tuffy`) to emit struct params as single values (follow-up)

## Affected Modules

- `tuffy_ir/src/types.rs` — add Struct/Array variants
- `tuffy_ir/src/instruction.rs` — add ExtractValue/InsertValue ops
- `tuffy_ir/src/builder.rs` — add extract_value/insert_value methods
- `tuffy_ir/src/display.rs` — format aggregates
- `tuffy_ir/src/verifier.rs` — validate aggregate operations
- `tuffy_ir/src/tests.rs` — test aggregate operations
- `tuffy_target_x86/src/isel.rs` — handle aggregates (or unimplemented)
- `tuffy_codegen/src/legalize.rs` — expand aggregates by ABI (or unimplemented)
