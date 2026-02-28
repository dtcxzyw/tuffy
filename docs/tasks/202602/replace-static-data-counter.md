# Replace STATIC_DATA_COUNTER with context-local counter

- Status: Completed
- Created: 2026-02-27
- Completed: 2026-02-28
- Parent: N/A

## Description

`rustc_codegen_tuffy/src/mir_to_ir.rs` uses a global `static STATIC_DATA_COUNTER: AtomicU64` to generate unique symbol names (`.Lconst.*`, `.Lstr.*`, `.Lvtable.*`, `.Lloc.*`, etc.). This is unreliable:

- Non-deterministic across parallel codegen units — symbol names depend on execution order.
- State leaks across compilation sessions if the compiler is used as a library.
- Violates the principle that mutable state should be scoped to a context, not global.

LLVM's approach: unique ID counters live on `Module` or `LLVMContext`, not as global statics. Each module independently numbers its private symbols.

## Current usage (11 sites)

All sites follow the same pattern — `format!(".L<prefix>.{}", STATIC_DATA_COUNTER.fetch_add(1, Ordering::Relaxed))`:

| Prefix | Purpose |
|--------|---------|
| `.Lloc_file` | Caller location file name data |
| `.Lloc` | Caller location struct |
| `.Lvtable` | Vtable data blobs |
| `.Lconst` | Constant data blobs |
| `.Lstr` | String literal data |

## Proposed fix

Move the counter onto `TranslationCtx` or a shared per-codegen-unit context (e.g. `CodegenSession`). Each function translation gets a mutable reference to the counter, ensuring:

- Deterministic output within a codegen unit.
- No cross-session state leakage.
- No need for atomic operations (single-threaded access within a CGU).

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir.rs` — remove `STATIC_DATA_COUNTER`, add counter field to context
- `tuffy_codegen/` — potentially add counter to `CodegenSession` if shared across functions
