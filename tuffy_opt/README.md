# tuffy_opt

Optimization pipeline and pass infrastructure for tuffy IR.

This crate hosts IR-level optimization passes operating on `tuffy_ir::Module` / `tuffy_ir::Function`.

## Status

- Lean-owned peephole framework is implemented.
- Default peephole rules are exported from `lean/TuffyLean/Rewrites/Basic.lean`.
- `build.rs` runs the Lean exporter, then invokes `tuffy_opt_gen` as a build-dependency library to generate Rust matcher code into `OUT_DIR`.
- The optimizer runtime executes generated rule-specific match/apply functions rather than interpreting generic JSON at runtime.

## Dependencies

- `tuffy_ir` — IR definitions to transform
