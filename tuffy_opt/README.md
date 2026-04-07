# tuffy_opt

Optimization pipeline and pass infrastructure for tuffy IR.

This crate hosts IR-level optimization passes operating on `tuffy_ir::Module` / `tuffy_ir::Function`.

## Status

- Lean-owned peephole framework is implemented.
- Default peephole rules are exported from `lean/TuffyLean/Rewrites/Basic.lean`.
- `build.rs` runs the Lean exporter at compile time and embeds the generated JSON from `OUT_DIR`.
- The current executor supports local value rewrites and `brif` condition rewrites, iterating to a fixed point.

## Dependencies

- `tuffy_ir` — IR definitions to transform
