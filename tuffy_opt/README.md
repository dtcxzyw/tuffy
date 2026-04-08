# tuffy_opt

Optimization pipeline and pass infrastructure for tuffy IR.

This crate hosts IR-level optimization passes operating on `tuffy_ir::Module` / `tuffy_ir::Function`.

## Status

- Lean-owned peephole framework is implemented.
- Default peephole rules are exported from `lean/TuffyLean/Rewrites/Basic.lean`.
- Constant folding is modeled as peephole rules and exported through the same Lean JSON pipeline.
- `build.rs` runs the Lean exporter, then invokes `tuffy_opt_gen` as a build-dependency library to generate Rust matcher code into `OUT_DIR`.
- The optimizer runtime executes generated rule-specific match/apply functions rather than interpreting generic JSON at runtime.
- Value-root constant folds reuse `tuffy_ir_interp` semantics for evaluation so poison-sensitive cases stay aligned with the interpreter.
- Peephole side conditions can query optimizer-local integer facts such as synthesized best-width annotations and known low bits.
- Value-root replacements are not limited to existing bindings; the current generated runtime can also materialize simple boolean expressions such as logical negation.
- Rewrites are modeled around generic value roots and terminator roots; the current terminator subset only includes `brif`, but it is no longer represented as a dedicated rewrite kind.

## Dependencies

- `tuffy_ir` — IR definitions to transform
