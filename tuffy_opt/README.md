# tuffy_opt

Optimization pipeline and pass infrastructure for tuffy IR.

This crate hosts IR-level optimization passes operating on `tuffy_ir::Module` / `tuffy_ir::Function`.

## Status

- Conservative stack-slot `sroa/mem2reg` runs before peephole cleanup.
- Module optimization now includes a direct same-module inliner for eligible
  `symbol_addr` call sites, followed by a second cleanup round on changed
  callers.
- Promotion is block-arg based (matching Tuffy IR CFG joins) rather than PHI-node based.
- Promotion currently handles local `stack_slot` objects reached through constant-offset `ptradd`.
- Promotion is intentionally conservative around escaping pointers, atomics, bulk memory ops, and unwind-cleanup calls.
- Lean-owned peephole framework is implemented.
- Default peephole rules are exported from `lean/TuffyLean/Rewrites/Basic.lean`.
- Constant folding is modeled as peephole rules and exported through the same Lean JSON pipeline.
- Context-sensitive at-use integer analysis is exported from `lean/TuffyLean/Rewrites/AtUse.lean`.
- The legacy handwritten `range` cleanup family has been replaced by a Lean-owned/generated `at_use` family.
- Cleanup pass ordering for non-inline `tuffy_opt` families is exported from Lean and code-generated into the Rust dispatcher.
- The `brif` canonicalization path is no longer a Rust-only manual rule; it is matched through the generated peephole pipeline.
- `build.rs` runs the Lean exporter, then invokes `tuffy_opt_gen` as a build-dependency library to generate Rust matcher code into `OUT_DIR`.
- The optimizer runtime executes generated rule-specific match/apply functions rather than interpreting generic JSON at runtime.
- The optimizer runtime also executes a generated at-use pass description for context-sensitive branch folding and annotation strengthening.
- Value-root constant folds reuse `tuffy_ir_interp` semantics for evaluation so poison-sensitive cases stay aligned with the interpreter.
- Peephole side conditions can query optimizer-local integer facts such as synthesized best-width annotations and known low bits.
- Value-root replacements are not limited to existing bindings; the current generated runtime can also materialize simple boolean expressions such as logical negation.
- Rewrites are modeled around generic value roots and terminator roots; the current terminator subset only includes `brif`, but it is no longer represented as a dedicated rewrite kind.
- The current cleanup manifest still distinguishes verified/generated families from legacy handwritten families; inlining remains outside that manifest.

`optimize_module` currently runs:

1. function-local cleanup for every function:
   promotion, peepholes, at-use simplification, CFG cleanup
2. module-level bulk memory and scalar-swap idiom formation
3. direct same-module inlining across the module
4. function-local cleanup again for callers changed by inlining

## Dependencies

- `tuffy_ir` — IR definitions to transform
