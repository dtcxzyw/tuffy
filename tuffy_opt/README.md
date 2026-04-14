# tuffy_opt

Optimization pipeline and pass infrastructure for tuffy IR.

This crate hosts IR-level optimization passes operating on `tuffy_ir::Module` / `tuffy_ir::Function`.

## Status

- Conservative stack-slot `sroa/mem2reg` runs before peephole cleanup.
- Module optimization now includes a direct same-module inliner for eligible
  `symbol_addr` call sites, followed by a second cleanup round on changed
  callers.
- Same-module inlining also handles call sites that ignore a callee's primary
  return value, which matters for out-parameter-heavy helper wrappers.
- Promotion is block-arg based (matching Tuffy IR CFG joins) rather than PHI-node based.
- Promotion currently handles local `stack_slot` objects reached through constant-offset `ptradd`.
- Promotion can also fold same-size integer slots when some stores write
  narrower integer constants, by widening those constants to the slot slice
  shape during SSA reconstruction.
- Promotion is intentionally conservative around escaping pointers, atomics, bulk memory ops, and unwind-cleanup calls.
- Lean-owned peephole framework is implemented.
- Default peephole rules are exported from `lean/TuffyLean/Rewrites/Basic.lean`.
- Constant folding is modeled as peephole rules and exported through the same Lean JSON pipeline.
- Context-sensitive at-use integer analysis metadata is exported alongside the peephole rule set from `lean/TuffyLean/Rewrites/AtUse.lean`.
- The generated at-use pass now runs in pointer-heavy functions too, but it still tracks only integer SSA values and integer operands; pointer values remain outside the fact domain.
- Lean-owned at-use forward rules now cover `add`, `sub`, `shr`, and `zext` in addition to the earlier const/select/bitwise cases.
- The legacy handwritten `range` cleanup family has been folded into the Lean-owned/generated `peephole` family.
- Cleanup pass ordering for non-inline `tuffy_opt` families is exported from Lean and code-generated into the Rust dispatcher.
- The `brif` canonicalization path is no longer a Rust-only manual rule; it is matched through the generated peephole pipeline.
- Lean-owned strength-reduction rules now cover `div x, 1 -> x`, `rem x, 1 -> 0`, and non-negative division by power-of-two constants to `shr`.
- Lean-owned strength-reduction rules also cover multiplication by power-of-two constants to `shl`.
- `build.rs` runs the Lean exporter, then invokes `tuffy_opt_gen` as a build-dependency library to generate Rust matcher code into `OUT_DIR`.
- The optimizer runtime executes generated rule-specific match/apply functions rather than interpreting generic JSON at runtime.
- The optimizer runtime executes one generated peephole family that covers both local root rewrites and context-sensitive branch folding / annotation strengthening.
- Value-root constant folds reuse `tuffy_ir_interp` semantics for evaluation so poison-sensitive cases stay aligned with the interpreter.
- Peephole side conditions can query optimizer-local integer facts such as synthesized best-width annotations, known low bits, and proven non-negativity.
- Value-root replacements are not limited to existing bindings; the current generated runtime can also materialize integer constants, derived shift amounts for power-of-two divisors, and simple boolean expressions such as logical negation.
- Rewrites are modeled around generic value roots and terminator roots; the current terminator subset only includes `brif`, but it is no longer represented as a dedicated rewrite kind.
- The current cleanup manifest still distinguishes verified/generated families from legacy handwritten families; inlining remains outside that manifest.
- Scalar-swap formation now follows uniquely forwarded memory tokens through
  single-predecessor branch edges and drops dead symbol-backed temp preloads
  that become unused after the rewrite.
- Local cleanup now also loopifies eligible direct self-tail recursion in
  root-only unit-returning functions by rebuilding them with a loop header and
  a backedge branch instead of the recursive tail call.

`optimize_module` currently runs:

1. function-local cleanup for every function:
   promotion, peepholes, CFG cleanup, tail recursion loopification
2. module-level bulk memory and scalar-swap idiom formation
3. direct same-module inlining across the module
4. function-local cleanup again for callers changed by inlining

## Dependencies

- `tuffy_ir` — IR definitions to transform
