# tuffy_opt_gen

Code generator for `tuffy_opt` peephole rules.

This crate reads the Lean-exported peephole JSON schema and emits Rust matcher/rewrite code for the optimizer, similar to how `tuffy_isel_gen` emits generated instruction-selection code.

The same peephole JSON artifact now also carries the context-sensitive at-use metadata consumed by the unified peephole runtime in `tuffy_opt`.

The generated matcher supports:
- structural value / terminator roots
- fact-based side conditions over integer bindings
- simple value-root replacement expressions in addition to direct binding reuse
- integer constants plus small integer expression trees (for example Lean-owned shift rewrites)

## Usage

```bash
tuffy_opt_gen <input.json> <output.rs>
```

In normal builds, `tuffy_opt/build.rs` uses the library interface directly after running the Lean exporter.
