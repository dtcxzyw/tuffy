# Formal verification of legalization rewrites in Lean

- Status: Long-term
- Created: 2026-02-28
- Completed: N/A
- Parent: move-legalize-to-codegen

## Description

Each legalization rewrite rule transforms an illegal IR operation into a sequence of legal operations. These rewrites must preserve program semantics — the legalized sequence must compute the same result as the original operation for all inputs.

The goal is to formally prove correctness of all legalization rewrite rules in Lean 4, ensuring that the Rust implementation in `tuffy_codegen` is backed by machine-checked proofs.

### Scope

Rewrites that must be verified:

- **Wide integer splitting** — e.g., 128-bit add → (lo add + carry, hi adc) preserves the mathematical result
- **Op expansion** — e.g., rotate → shift+or, bswap → shift sequence, popcount → Kernighan's algorithm
- **Carry/borrow propagation** — correctness of multi-word arithmetic chains (add-with-carry, subtract-with-borrow)
- **Comparison lowering** — wide icmp → cascaded comparisons on halves
- **Shift/rotate splitting** — wide shl/shr with cross-word bit transfer

Rewrites explicitly excluded from formal verification:

- **Library call lowering** — libcall correctness depends on the runtime library implementation (e.g., compiler-rt, libgcc), which is outside Tuffy's control. The proof obligation is only that the call interface (arguments, return value) matches the expected semantics.

### Proof structure

For each rewrite rule `R` that transforms `op(args...)` into `seq(legal_ops...)`:

```
theorem R_correct :
  ∀ args, eval(seq(legal_ops...)) = eval(op(args...))
```

Proofs should be structured in `lean/TuffyLean/Rewrites/Legalize/` mirroring the rewrite rule organization in the Rust implementation.

## Affected Modules

- `lean/TuffyLean/Rewrites/Legalize/` — new proof modules
- `lean/TuffyLean/IR/` — may need additional IR semantics definitions for proof support
