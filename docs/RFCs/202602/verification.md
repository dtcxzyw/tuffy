# Feature Name: `tuffy_verification`

- Status: Draft
- Created: 2026-02-07
- Completed: N/A

## Summary

This RFC defines the correctness guarantee framework for the tuffy compiler. All optimization transforms are declarative rewrite rules with machine-checked correctness proofs in Lean 4. Instruction selection (isel) — the lowering from tuffy IR to machine instructions — is also formally verified in Lean 4, proving that the generated machine code faithfully implements the IR semantics. An Alive2-style automatic verifier and traditional testing (interpreter + fuzzer) serve as auxiliary discovery tools, not as correctness foundations.

## Motivation

Compiler optimization bugs are a persistent source of real-world software defects. LLVM's InstCombine alone has accumulated hundreds of miscompilation bugs, many stemming from subtle semantic errors in hand-written transforms. The root causes are:

- **Imperative transforms**: hand-written code that directly manipulates IR is error-prone. Each transform must correctly handle edge cases (poison, overflow, pointer provenance) that are easy to overlook.
- **Informal correctness arguments**: most transforms are justified by informal reasoning or review, not machine-checked proofs. Subtle errors survive review.
- **Disconnected verification**: tools like Alive2 verify transforms after the fact, but are not integrated into the development workflow as a hard gate.

Instruction selection has similar risks. The lowering from IR to machine instructions must preserve semantics — incorrect register sizing, wrong sign/zero extension, or mishandled non-standard bit-widths (e.g., u17 annotations) can silently produce wrong code. Traditional compilers rely on testing to catch these bugs; tuffy formally verifies isel correctness.

Tuffy takes a formal-first approach: every rewrite rule and every isel lowering rule must have a Lean 4 proof before it enters the production pipeline.

## Guide-level explanation

### Three-layer verification

Tuffy uses three layers of verification, with clear trust hierarchy:

| Layer | Role | Trust level |
|-------|------|-------------|
| Lean 4 proofs | Gold standard. Machine-checked correctness of every rewrite rule and isel lowering rule | **Authoritative** |
| Alive2-style verifier | SMT-based quick check for discovering missed optimizations and regressions | Auxiliary |
| Interpreter + fuzzer + test suite | End-to-end behavioral testing | Auxiliary |

Only Lean 4 proofs gate production inclusion. The other two layers are discovery tools — they find bugs and missed optimizations, but do not constitute correctness evidence.

### Verified optimization transforms

Transforms are not hand-written imperative IR manipulation. They are **declarative rewrite rules**:

```
rule strength_reduce_mul_pow2 {
    pattern:  mul %x, const(C) where is_power_of_2(C)
    replace:  shl %x, log2(C)
    kind:     equivalence
}

rule narrow_add_known_bits {
    pattern:  add %x, %y where known_zeros(%x, [32:63]) && known_zeros(%y, [32:63])
    replace:  add %x, %y  // same operation, but refine known_zeros on result
    refine:   known_zeros(result, [32:63])
    kind:     refinement
}
```

Each rule specifies:
- **pattern**: what IR fragment to match
- **replace**: what to produce
- **kind**: equivalence or refinement (used by dirty bit mechanism)
- **preconditions**: constraints that must hold for the rule to apply

### Workflow

The development workflow for a new optimization:

1. **Define the rewrite rule and prove correctness in Lean 4** — the rule definition and its proof live together in the same Lean file, against the formal IR semantics. This ensures the proof and the rule are always consistent.
2. **Lean exports declarative transform description** — Lean generates a machine-readable description (JSON) of the verified rule, including pattern, replacement, preconditions, and transform kind.
3. **Codegen generator produces Rust code** from the exported description via codegen.
4. **Generated code** uses the builder API (origin, dirty bit handled automatically by Rust type system)
5. **Alive2-style verifier** cross-checks the rule for additional confidence
6. **Fuzzer** exercises the rule on diverse inputs

Steps 1–3 are mandatory. Steps 5–6 are recommended but not gating.

The key insight: by having Lean own both the rule definition and the proof, there is no possibility of the proof and the implementation diverging. The codegen generator only reads what Lean exports.

### Verified instruction selection

Instruction selection lowers tuffy IR (infinite precision integers with annotations) to
target machine instructions (fixed-width registers). This lowering must preserve semantics:
the machine code must produce the same observable behavior as the IR.

Key properties to verify:

- **Annotation-driven sizing**: an `:s32` annotation lowers to 32-bit machine operations;
  non-standard widths (e.g., `:u17`) lower to the correct shift/mask sequences.
- **Signedness correctness**: signed annotations select signed machine operations (SAR, IDIV,
  signed condition codes) and unsigned annotations select unsigned ones (SHR, DIV, unsigned
  condition codes).
- **Extension correctness**: sext/zext from annotation width N produces the correct result,
  including the no-op cases (zext from unsigned, sext from signed) and the cases requiring
  explicit shift/mask sequences.

Each isel lowering rule is defined in Lean 4 as a relation between IR instruction semantics
and machine instruction semantics. The proof obligation is:

> For all inputs satisfying the annotation constraints, the machine instruction sequence
> produces the same result as the IR instruction under the formal semantics.

The Lean formalization requires a machine-level semantics model (x86-64 integer operations
on fixed-width registers) in addition to the existing IR semantics.

### Trust boundary

```
┌─────────────────────────────────────────┐
│              Trusted components          │
│                                         │
│  ┌───────────────┐  ┌────────────────┐  │
│  │ Lean 4 kernel │  │ IR formal      │  │
│  │               │  │ semantics      │  │
│  └───────────────┘  └────────────────┘  │
│  ┌────────────────┐  ┌───────────────┐  │
│  │ x86-64 machine │  │ Codegen       │  │
│  │ semantics      │  │ generator     │  │
│  └────────────────┘  └───────────────┘  │
├─────────────────────────────────────────┤
│              Verified components         │
│                                         │
│  ┌────────────────────────────────────┐  │
│  │ Each rewrite rule                  │  │
│  │ (proven correct in Lean 4)         │  │
│  └────────────────────────────────────┘  │
│  ┌────────────────────────────────────┐  │
│  │ Each isel lowering rule            │  │
│  │ (proven correct in Lean 4)         │  │
│  └────────────────────────────────────┘  │
├─────────────────────────────────────────┤
│              Constrained components      │
│                                         │
│  ┌────────────────────────────────────┐  │
│  │ Generated Rust transform code      │  │
│  │ (type system enforces invariants)  │  │
│  └────────────────────────────────────┘  │
└─────────────────────────────────────────┘
```

### IR formal semantics in Lean 4

The foundation of all proofs is a formal semantics of tuffy IR defined in Lean 4. This includes:

- Type system semantics (infinite precision integers, byte types, pointers, vectors)
- Instruction semantics (each operation's mathematical definition)
- Poison propagation rules
- Memory model (four-state bytes, provenance)
- Assert node semantics (assertsext, assertzext)

This formalization is the single source of truth for what the IR means. All rewrite rule proofs reference this definition.

### Alive2-style verifier

A separate SMT-based tool that can:

- Automatically verify simple rewrite rules (bounded bit widths, no loops)
- Discover missed optimizations by enumerating candidate rewrites
- Regression-test existing rules against IR semantics changes
- Run in CI as a fast feedback loop

This tool is valuable for development velocity but is not a substitute for Lean 4 proofs. It may miss edge cases that the theorem prover catches, and it cannot handle unbounded reasoning (infinite precision integers require induction).

### Interpreter and fuzzer

The tuffy IR interpreter (miri-like) combined with fuzzing provides end-to-end validation:

- Compile Rust programs with tuffy, run the output, compare against reference (rustc + LLVM)
- Fuzz IR fragments through the optimization pipeline, check that interpreter results are preserved
- Exercise edge cases in poison propagation, pointer provenance, and memory model

## Reference-level explanation

### Rewrite rule representation

```
struct RewriteRule {
    name: String,
    pattern: Pattern,
    replacement: Replacement,
    preconditions: Vec<Precondition>,
    kind: TransformKind,
    proof_ref: LeanProofRef,
}

struct LeanProofRef {
    module: String,      // Lean 4 module path
    theorem: String,     // theorem name
    verified: bool,      // checked by build system
}
```

### Codegen pipeline

```
Lean 4 rewrite rule definition + proof
        │
        ▼
  Codegen generator (trusted)
        │
        ▼
  Generated Rust code:
    - Pattern matching function
    - Replacement construction (via Builder API)
    - TransformKind declaration
    - Precondition checks
```

The generator produces Rust code that:
1. Implements the `Pass` trait
2. Uses the builder API (origin is mandatory, dirty bit is automatic)
3. Declares `TransformKind` matching the Lean 4 proof (equivalence or refinement)

### Build system integration

The build system verifies that:
1. Every rewrite rule in the production pipeline has a corresponding Lean 4 proof
2. The proof references a theorem that is successfully checked by Lean 4
3. The generated Rust code is up-to-date with the rule definition

Rules without proofs can exist in a `experimental` pipeline for development, but cannot be included in release builds.

## Drawbacks

- **Lean 4 learning curve**: contributors must learn Lean 4 to add new optimizations. This raises the barrier to contribution.
- **Proof effort**: proving correctness of complex transforms (loop optimizations, vectorization) requires significant effort. Some transforms may be difficult to formalize.
- **Formalization maintenance**: changes to IR semantics require updating the Lean 4 formalization and potentially re-proving existing theorems.
- **Codegen generator trust**: the generator is in the trusted computing base. Bugs in the generator could produce incorrect Rust code from correct proofs.
- **Development velocity**: requiring proofs for every optimization may slow down the pace of adding new optimizations compared to traditional compilers.

## Rationale and alternatives

### Why Lean 4?

- Active ecosystem with Mathlib providing extensive mathematical foundations
- Good metaprogramming support (tactics, macros) for proof automation
- Overlap with Rust community (shared interest in formal methods)
- Compiled language with reasonable performance for proof checking

**Alternative: Coq.** Mature ecosystem but less active development. Lean 4's metaprogramming is more ergonomic.

**Alternative: Isabelle.** Strong automation (Sledgehammer) but less mainstream adoption and weaker programming language integration.

### Why declarative transforms?

**Alternative: imperative transforms with post-hoc verification.** Write transforms in Rust, then verify them with Alive2 or similar. Rejected because imperative code has a large surface area for bugs that post-hoc tools may miss, and it's harder to establish a formal correspondence between the Rust code and the verified property.

Declarative rules have a narrow semantic gap between the rule definition and the Lean 4 proof. The codegen generator bridges this gap with minimal trusted code.

### Why not rely solely on Alive2-style verification?

SMT-based verification is bounded — it checks finite bit widths and cannot perform induction. Tuffy's infinite precision integers require inductive proofs that only an interactive theorem prover can provide. Additionally, SMT solvers may time out on complex transforms, giving no answer rather than a proof.

## Prior art

- **CompCert**: fully verified C compiler in Coq. Proves correctness of the entire compilation pipeline, not just individual transforms. Tuffy takes a similar approach for isel (verified lowering) while using declarative rules for optimizations.
- **Alive / Alive2**: SMT-based verification of LLVM InstCombine transforms. Discovered numerous bugs. Tuffy uses this as an auxiliary tool, not the primary correctness mechanism.
- **CakeML**: verified ML compiler in HOL4. Similar full-pipeline verification to CompCert.
- **Lean 4 + Mathlib**: growing library of formalized mathematics. Provides foundations for reasoning about integers, bit operations, and algebraic properties.
- **Souper**: superoptimizer for LLVM that discovers optimizations via SMT. Could complement tuffy's approach by suggesting candidate rewrite rules for human proof.

## Unresolved questions

- **Declarative rule expressiveness**: can all useful transforms be expressed declaratively, or will some require escape hatches for imperative logic (e.g., complex loop transforms)?
- **Proof automation**: how much of the proof burden can be automated via Lean 4 tactics? Custom tactics for common proof patterns (bit manipulation, poison propagation) would significantly reduce effort.
- **Codegen generator verification**: should the generator itself be verified (in Lean 4), or is manual audit sufficient given its narrow scope?
- **Incremental proof checking**: how to efficiently re-check proofs when IR semantics change? Full re-verification may be expensive.

## Future possibilities

- **Proof-carrying optimizations**: distribute verified rewrite rules as packages, enabling a community-driven optimization library with machine-checked correctness.
- **Superoptimizer integration**: use SMT-based search (Souper-style) to discover candidate rewrites, then prove them in Lean 4 for inclusion in the production pipeline.
- **End-to-end verification**: with optimizations and isel now verified, extend verification to the remaining pipeline stages (MIR translation, register allocation, machine code emission) to close the full compilation gap.
- **LLM-assisted proofs**: use language models to draft Lean 4 proofs for new rewrite rules, with human review and machine checking.
