# Planned Features

The following features are described in the [IR Design RFC](../RFCs/202602/ir-design.md) but
are not yet implemented in the Rust codebase.

## Floating Point Semantics

The IR adopts IEEE 754-2008 as the floating-point semantics standard. Basic
operations (`fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `copysign`) are
implemented. Per-instruction rewrite flags (`reassoc`, `contract`) and float
value class constraints (`nofpclass`) are defined.

### IEEE 754 Lean library

The current Lean model uses Lean 4's native `Float` type (IEEE 754 binary64) as a
placeholder. `Float` is opaque — it maps directly to hardware double and cannot be
unfolded in proofs. Properties that follow from the IEEE 754 standard (e.g.,
"fadd produces -0.0 only when both operands are -0.0") must be axiomatized
(see `IR/FloatAxioms.lean`). This is unsatisfactory for a formal-first project.

We need a Lean 4 library that provides a transparent, proof-friendly model of IEEE 754
floating-point arithmetic covering all widths (f16, bf16, f32, f64), rounding modes,
NaN payloads, subnormals, and signed zeros. Existing efforts:

- [HOLFloat-Lean](https://github.com/opencompl/HOLFloat-Lean) — formalizes FP
  semantics in Lean 4, building on prior HOL formalizations.
- **Flean** — individual effort for IEEE 754 in Lean; requires rewrite.
- **Flocq port** — the Coq [Flocq](https://flocq.gitlabpages.inria.fr/) library is
  the most mature FP formalization; porting it to Lean 4 is a community proposal.

Until a suitable library is available, tuffy will continue axiomatizing IEEE 754
properties as needed. The axiom set should be kept minimal and well-documented so
that it can be discharged once a real library is adopted.

## Scalable Vector Types

Vector types parameterized by total bit-width, not element count. Element count is
derived: `count = total_bits / element_bits`. Scalable vectors use
`vscale × base_width`, where `vscale` is a runtime constant determined by hardware
(cf. SVE, RVV). Well-formedness: `total_bits % element_bits == 0` and lane count
must be a power of two. See the [scalable vector RFC](../RFCs/202602/) (planned).

## Byte Type Operations

`bytecast` semantics are specified in [Type Conversion](instructions.md#type-conversion). The Lean
formal definition and Rust implementation are not yet complete.

## Memory SSA

Memory dependencies encoded directly into the IR as memory version tokens on load/store
operations, enabling progressive refinement as alias analysis improves.

## Atomic Operations

Atomic operations (`load.atomic`, `store.atomic`, `rmw`, `cmpxchg`, `fence`) are
implemented with `MemoryOrdering` and `AtomicRmwOp` enumerations. See
[Atomic Operations](instructions.md#atomic-operations). The formal concurrency model is TBD — current
Lean semantics define sequential behavior only.

## Control Flow Structuralization

Translation from rustc MIR to tuffy IR with automatic structuralization of loops and
branches into SESE regions. Irreducible control flow remains as flat CFG within a region.
