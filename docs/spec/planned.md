# Planned Features

The following features are described in the [IR Design RFC](../RFCs/202602/ir-design.md) but
are not yet implemented in the Rust codebase.

## Floating Point Semantics

The IR adopts IEEE 754-2008 as the floating-point semantics standard. Basic
operations (`fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `copysign`) are
implemented. Per-instruction rewrite flags (`reassoc`, `contract`) and float
value class constraints (`nofpclass`) are defined. Full NaN payload and denormal
semantics are still under discussion — the current Lean model uses Lean 4's
native `Float` type (IEEE 754 binary64) as a placeholder.

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
