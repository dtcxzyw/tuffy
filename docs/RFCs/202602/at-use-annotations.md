# Feature Name: `at-use-annotations`

- Status: Draft
- Created: 2026-02-08
- Completed: N/A

## Summary

Replace standalone `assert_sext`/`assert_zext` instructions with annotations on value
definitions (result-side) and use edges (use-side). Range constraints, known bits, and
demanded bits are encoded directly on the IR edges rather than as separate instructions.
Additionally, simplify the text format by eliding the implicit top-level `region function`.

## Motivation

The current IR uses `assert_sext` and `assert_zext` as standalone instructions to express
range constraints on infinite precision integers:

```
v0 = param 0
v1 = assert_sext v0, 32
v2 = param 1
v3 = assert_sext v2, 32
v4 = add v1, v3
v5 = assert_sext v4, 32
ret v5
```

This has several problems:

1. **Instruction bloat** — Every constrained value requires a separate assert instruction,
   roughly doubling the instruction count for typical integer-heavy code.
2. **Artificial data dependencies** — Assert nodes create new SSA values (`v1` instead of
   `v0`), forcing all downstream uses to reference the asserted value. This complicates
   pattern matching in optimization passes.
3. **No place for analysis results** — The planned at-use bit-level analysis (known bits,
   demanded bits) has no natural home. Assert nodes only express range constraints, not
   arbitrary bit-level facts.
4. **Phase ordering** — Analysis results stored in side tables become stale after
   transformations. Encoding them in the IR itself keeps them synchronized.

Additionally, the text format wraps every function body in `region function { ... }`, which
is redundant since every function has exactly one top-level function region.

## Guide-level explanation

### Annotations on values

Every value reference in tuffy IR can carry an optional annotation describing constraints
on that value. Annotations appear in two positions:

- **Result-side**: on the value defined by an instruction, declaring the range of the output.
- **Use-side**: on an operand of an instruction, declaring a constraint the consumer requires.

### Annotation types

| Annotation | Meaning |
|---|---|
| `:s<N>` | Value is in signed N-bit range `[-2^(N-1), 2^(N-1)-1]` |
| `:u<N>` | Value is in unsigned N-bit range `[0, 2^N-1]` |
| `:known(<ternary>)` | Per-bit three-state constraint (see below) |
| (none) | No constraint; value is an unconstrained `int` |

Annotations are composable: `:s32:known(...)` applies both constraints simultaneously.

#### Known bits ternary encoding

Each bit in a `known` annotation is one of four states:

| Symbol | Meaning |
|---|---|
| `0` | Bit is known to be 0 |
| `1` | Bit is known to be 1 |
| `?` | Unknown — bit is demanded but its value has not been determined |
| `x` | Don't-care — bit is not demanded by the consumer |

Example: `:known(xxxx_??11_1111_0000)` means:
- Bits [0:3] are known-0
- Bits [4:9] are known-1
- Bits [8:9] are demanded but unknown
- Bits [10:] are don't-care (not demanded)

The distinction between `?` and `x` matters for optimization:
- **`?` (unknown)**: the consumer needs this bit, so the producer must supply a
  well-defined value. An analysis pass may later refine `?` to `0` or `1`.
- **`x` (don't-care)**: the consumer ignores this bit entirely. The producer is free
  to supply any value, enabling dead-bit elimination and narrowing optimizations.

### Example: `i32 a + i32 b` (C signed addition)

Before (assert nodes):

```
func @add_i32(int, int) -> int {
  region function {
    bb0:
      v0 = param 0
      v1 = assert_sext v0, 32
      v2 = param 1
      v3 = assert_sext v2, 32
      v4 = add v1, v3
      v5 = assert_sext v4, 32
      ret v5
  }
}
```

After (at-use annotations, top-level region elided):

```
func @add_i32(int:s32, int:s32) -> int:s32 {
  bb0:
    v0:s32 = param 0
    v1:s32 = param 1
    v2:s32 = add v0:s32, v1:s32
    ret v2:s32
}
```

6 instructions reduced to 4. No artificial SSA values from assert nodes.

### Example: optimization strengthening a use-side annotation

After an analysis pass discovers that `v1` is always in `[0, 100]` at a particular use:

```
func @example(int:s32) -> int:s32 {
  bb0:
    v0:s32 = param 0
    v1:s32 = add v0:s32, v0:s32
    v2:s32 = foo v1:u7              // use-side: optimizer proved v1 in [0, 127] here
    ret v2:s32
}
```

The `:u7` on the use of `v1` is stronger than the `:s32` on its definition. This is valid
because the use-side annotation is a local fact about this specific use site.

### Example: known bits after optimization

```
v3:s32:known(xxxx_xxxx_xxxx_xxxx_????_????_????_???0) = and v1:s32, v2:s32
```

The `and` result has bit 0 known to be 0 (discovered by analysis), bits [1:15] are
demanded but unknown, and bits [16:31] are don't-care.

### Semantics

**Result-side annotation violation**: the instruction itself produces `poison`.

```
v0:s8 = add v1, v2    // if the true result is 200, v0 becomes poison
```

**Use-side annotation violation**: the consuming instruction produces `poison`.

```
v1 = foo v0:u4        // if v0 is 20, then foo produces poison
```

**Constraint strength**: a use-side annotation may be stronger (narrower) than the
result-side annotation on the referenced value. It must not be weaker — a weaker
use-side annotation is redundant and should be omitted.

**No annotation**: the value is an unconstrained infinite precision `int`. During
instruction selection, the verifier reports an error if it cannot determine a concrete
machine type for an unconstrained value.

### Function signatures

Function signatures carry annotations on parameter types and the return type. These
are ABI-level contracts between caller and callee:

```
func @add_i32(int:s32, int:s32) -> int:s32 { ... }
```

- **Parameter annotation**: the caller guarantees the argument satisfies the constraint.
  Inside the function body, `param` result-side annotations match the signature.
- **Return annotation**: the callee guarantees the return value satisfies the constraint.
  The `ret` use-side annotation must be at least as strong as the signature's return
  annotation.

### Text format: elide top-level region

Every function has exactly one top-level `region function`. The text format elides it:

```
// Before:
func @f(int) -> int {
  region function {
    bb0:
      ...
  }
}

// After:
func @f(int) -> int {
  bb0:
    ...
}
```

Inner regions (`loop`, `plain`) are still written explicitly.

## Reference-level explanation

### Annotation representation

In the Rust implementation, annotations are stored alongside each operand (use-side) and
each instruction result (result-side). A compact representation:

```rust
/// Per-bit four-state annotation.
struct KnownBits {
    /// Bits known to be 1.
    ones: BigUint,
    /// Bits known to be 0.
    zeros: BigUint,
    /// Bits that are demanded by the consumer.
    demanded: BigUint,
}
```

Invariant: `ones & zeros == 0` (a bit cannot be simultaneously known-0 and known-1).

The `:s<N>` and `:u<N>` shorthand annotations are sugar over `KnownBits`:
- `:s32` implies demanded bits [0:31], with the sign bit propagation constraint.
- `:u32` implies demanded bits [0:31], with bits [32:] known-0.

### Interaction with other features

**Block arguments**: block arguments carry result-side annotations. Branch instructions
carry use-side annotations on the passed values:

```
bb0:
  v0:s32 = iconst 42
  br bb1(v0:s32)

bb1(v1:s32: int):
  ret v1:s32
```

**Terminators**: `ret`, `br`, `brif`, `continue`, `region_yield` all carry use-side
annotations on their operands.

**Memory operations**: `load` result carries a result-side annotation. `store` value
operand carries a use-side annotation. Pointer operands are not annotated (pointers
have concrete types).

**Instruction selection**: the verifier walks all values and checks that every `int`
value has sufficient annotation (result-side or use-side) to determine a concrete
machine type. Missing annotations are reported as errors.

### Grammar changes

```
annotation   ::= (':' range_ann)*
range_ann    ::= 's' N | 'u' N | 'known' '(' ternary ')'
ternary      ::= [01?x_]+

function     ::= 'func' '@' name '(' param_list ')' ('->' type annotation)? '{' body '}'
param_list   ::= (type annotation (',' type annotation)*)?
body         ::= (block | region)*
instruction  ::= (value annotation '=')? opcode operands
operand      ::= value annotation
```

The top-level `region function { ... }` wrapper is removed from the grammar. The
function body directly contains blocks and regions.

## Drawbacks

- **Annotation storage overhead** — Every use edge now carries optional annotation data.
  For dense integer code this may increase memory usage compared to standalone assert
  instructions (one annotation per use vs one instruction per value).
- **Complexity in the builder API** — The builder must accept annotations on every operand,
  making the API surface larger.
- **Parsing complexity** — The text format parser must handle annotations on every value
  reference, increasing grammar complexity.

## Rationale and alternatives

### Why annotations on edges instead of standalone instructions?

The core insight is that range constraints and bit-level facts are properties of
**how a value is used**, not properties of the value itself. A value `v0` may be in
the full `int` range, but a particular consumer may only need 8 bits of it. Encoding
this on the use edge is the natural representation.

### Alternative: keep assert nodes, add side-table analyses

This is the LLVM approach — `KnownBits` and `DemandedBits` live in analysis caches
outside the IR. The problem is phase ordering: after a transformation, the side tables
are stale and must be recomputed. Tuffy's "analysis is also a transformation" principle
rejects this approach.

### Alternative: assert nodes with use-side annotations (hybrid)

Keep assert nodes for result-side constraints, add use-side annotations only for
analysis results. This avoids changing the instruction set but retains the instruction
bloat problem and the artificial SSA value issue.

### Why signed/unsigned is a binary choice

A natural question is whether annotations should support expressing both signed and
unsigned constraints simultaneously — e.g., a value that is both `:s32` and `:u16`.
The answer is no, because the intersection of any two range annotations is always
expressible as a single annotation:

| Intersection | Result | Reasoning |
|---|---|---|
| `:s<M>` ∩ `:s<N>` | `:s<min(M,N)>` | Smaller signed range is a subset of the larger |
| `:u<M>` ∩ `:u<N>` | `:u<min(M,N)>` | Smaller unsigned range is a subset of the larger |
| `:s<M>` ∩ `:u<N>` | `:u<min(M-1, N)>` | The non-negative portion of `:s<M>` is `[0, 2^(M-1)-1]`, which equals `:u<M-1>` |

The third case is the key insight. A signed N-bit value is in `[-2^(N-1), 2^(N-1)-1]`.
An unsigned M-bit value is in `[0, 2^M-1]`. Their intersection is
`[0, min(2^(N-1)-1, 2^M-1)]`, which is always an unsigned range expressible as
`:u<min(N-1, M)>`.

Since any combination of signed and unsigned constraints collapses to a single
annotation, supporting both simultaneously adds no expressive power — it only adds
implementation complexity.

For constraints that range annotations genuinely cannot express (e.g., "bit 3 is
known to be 1" or "bits above 8 are don't-care"), the `KnownBits` extension is the
correct generalization. `KnownBits` subsumes range annotations entirely: `:s32` and
`:u32` are sugar over specific `KnownBits` patterns.

### Impact of not doing this

Without this change, the IR would need both assert nodes (for range constraints) and
a separate mechanism (side tables or new annotation syntax) for known/demanded bits.
Two parallel systems for the same concept.

## Prior art

- **LLVM KnownBits / DemandedBits** — Side-table analyses that track per-bit information.
  Effective but disconnected from the IR, causing phase ordering issues and stale results
  after transformations. Tuffy's approach promotes these to first-class IR constructs.
- **Cranelift aegraph annotations** — Cranelift's e-graph framework attaches facts to
  values (range constraints for proof-carrying code). Similar in spirit to result-side
  annotations, but not on use edges.
- **MLIR type refinement** — MLIR dialects can carry refined type information on values.
  However, MLIR's approach is type-based (the type itself changes), not annotation-based
  (the type stays `int`, annotations are metadata).

## Unresolved questions

- **Compact storage for common cases** — Most annotations will be simple `:s32` or `:u64`.
  Should the implementation use a small-enum optimization to avoid allocating `BigUint`
  for these common cases?
- **Annotation canonicalization** — Should redundant annotations (e.g., `:s32` on a use
  when the result already has `:s32`) be stripped automatically, or preserved for
  readability?
- **Lean formalization** — How should annotations be represented in the Lean formal model?
  As metadata on the operational semantics, or as part of the value type?

## Future possibilities

- **Annotation inference pass** — A dedicated pass that propagates known bits forward and
  demanded bits backward, filling in `?` bits with `0`/`1` and narrowing `?` to `x`
  where possible.
- **Annotation-driven instruction selection** — The instruction selector reads annotations
  directly to choose machine instructions, register classes, and sign/zero extension
  without a separate legalization phase.
- **Annotation-aware rewrite rules** — Declarative rewrite rules that match on annotation
  patterns, e.g., "if all bits above bit 7 are don't-care, narrow to 8-bit operation".
- **Floating point annotations** — Extend the annotation system to floating point values
  (e.g., known-NaN, known-finite, known-positive).
