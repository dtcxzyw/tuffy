# Add DontCare(N) Annotation for Integers

- Status: Completed
- Created: 2026-03-04
- Completed: 2026-03-04
- Parent: N/A

## Description

Add a `DontCare(N)` annotation variant to the integer `Annotation` type, indicating that only the
lower N bits of the value are meaningful — the upper bits are undefined (may be 0 or 1 freely).

### Rationale

The existing annotations model *value-range* constraints:

- `Signed(N)` — value is in `[-2^(N-1), 2^(N-1)-1]`
- `Unsigned(N)` — value is in `[0, 2^N-1]`

These are insufficient to model operations like wrapping arithmetic. For example, a
`wrapping_add i32 %a, %b` in Rust produces a full 32-bit result that is mathematically well-defined
modulo `2^32`, but from the caller's perspective the high bits of the infinite-precision integer are
garbage. Forcing `Unsigned(32)` would be wrong when the true mathematical result is negative.
`DontCare(N)` cleanly captures this: *"I only guarantee the low N bits; treat everything above as
undef."*

### Semantics

A value annotated `DontCare(N)` satisfies:

- The lower N bits are the authoritative result; consumers must mask or truncate before use.
- Any bit at position ≥ N is allowed to hold any value.
- A use-site `DontCare(N)` annotation means the consumer promises it will only inspect the lower N
  bits (dual to the definition-side semantics), enabling the optimizer to propagate undef freely
  through the high bits.

This design is consistent with the existing annotation-as-constraint philosophy: violating the
annotation at definition or use produces poison.

### Design

**Lean 4 (source of truth — `lean/TuffyLean/IR/Types.lean`):**

Add a new variant to the `Annotation` inductive type:

```lean
| dontCare (bits : Nat) : Annotation
  -- Only the lower `bits` bits of the integer value are significant;
  -- all higher bits are undefined.
```

Add corresponding semantics in `lean/TuffyLean/IR/Semantics.lean` (or a new
`lean/TuffyLean/IR/Annotation.lean` if the file grows): define the validity predicate for
`dontCare` annotations and document interaction rules with existing `signed`/`unsigned` annotations.

**Rust (`tuffy_ir/src/types.rs`):**

Add `DontCare(u32)` to the `Annotation` enum:

```rust
DontCare(u32),  // :dc<N> — only low N bits are meaningful
```

Display format: `:dc<N>` (e.g., `:dc32`).

Update all match arms on `Annotation` throughout `tuffy_ir`.

**Verifier (`tuffy_ir/src/verifier.rs`):**

- Reject `DontCare(0)` (zero meaningful bits is nonsensical).
- Reject `DontCare(N)` where N ≥ bit-width of the integer type (the annotation is vacuous; use no
  annotation or `Unsigned(N)` instead).

**Optimizer / passes:**

Document (in code comments and/or a follow-up RFC) the rewrite rules enabled by `DontCare`:

- `DontCare(N)` result of `add/sub/mul` with matching-width operands → the operation need not
  preserve high bits, enabling cheaper codegen (e.g., plain `ADD` without sign/zero extension).
- `DontCare(N)` on both sides of an `icmp` → undefined; flag as poison or add a verifier error.

## Subtasks

1. Add `dontCare` variant to `Annotation` in `lean/TuffyLean/IR/Types.lean`
2. Add validity predicate and semantics for `dontCare` in the Lean IR semantics
3. Add `DontCare(u32)` variant to `Annotation` in `tuffy_ir/src/types.rs`
4. Update display formatting (`:dc<N>`) in `tuffy_ir/src/display.rs`
5. Update verifier checks for `DontCare` in `tuffy_ir/src/verifier.rs`
6. Update all other `Annotation` match arms in `tuffy_ir` (instruction.rs, etc.)
7. Add tests covering `DontCare` construction, display, and verifier rejection cases

## Affected Modules

- `lean/TuffyLean/IR/Types.lean` — add `dontCare` variant (source of truth)
- `lean/TuffyLean/IR/Semantics.lean` — add validity predicate and interaction rules
- `tuffy_ir/src/types.rs` — add `DontCare(u32)` variant
- `tuffy_ir/src/display.rs` — format `:dc<N>`
- `tuffy_ir/src/verifier.rs` — validate `DontCare` constraints
- `tuffy_ir/src/instruction.rs` — update `Annotation` match arms if present
- `tuffy_ir/src/tests.rs` — add tests
