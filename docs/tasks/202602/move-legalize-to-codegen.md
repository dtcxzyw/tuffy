# Move legalization pass from tuffy_target_x86 to tuffy_codegen

- Status: Draft
- Created: 2026-02-28
- Completed: N/A
- Parent: N/A

## Description

Currently the legalization pass (`legalize.rs`, ~1574 lines) lives in `tuffy_target_x86` and only handles i128/u128. However, legalization is a broader, target-independent concern. It must handle three categories of illegal IR:

1. **Wide integer splitting** — split operations on integers wider than the target's native register width into sequences of narrower operations. This is not limited to 128-bit; it applies to any width exceeding the target's legal maximum (e.g., 64-bit on x86-64). The splitting algorithm is recursive: a 256-bit op splits into two 128-bit ops, each of which splits into two 64-bit ops.
2. **Unsupported op expansion** — rewrite ops that have no direct machine instruction into combinations of supported ops (e.g., `RotateLeft` → shift+or sequence on targets without native rotate, `CountOnes` → Kernighan's algorithm on targets without `popcnt`).
3. **Library call lowering** — replace ops that cannot be efficiently expanded inline with calls to runtime library functions (e.g., `Div`/`Rem` on 128-bit integers → `__divti3`/`__modti3`, soft-float operations → `__addsf3`, etc.).

The legalization driver is target-independent. Only the *legality query* ("can this target handle op X on type/width Y?") and the *action* (expand inline vs libcall) are target-specific.

## Design

### Legality trait (`tuffy_target`)

```rust
enum LegalizeAction {
    /// Op is natively supported — no transformation needed.
    Legal,
    /// Expand into a sequence of legal ops (e.g., wide split, shift+or).
    Expand,
    /// Replace with a library call (e.g., __divti3).
    LibCall(&'static str),
}

trait LegalityInfo {
    /// Query whether (op, annotation-width) is legal on this target.
    fn legalize_action(&self, op: &Op, width: Option<u32>) -> LegalizeAction;

    /// Maximum integer width natively supported (e.g., 64 for x86-64).
    fn max_int_width(&self) -> u32;
}
```

### Legalization driver (`tuffy_codegen`)

The driver iterates to a fixpoint:

1. Walk all instructions in the function.
2. For each instruction, query `LegalityInfo::legalize_action`.
3. If `Expand` — apply the appropriate rewrite rule (wide split, op expansion).
4. If `LibCall` — replace with a `Call` to the named symbol.
5. Repeat until all instructions are legal.

The rewrite rules are generic algorithms parameterized by width:
- Wide integer splitting: split N-bit op into two N/2-bit ops with carry propagation.
- Op expansion: express unsupported ops in terms of supported ones.

### x86 legality (`tuffy_target_x86`)

Implements `LegalityInfo` declaring:
- `max_int_width() = 64`
- Arithmetic ops (`Add`, `Sub`, `Mul`, `And`, `Or`, `Xor`, `Shl`, `Shr`) legal at widths ≤ 64
- `Div`/`Rem` at width > 64 → `LibCall("__divti3")` / `LibCall("__modti3")`
- `CountOnes` → `Legal` (x86 has `popcnt`), or `Expand` if target lacks `popcnt`
- `RotateLeft`/`RotateRight` → `Legal` (x86 has `rol`/`ror`)
- etc.

### Current state

`tuffy_target_x86/src/legalize.rs` contains everything monolithically:

- i128/u128 detection and value mapping infrastructure
- Full IR rewrite engine (region walk, block remapping, instruction copy)
- ~30 operation-specific lowering functions (hardcoded to 128→64 split)
- x86-specific ABI metadata remapping

### Target state

```
tuffy_target/src/legality.rs      — LegalityInfo trait + LegalizeAction enum
tuffy_codegen/src/legalize.rs     — target-independent driver + generic rewrite rules
tuffy_target_x86/src/legality.rs  — X86LegalityInfo impl (replaces legalize.rs)
```

## Reference: LLVM GlobalISel Pipeline

Reference: https://llvm.org/docs/GlobalISel/Pipeline.html

LLVM's GlobalISel pipeline consists of four stages:

1. **IRTranslator** — converts LLVM-IR into gMIR (Generic MIR), a relaxed MIR with typed virtual registers.
2. **Legalizer** — replaces unsupported operations with supported ones. Actions include: `Legal`, `NarrowScalar`, `WidenScalar`, `FewerElements`, `MoreElements`, `Lower` (expand into equivalent ops), `Libcall`, `Custom`.
3. **RegBankSelect** — binds virtual registers to register banks, minimizing cross-bank copies.
4. **InstructionSelect** — selects target instructions from legalized gMIR.

Tuffy's pipeline compared to GlobalISel:

```
GlobalISel:  LLVM-IR → IRTranslator → Legalizer → RegBankSelect → InstructionSelect
Tuffy:       tuffy IR → Legalizer → InstructionSelect (+ RegAlloc)
```

Key differences:
- **No IRTranslator** — Tuffy's frontend (`rustc_codegen_tuffy`) emits tuffy IR directly; there is no intermediate gMIR representation. The IR is already in a form suitable for legalization.
- **No RegBankSelect** — Tuffy currently has a single register class (GPR). Register bank selection can be added later when SIMD/FP register files are introduced.
- **LegalizeAction mapping** — Tuffy's `Expand` corresponds to LLVM's `NarrowScalar` + `Lower`; Tuffy's `LibCall` maps directly to LLVM's `Libcall`.

## Subtasks

1. Design `LegalityInfo` trait in `tuffy_target` with `LegalizeAction` enum
2. Move the legalization driver (IR walk, value mapping, block remapping) to `tuffy_codegen`
3. Generalize rewrite rules from hardcoded 128→64 to recursive N→N/2 splitting
4. Add op expansion rules for unsupported ops (rotate, popcount, etc.)
5. Add libcall lowering for ops that cannot be expanded inline (wide div/rem, soft-float)
6. Implement `X86LegalityInfo` in `tuffy_target_x86`
7. Refactor ABI metadata handling to work through the target abstraction
8. Remove `tuffy_target_x86/src/legalize.rs`
9. Verify `cargo test` and `cargo clippy` pass
10. Run rustlantis fuzzing seeds to confirm no regressions

## Affected Modules

- `tuffy_target/src/` — new `LegalityInfo` trait + `LegalizeAction` enum
- `tuffy_codegen/src/` — new legalization driver + generic rewrite rules
- `tuffy_target_x86/src/legalize.rs` — to be replaced by legality declaration
- `tuffy_target_x86/src/backend.rs` — update pipeline to use new legalization
