# Refine IR: eliminate redundant opcodes and fix semantic bugs

- Status: Completed
- Created: 2026-02-09
- Completed: 2026-02-09
- Parent: N/A

## Description

Clean up the tuffy IR instruction set by:

1. **Eliminating signedness-split instructions.** In the infinite precision
   integer model, signedness is a property of operand annotations, not of
   instructions. Instruction pairs that duplicate the same mathematical
   semantics should be merged, with isel reading annotations to choose the
   correct machine instruction.

2. **Fixing semantic bugs** in existing instruction definitions.

3. **Designing scalable vector types.** Vector types should be parameterized by
   total bit-width rather than element count, consistent with the infinite
   precision integer model where bit-width is an annotation. Element count is
   derived: `count = total_bits / element_bits`.

The div/rem merge (SDiv+UDiv → Div, SRem+URem → Rem) has already been
completed and serves as the template for further merges.

## Subtasks

### Signedness merges

- [x] Merge SDiv/UDiv → Div, SRem/URem → Rem (completed 2026-02-09)
- [x] Merge Lshr/Ashr → Shr (completed 2026-02-09)
- [x] Merge ICmpOp signed/unsigned pairs: Slt/Ult → Lt, Sle/Ule → Le, Sgt/Ugt → Gt, Sge/Uge → Ge (completed 2026-02-09)

### Spec clarifications

- [x] Document in spec that load returns `List AbstractByte` and store takes
  `List AbstractByte` — memory access operates at the byte level only. Type
  interpretation (bytes → int/float) is a separate step, cleanly separating
  memory access from type semantics. (completed 2026-02-09)
- [x] Define `bytecast` semantics in Lean. Design decisions:
  - Annotations are always droppable — they never determine semantics.
  - `b<N>` requires N to be a multiple of 8 (byte-aligned).
  - `bytecast b<N> → int` low N*8 bits are determined by byte contents;
    high bits are **unspecified**. The caller must apply `zext` or `sext`
    to obtain a fully determined value.
  - `bytecast b<N> → float/double` requires exact size match (b32 → float,
    b64 → double). Size mismatch is ill-formed.
  - Handle all four AbstractByte states: `Bits` → decode, `Poison` → poison,
    `Uninit` → poison, `PtrFragment` → ptrtoint semantics.
  (completed 2026-02-09)

### Semantic fixes

- [x] Fix evalCopySign: uses `sign < 0.0` which is false for `-0.0` (IEEE 754
  negative zero equals positive zero in comparison) and also false for `-NaN`
  (NaN compares false with everything). Must check the sign bit instead, so
  `copysign(1.0, -0.0)` correctly returns `-1.0`. Fix: use `Float.toBits` to
  extract the sign bit (bit 63 of the UInt64 representation). (completed 2026-02-09)

### IEEE 754-2008 conformance

- [x] Adopt IEEE 754-2008 as the floating-point semantics standard for the IR (completed 2026-02-09)

### Scalable vector types

Design vector types parameterized by bit-width, not element count. Reference:
[Google Highway](https://github.com/google/highway) library.

Key design points (derived from Highway's model):

- The fundamental parameter is total bit-width; element count is derived from
  `total_bits / element_bits`.
- Scalable vectors use `vscale × base_width`, where `vscale` is a runtime
  constant determined by hardware (cf. SVE, RVV).
- Well-formedness constraints: `total_bits % element_bits == 0` and the
  resulting lane count must be a power of two.
- Fractional vectors (e.g. half-width) are naturally expressed as smaller
  bit-widths, no extra mechanism needed.

Subtasks:

- [x] Draft RFC for bit-width-parameterized vector type (completed 2026-02-09)
- [x] Define vector type in Lean 4 IR (completed 2026-02-09)
- [x] Implement vector type in Rust IR (completed 2026-02-09)

## Affected Modules

- `lean/TuffyLean/IR/Semantics.lean` — merge evalLshr/evalAshr into evalShr
- `tuffy_ir/src/instruction.rs` — merge Op::Lshr/Op::Ashr into Op::Shr
- `tuffy_ir/src/builder.rs` — merge lshr()/ashr() into shr()
- `tuffy_ir/src/display.rs` — merge display arms into "shr"
- `tuffy_ir/src/tests.rs` — update shift display test
- `tuffy_target_x86/src/isel.rs` — isel reads annotation to choose SHR vs SAR
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — emit builder.shr() with annotations
- `docs/spec.md` — merge lshr/ashr sections into shr
- `docs/RFCs/202602/ir-design.md` — update instruction table
