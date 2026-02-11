# Translate Rust bool as Type::Bool instead of Type::Int

- Status: Draft
- Created: 2026-02-11
- Completed: N/A
- Parent: N/A

## Description

Currently, `rustc_codegen_tuffy` translates Rust's `bool` type as `Type::Int` with
`Annotation::Unsigned(8)`, effectively erasing boolean semantics at the MIR-to-IR boundary.

However, tuffy IR has a dedicated `Type::Bool` type: `ICmp` returns `Bool`, `Select` expects
a `Bool` condition, and `BoolToInt` exists for explicit conversion. The current translation
is inconsistent — IR-internal comparisons produce `Bool`, but MIR-originating bool values
are `Int`.

This task fixes the translation so that Rust `bool` maps to `Type::Bool`, preserving
semantic information and making the IR consistent.

### Changes required

1. `translate_ty`: `ty::Bool` → `Type::Bool` (not `Type::Int`)
2. `translate_annotation`: `ty::Bool` → `None` (Bool has no bit-width annotation)
3. `bit_width`: remove the `ty::Bool => Some(8)` arm (or map to a Bool-appropriate value)
4. Bool constants: emit as `Type::Bool` values instead of `iconst`
5. Anywhere a bool value is used as an integer (e.g., stored to memory, passed as argument),
   insert explicit `BoolToInt` conversion
6. Anywhere an integer is used where `Bool` is expected (e.g., loaded from memory),
   insert explicit `IntToBool` or comparison-to-zero

### Potential complications

- Memory load/store: `bool` is 1 byte in memory, so load/store still needs integer semantics.
  The conversion between `Bool` and `Int` must happen at load/store boundaries.
- ABI: function arguments and return values of type `bool` are passed as integers in the
  calling convention. Conversion is needed at call boundaries.

## Subtasks

- (inline) Update `translate_ty` for `ty::Bool`
- (inline) Update `translate_annotation` for `ty::Bool`
- (inline) Handle bool constants
- (inline) Insert BoolToInt at integer-use sites
- (inline) Handle bool load/store with proper conversion
- (inline) Update or add tests

## Affected Modules

- `rustc_codegen_tuffy` — MIR-to-IR translation (`mir_to_ir.rs`)
- `tuffy_ir` — may need `IntToBool` instruction if not already present
