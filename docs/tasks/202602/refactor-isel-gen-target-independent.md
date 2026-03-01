# Refactor tuffy_isel_gen to be target-independent

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-03-01
- Parent: N/A

## Description

`tuffy_isel_gen` is supposed to be a generic code generator that reads isel rules from JSON and produces Rust matching code. However, it currently has x86-specific knowledge hardcoded throughout:

### x86-specific code in `schema.rs`

`EmitInst` enum has hardcoded x86 instruction variants:

```rust
enum EmitInst {
    MovRR { size, dst, src },
    AddRR { size, dst, src },
    SubRR { size, dst, src },
    ImulRR { size, dst, src },
    // ... 14 x86-specific variants
}
```

This should be a generic representation driven by the JSON export.

### x86-specific code in `codegen.rs`

- `fixed_reg_to_rust()` — hardcodes x86 GPR names (`Gpr::Rax`, `Gpr::Rcx`, etc.)
- `size_to_rust()` — hardcodes x86 `OpSize` variants (`S8`, `S16`, `S32`, `S64`)
- `cc_to_rust()` — hardcodes x86 `CondCode` variants (`E`, `Ne`, `L`, `Le`, etc.)
- `emit_inst()` — generates `MInst::Xxx { ... }` push statements for each hardcoded x86 variant
- Import preamble — emits `use crate::inst::{CondCode, MInst, OpSize}` and `use crate::reg::Gpr`

### What is NOT x86-specific

The IR-side pattern matching (`IrPattern`, `op_variant_pattern`, `op_operand_names`) and the dispatch logic (`generate_dispatch`) operate on tuffy IR opcodes, which are target-independent. These can remain as-is.

## Design

The JSON export should fully describe the target machine instructions, so the code generator never needs to know what target it is generating for.

### Generic EmitInst schema

Replace the hardcoded `EmitInst` enum with a data-driven representation:

```json
{
  "inst": "AddRR",
  "rust_type": "MInst::AddRR",
  "fields": [
    { "name": "size", "kind": "size", "value": "s64" },
    { "name": "dst", "kind": "reg", "ref": { "kind": "fresh", "name": "d" } },
    { "name": "src", "kind": "reg", "ref": { "kind": "named", "name": "r" } }
  ]
}
```

The code generator treats each emitted instruction as a generic struct with named fields. Field kinds:
- `reg` — a register reference (named, fresh, or fresh-fixed)
- `size` — an opaque enum value, passed through as-is (e.g., `OpSize::S64`)
- `cc` — an opaque enum value for condition codes
- `literal` — a literal Rust expression

### Generic import preamble

The JSON export should include a list of `use` statements the generated file needs:

```json
{
  "imports": [
    "use crate::inst::{CondCode, MInst, OpSize};",
    "use crate::reg::Gpr;"
  ],
  "fixed_regs": {
    "rax": "Gpr::Rax.to_preg()",
    "rcx": "Gpr::Rcx.to_preg()"
  },
  "size_map": {
    "s8": "OpSize::S8",
    "s64": "OpSize::S64"
  },
  "cc_map": {
    "e": "CondCode::E",
    "ne": "CondCode::Ne"
  }
}
```

This moves all target-specific string mappings into the JSON input, making the code generator purely mechanical.

## Subtasks

1. Design the generic JSON schema for emitted instructions (replace hardcoded `EmitInst` enum)
2. Add target-level metadata to JSON input (imports, fixed register map, size map, condition code map)
3. Rewrite `schema.rs` to deserialize the generic representation
4. Rewrite `codegen.rs` `emit_inst()` to generate code from generic field descriptions
5. Remove `fixed_reg_to_rust()`, `size_to_rust()`, `cc_to_rust()` hardcoded mappings
6. Update the Lean export to produce the new JSON format
7. Regenerate `isel_gen.rs` and verify output is equivalent
8. Verify `cargo test` and `cargo clippy` pass

## Affected Modules

- `tuffy_isel_gen/src/schema.rs` — replace `EmitInst` enum with generic representation
- `tuffy_isel_gen/src/codegen.rs` — remove x86-specific mappings, generate from generic fields
- `lean/TuffyLean/Export/` — update JSON export format
- `tuffy_target_x86/src/isel_gen.rs` — regenerated output (should be functionally identical)
