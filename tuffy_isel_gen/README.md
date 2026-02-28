# tuffy_isel_gen

Code generator for instruction selection rules.

## Purpose

CLI tool that reads instruction selection rules from a JSON file (exported from Lean 4 formal definitions) and generates Rust source code (`isel_gen.rs`) for pattern-matching dispatch in target backends.

## Usage

```
tuffy_isel_gen <input.json> <output.rs>
```

## Architecture

### `schema.rs` — JSON Schema Types

Deserializes the Lean export format into Rust types:

- `IselRule` — a single rule: name, IR pattern, emitted instructions, and result kind.
- `IrPattern` — what to match: `Binop`, `Unop`, or `Icmp`, each with operand patterns.
- `OperandPat` — operand pattern with register name and annotation guard (`Any`, `Signed`, `Unsigned`).
- `EmitInst` — x86 instruction to emit (e.g., `AddRR`, `SubRR`, `CmpRR`, `ShlRCL`).
- `ResultKind` — how the result is produced: `Reg`, `CmpFlags`, or `None`.

### `codegen.rs` — Rust Code Generation

Generates the complete `isel_gen.rs` source file:

1. Per-rule helper functions that emit machine instructions.
2. A dispatch function that matches IR opcodes to the appropriate rule.

Register allocation within generated code uses `RegEnv` to track named and fresh virtual registers.

## Dependencies

- `serde`, `serde_json` — JSON deserialization
