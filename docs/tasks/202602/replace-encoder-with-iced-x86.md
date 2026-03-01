# Replace custom x86 encoder with iced-x86

- Status: Completed
- Created: 2026-02-28
- Completed: 2026-02-28
- Parent: N/A

## Description

`tuffy_target_x86/src/encode.rs` (~918 lines) is a hand-written x86-64 machine code encoder that manually constructs REX prefixes, ModR/M bytes, immediates, and relocation placeholders for each `MInst` variant (~54 instruction patterns). This is error-prone, hard to extend, and duplicates work already done by mature libraries.

The goal is to replace `encode.rs` with [iced-x86](https://github.com/icedland/iced), a complete x86/x64 disassembler, assembler, and encoder library. iced-x86 provides:

- Correct encoding for all x86/x64 instructions (including VEX, EVEX, etc.)
- Built-in label/fixup resolution
- Relocation support
- Instruction validation

### Current architecture

```
MInst<Gpr> (post-regalloc) → encode.rs (hand-written) → Vec<u8> + Vec<Relocation>
                                                          ↓
                                                     emit.rs → ELF .o (via `object` crate)
```

`encode.rs` handles:
- REX prefix computation and emission
- ModR/M + SIB encoding for register-register and memory operands
- Immediate encoding (8/16/32/64-bit)
- Jump fixup (two-pass: emit with placeholder, then patch rel32)
- External symbol relocation tracking

### Target architecture

```
MInst<Gpr> (post-regalloc) → iced-x86 Encoder → Vec<u8> + Vec<Relocation>
                                                    ↓
                                               emit.rs → ELF .o (unchanged)
```

`emit.rs` (ELF emission via `object` crate) is unaffected — it consumes `CompiledFunction` which is just `(name, code_bytes, relocations)`.

### Migration approach

Each `MInst` variant in `encode_inst()` maps to one or more iced-x86 `Instruction` constructors. For example:

```rust
// Before (hand-written):
MInst::AddRR { size, dst, src } => encode_alu_rr(0x01, *size, *dst, *src, buf),

// After (iced-x86):
MInst::AddRR { size, dst, src } => {
    encoder.encode(&Instruction::with2(
        size_to_iced_code(Code::Add_rm64_r64, *size),
        to_iced_reg(*dst),
        to_iced_reg(*src),
    )?)?;
}
```

External symbol references (calls, LEA of globals) still need relocation tracking. iced-x86 can encode the instruction with a placeholder immediate; we record the relocation offset as before.

## Subtasks

1. Add `iced-x86` dependency to `tuffy_target_x86/Cargo.toml` (encoder feature only)
2. Write `MInst<Gpr>` → `iced_x86::Instruction` mapping layer
3. Handle label resolution using iced-x86's `BlockEncoder` or manual fixup
4. Preserve relocation tracking for external symbols
5. Replace `encode_function()` implementation
6. Remove hand-written encoding helpers (REX, ModR/M, SIB, immediate emitters)
7. Verify byte-identical or functionally equivalent output on existing tests
8. Verify `cargo test` and `cargo clippy` pass
9. Run rustlantis fuzzing seeds to confirm no regressions

## Affected Modules

- `tuffy_target_x86/Cargo.toml` — add `iced-x86` dependency
- `tuffy_target_x86/src/encode.rs` — rewrite to use iced-x86 encoder
- `tuffy_target_x86/src/inst.rs` — may need minor adjustments for iced-x86 mapping
