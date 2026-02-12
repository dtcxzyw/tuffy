# Lean 4 Isel Rule DSL + Rust Code Generator

- Status: Completed
- Created: 2026-02-11
- Completed: 2026-02-12
- Parent: N/A

## Description

The x86 instruction selection in `tuffy_target_x86/src/isel.rs` contains ~15 recurring patterns (binop, shift, cmp+cmov, etc.) that are hand-written Rust. These patterns are mechanical mappings from IR ops to x86 instruction sequences, differing only in which MInst variant and condition codes to use.

The goal is to define these patterns declaratively in Lean 4, export them as JSON, and use a Rust code generator to produce the isel dispatch code. This gives us:

- Single source of truth in Lean (with future path to correctness proofs)
- Less hand-written boilerplate in isel.rs
- Easier to add new rules

### Architecture

```
Lean 4 DSL (rules)  -->  JSON  -->  Rust codegen tool  -->  isel_gen.rs
lean/TuffyLean/          lean/       tuffy_isel_gen/        tuffy_target_x86/
Target/X86/              target/                            src/isel_gen.rs
```

### Scope

**In scope (declarative rules):** Add, Sub, Mul, Or, And, Xor, Shl, Shr, Min, Max, CountOnes, ICmp, PtrAdd, PtrDiff

**Out of scope (remain hand-written):** Param, Const, Br, BrIf, Ret, Call, Load, Store, StackSlot, Select, BoolToInt, Sext, Zext, Div, Rem, SymbolAddr, Bitcast/PtrToInt/IntToPtr

These are either too complex (BrIf with block args, Div with RAX/RDX dance), need special context (Const with rdx_captures), or have irregular patterns (BoolToInt checking CmpMap).

## Subtasks

### Step 1: Lean x86 Isel DSL

New files under `lean/TuffyLean/Target/X86/`:

**`Defs.lean`** — Core DSL types:

```lean
inductive OpSize where | s8 | s16 | s32 | s64
inductive CondCode where | e | ne | l | le | g | ge | b | be | a | ae
inductive FixedReg where | rax | rcx | rdx | rbp

inductive RegRef where
  | named (name : String)                       -- bound from pattern
  | fresh (name : String)                       -- allocate new vreg
  | freshFixed (name : String) (reg : FixedReg) -- new vreg with constraint

inductive AnnGuard where
  | any | signed | unsigned

inductive EmitInst where
  | movRR (size : OpSize) (dst src : RegRef)
  | addRR (size : OpSize) (dst src : RegRef)
  | subRR (size : OpSize) (dst src : RegRef)
  | imulRR (size : OpSize) (dst src : RegRef)
  | orRR  (size : OpSize) (dst src : RegRef)
  | andRR (size : OpSize) (dst src : RegRef)
  | xorRR (size : OpSize) (dst src : RegRef)
  | shlRCL (size : OpSize) (dst : RegRef)
  | shrRCL (size : OpSize) (dst : RegRef)
  | sarRCL (size : OpSize) (dst : RegRef)
  | cmpRR (size : OpSize) (src1 src2 : RegRef)
  | cmovCC (size : OpSize) (cc : CondCode) (dst src : RegRef)
  | popcnt (dst src : RegRef)
```

**`IselRule.lean`** — Rule structure:

```lean
inductive IrPattern where
  | binop (op : String) (lhs rhs : OperandPat)
  | unop (op : String) (val : OperandPat)
  | icmp (lhs rhs : OperandPat)

structure OperandPat where
  regName : String
  annGuard : AnnGuard := .any

inductive ResultKind where
  | reg (name : String)
  | cmpFlags
  | none

structure IselRule where
  name : String
  pattern : IrPattern
  emit : List EmitInst
  result : ResultKind
  icmpCcFromOp : Bool := false
```

**`Rules.lean`** — Concrete rule definitions:

```lean
def addRule : IselRule := {
  name := "add"
  pattern := .binop "Add" ⟨"lhs"⟩ ⟨"rhs"⟩
  emit := [.movRR .s64 (.fresh "dst") (.named "lhs"),
           .addRR .s64 (.fresh "dst") (.named "rhs")]
  result := .reg "dst"
}

def minSignedRule : IselRule := {
  name := "min_signed"
  pattern := .binop "Min" ⟨"lhs", .signed⟩ ⟨"rhs"⟩
  emit := [.movRR .s64 (.fresh "dst") (.named "rhs"),
           .cmpRR .s64 (.named "lhs") (.named "rhs"),
           .cmovCC .s64 .l (.fresh "dst") (.named "lhs")]
  result := .reg "dst"
}

def allRules : List IselRule := [addRule, subRule, ...]
```

### Step 2: JSON Export

Extend `lean/TuffyLean/Export/Json.lean` to serialize `allRules`.

Output: `lean/target/x86_isel_rules.json`

Run: `cd lean && lake env lean --run TuffyLean/Export/Json.lean > target/x86_isel_rules.json`

JSON format per rule:

```json
{
  "name": "add",
  "pattern": {"kind": "binop", "op": "Add",
    "lhs": {"reg": "lhs", "ann": "any"},
    "rhs": {"reg": "rhs", "ann": "any"}},
  "emit": [
    {"inst": "MovRR", "size": "s64",
     "dst": {"fresh": "dst"}, "src": {"named": "lhs"}},
    {"inst": "AddRR", "size": "s64",
     "dst": {"fresh": "dst"}, "src": {"named": "rhs"}}
  ],
  "result": {"kind": "reg", "name": "dst"}
}
```

### Step 3: Rust Code Generator (`tuffy_isel_gen`)

New workspace member crate. CLI tool that reads JSON and outputs Rust source.

```
tuffy_isel_gen/
  Cargo.toml          # deps: serde, serde_json
  src/
    main.rs           # CLI: read JSON path, write Rust path
    schema.rs         # Deserialize JSON into typed structs
    codegen.rs        # Generate Rust code from rules
```

Usage: `cargo run -p tuffy_isel_gen -- lean/target/x86_isel_rules.json tuffy_target_x86/src/isel_gen.rs`

Generated `isel_gen.rs` contains:

1. Per-rule `gen_<name>()` functions that emit MInst sequences
2. A `try_select_generated()` dispatch function

Example generated output:

```rust
// @generated by tuffy_isel_gen -- DO NOT EDIT

fn gen_add(ctx: &mut super::IselCtx, vref: ValueRef,
           lhs: VReg, rhs: VReg) -> Option<()> {
    let dst = ctx.alloc.alloc();
    ctx.out.push(MInst::MovRR { size: OpSize::S64, dst, src: lhs });
    ctx.out.push(MInst::AddRR { size: OpSize::S64, dst, src: rhs });
    ctx.regs.assign(vref, dst);
    Some(())
}

pub(super) fn try_select_generated(
    ctx: &mut super::IselCtx, vref: ValueRef,
    op: &Op,
) -> Option<()> {
    match op {
        Op::Add(lhs, rhs) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            gen_add(ctx, vref, l, r)
        }
        Op::Shr(lhs, rhs) => {
            let l = ctx.ensure_in_reg(lhs.value)?;
            let r = ctx.ensure_in_reg(rhs.value)?;
            match lhs.annotation {
                Some(Annotation::Signed(_)) => gen_shr_signed(ctx, vref, l, r),
                _ => gen_shr_unsigned(ctx, vref, l, r),
            }
        }
        _ => None,
    }
}
```

### Step 4: Integration with isel.rs

Minimal changes to `tuffy_target_x86/src/isel.rs`:

1. Add `mod isel_gen;`
2. In `select_inst()`, call generated dispatch first
3. Remove migrated match arms

```rust
fn select_inst(ctx: &mut IselCtx, vref: ValueRef, op: &Op, ...) -> Option<()> {
    if isel_gen::try_select_generated(ctx, vref, op).is_some() {
        return Some(());
    }
    // Only complex ops remain here
    match op {
        Op::Param(idx) => { ... }
        Op::Const(imm) => { ... }
        ...
    }
}
```

## Affected Modules

- `lean/TuffyLean/Target/X86/` — new Lean module: DSL types and rule definitions
- `lean/TuffyLean/Export/Json.lean` — extend with isel rule serialization
- `tuffy_isel_gen/` — new Rust crate: JSON → Rust code generator
- `tuffy_target_x86/src/isel.rs` — integrate generated dispatch, remove migrated arms
- `tuffy_target_x86/src/isel_gen.rs` — generated output file

## Verification

1. `cd lean && lake build` — Lean compiles
2. Export JSON and inspect: rules match expected patterns
3. `cargo build -p tuffy_isel_gen` — generator compiles
4. Run generator, inspect output `isel_gen.rs`
5. `cargo test` — all existing tests pass (behavior unchanged)
6. `cargo clippy` — no warnings
