# TuffyLean

Lean 4 formal definitions for the tuffy compiler IR. This is the **source of truth** — the Rust implementation and spec must conform to these definitions.

## Directory Structure

```
TuffyLean/
├── IR/                  # Core IR definitions (source of truth)
│   ├── Types.lean       # Type system, values, abstract bytes, annotations
│   └── Semantics.lean   # Operational semantics of all instructions
│
├── Rewrites/            # Production rewrite rules (used in optimization pipeline)
│   └── Basic.lean       # Basic algebraic rewrites with correctness proofs
│
├── Prototyping/         # Design validation (NOT part of production pipeline)
│   └── Opt/             # Prototype optimizations to validate IR expressiveness
│       ├── Arith/       # Arithmetic optimization prototypes
│       │   └── Basic.lean
│       └── Mem/         # Memory optimization prototypes
│           ├── Basic.lean
│           └── Mem2Reg.lean
│
└── Export/              # Serialization and interop
    └── Json.lean        # Target-agnostic JSON export entrypoint
```

## Isel Export Conventions

- `TuffyLean/Export/Json.lean` must remain target-agnostic and only dispatch to target-local exporters.
- All target-specific isel JSON encoding (rules, metadata maps, imports, instruction field encoding) must live under `TuffyLean/Target/<target>/Export.lean`.
- Use explicit target selection when exporting isel JSON:

```bash
lake env lean --run TuffyLean/Export/Json.lean --target x86
```

- Do not rely on implicit defaults in automation scripts.

## Peephole Export Conventions

- Production peephole rules live under `TuffyLean/Rewrites/`.
- `TuffyLean/Export/Json.lean` also exports the peephole rule set:

```bash
lake env lean --run TuffyLean/Export/Json.lean --kind peephole
```

- The exported JSON is the interface consumed by `tuffy_opt`; do not hand-maintain Rust copies of production rules.
- Context-sensitive at-use analysis metadata in `TuffyLean/Rewrites/AtUse.lean` is exported as part of the same `peephole` JSON artifact and consumed by the unified peephole generator/runtime in `tuffy_opt`.

## Optimizer Manifest Export

- `TuffyLean/Export/Json.lean` also exports the non-inline `tuffy_opt` cleanup manifest:

```bash
lake env lean --run TuffyLean/Export/Json.lean --kind opt_pass_manifest
```

- This manifest is the Lean-owned source for cleanup pass ordering and family metadata consumed by `tuffy_opt`.

## Key Distinction: Rewrites vs Prototyping

- **`Rewrites/`** — Production rewrite rules with formal correctness proofs. These feed into the actual compiler optimization pipeline.
- **`Prototyping/Opt/`** — Exploratory prototypes that validate whether the IR design can express common optimizations. These are never used in production; they exist to catch design issues early.
