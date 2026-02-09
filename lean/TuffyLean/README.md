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
│           └── Basic.lean
│
└── Export/              # Serialization and interop
    └── Json.lean        # JSON export for Lean↔Rust data exchange
```

## Key Distinction: Rewrites vs Prototyping

- **`Rewrites/`** — Production rewrite rules with formal correctness proofs. These feed into the actual compiler optimization pipeline.
- **`Prototyping/Opt/`** — Exploratory prototypes that validate whether the IR design can express common optimizations. These are never used in production; they exist to catch design issues early.
