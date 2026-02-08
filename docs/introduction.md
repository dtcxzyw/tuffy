# Introduction

Tuffy is an experimental optimizing compiler written in Rust, developed with LLM assistance.

> **Note:** This project is currently in an experimental stage.

## Key Design Ideas

- **Infinite precision integers** — The IR uses a single `int` type with no fixed bitwidth. Arithmetic operates on mathematical integers; signedness and minimum required bits are derived at use sites. This eliminates zext/sext/trunc noise and lets optimization passes focus on mathematical equivalence.
- **Analysis is also a transformation** — Static analyses are expressed as transformations on the IR itself, unifying analysis and optimization and reducing phase ordering problems.
- **Declarative, verified optimizations** — Transforms are declarative rewrite rules with machine-checked correctness proofs in Lean 4 against the formal IR semantics. A codegen generator produces Rust implementation from verified rules, minimizing the trusted code base.
- **Formal-first** — Correctness of optimization passes is backed by formal verification from the start, not bolted on after the fact.
- **Hardware-friendly IR** — IR representations designed to be cache-friendly and suitable for modern hardware, reducing pointer chasing and improving data locality during compilation.
- **Policy-mechanism separation** — Optimization strategies are decoupled from the compiler engine. Users can specify or pin a particular optimization policy to prevent performance regressions when upgrading the compiler.

## Documentation Overview

- **[IR Language Reference](spec.md)** — The textual IR format, type system, and instruction set.
- **[Initial Design](initial.md)** — Early design discussions and architectural decisions.
- **[References](references.md)** — Curated list of reference documents and resources.
- **[RFCs](RFCs/202602/ir-design.md)** — Design proposals for major features.
- **[Development Tasks](tasks/202602/init.md)** — Task tracking for current milestones.
