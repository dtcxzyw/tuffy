# tuffy
An experimental optimizing compiler written by LLM

> **Note:** This project is currently in an experimental stage. External pull requests are not accepted at this time.

## Experiments

Tuffy explores several unconventional compiler design ideas:

- **Infinite precision integers** (idea by [inclyc](https://github.com/inclyc)) — The IR uses a single `int` type with no fixed bitwidth. Arithmetic operates on mathematical integers; signedness and minimum required bits are derived at use sites. This eliminates zext/sext/trunc noise and lets optimization passes focus on mathematical equivalence.
- **Analysis is also a transformation** (idea by [inclyc](https://github.com/inclyc)) — Static analyses are not separate passes that feed information to optimizations. Instead, analyses are expressed as transformations on the IR itself, unifying the two and reducing phase ordering problems.
- **Formal-first** — Correctness of optimization passes is backed by formal verification from the start, not bolted on after the fact. The IR semantics are designed to be amenable to automated reasoning.
- **Hardware-friendly IR** — Explore IR representations that are more cache-friendly and suitable for modern hardware, reducing pointer chasing and improving data locality during compilation.
- **Policy-mechanism separation** — Optimization strategies are decoupled from the compiler engine. Users can specify or pin a particular optimization policy (e.g., lock to a versioned strategy) to prevent performance regressions when upgrading the compiler.
