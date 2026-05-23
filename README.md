# tuffy
[![CI](https://github.com/dtcxzyw/tuffy/actions/workflows/ci.yml/badge.svg)](https://github.com/dtcxzyw/tuffy/actions/workflows/ci.yml)

An experimental optimizing compiler written by LLM

> **Status (2026-05-24):** I have decided to pause the development of this project until sufficiently powerful and affordable models become available. Although the flagship models from various vendors have initially demonstrated their impressive capabilities in this project, I believe now is still not the best time to continue.
>
> Over the past few months of development, I found that the models consistently opt for the simplest solutions, or forcibly apply their LLVM knowledge onto Tuffy IR. This forced me to adjust Tuffy IR's design as a compromise.
>
> From my perspective, it is not only ruining my ideas but also burning through my wallet. I feel this state is somewhat affecting my physical and mental well-being, prompting me to pause exploration in order to maintain my active participation in the LLVM community.
>
> I firmly believe this is not an issue with how I interact with LLMs — I have used LLMs to develop small services to aid LLVM development, and I have also built several production-ready programs with tens of millions of end users entirely using LLMs at my employer.
>
> The projects I developed at my employer are not as complex as tuffy, but I needed to spend roughly $1,000/day on token consumption. Based on this estimate, the token consumption required to develop tuffy is clearly beyond what I can personally afford.

> **Note:** This project is currently in an experimental stage. External pull requests are not accepted at this time.

## Experiments

Tuffy explores several unconventional compiler design ideas:

- **Infinite precision integers** (idea by [inclyc](https://github.com/inclyc)) — The IR uses a single `int` type with no fixed bitwidth. Arithmetic operates on mathematical integers; signedness and minimum required bits are derived at use sites. This eliminates zext/sext/trunc noise and lets optimization passes focus on mathematical equivalence.
- **Analysis is also a transformation** (idea by [inclyc](https://github.com/inclyc)) — Static analyses are not separate passes that feed information to optimizations. Instead, analyses are expressed as transformations on the IR itself, unifying the two and reducing phase ordering problems.
- **Declarative, verified optimizations** — Transforms are declarative rewrite rules, not hand-written IR manipulation. Every rule has a machine-checked correctness proof in Lean 4 against the formal IR semantics. A codegen generator produces Rust implementation from verified rules, minimizing the trusted code base.
- **Formal-first** — Correctness of optimization passes is backed by formal verification from the start, not bolted on after the fact. The IR semantics are designed to be amenable to automated reasoning.
- **Hardware-friendly IR** — Explore IR representations that are more cache-friendly and suitable for modern hardware, reducing pointer chasing and improving data locality during compilation.
- **Policy-mechanism separation** — Optimization strategies are decoupled from the compiler engine. Users can specify or pin a particular optimization policy (e.g., lock to a versioned strategy) to prevent performance regressions when upgrading the compiler.

## Milestones

- **2026-02-08** — Project started
- **2026-02-09** — Successfully compiled and ran "Hello, world!" via `rustc -Z codegen-backend`
- **2026-04-02** — Compiled and tested [bitflags](https://github.com/bitflags/bitflags) (with all dependencies) using the Tuffy backend — all tests passing
- **2026-04-05** — Passed all Rust standard library tests (coretests, alloctests, libtest) compiled with the Tuffy backend
