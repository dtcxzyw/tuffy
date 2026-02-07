# References

A curated list of reference documents and resources for the tuffy project.

## Compiler Optimization

- [Future Directions for Optimizing Compilers](https://arxiv.org/abs/1809.02161) — Nuno P. Lopes, John Regehr, 2018. Discusses challenges in making optimizing compilers faster, less buggy, and more capable.

## IR Design and Semantics

- [RFC: Add a New Byte Type to LLVM IR](https://discourse.llvm.org/t/rfc-add-a-new-byte-type-to-llvm-ir/89522) — Juneyoung Lee, Pedro Lobo, Nuno Lopes, George Mitenkov. Proposes `b<N>` byte type to represent raw memory data, enabling per-byte poison tracking and paving the way for undef removal.
- [Leaving the Sea of Nodes](https://v8.dev/blog/leaving-the-sea-of-nodes) — V8 team. Post-mortem on 10 years of Sea of Nodes in TurboFan: effect chain complexity, poor cache locality, limited floating benefits for effectful operations, compilation speed issues. Replaced with CFG-based Turboshaft, halving compile time.
- [A Simple Reply](https://github.com/SeaOfNodes/Simple/blob/main/ASimpleReply.md) — Cliff Click. Rebuttal to V8's SoN criticism: argues problems stem from JS's lack of strong typing, not SoN itself. Strong typing (Java, Rust) provides ECA naturally, simplifying effect management. Worklist algorithms solve visitation order. Dead code elimination is near-free with reference counting.
