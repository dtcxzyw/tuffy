# References

A curated list of reference documents and resources for the tuffy project.

## Compiler Optimization

- [Future Directions for Optimizing Compilers](https://arxiv.org/abs/1809.02161) — Nuno P. Lopes, John Regehr, 2018. Discusses challenges in making optimizing compilers faster, less buggy, and more capable.

## IR Design and Semantics

- [RFC: Add a New Byte Type to LLVM IR](https://discourse.llvm.org/t/rfc-add-a-new-byte-type-to-llvm-ir/89522) — Juneyoung Lee, Pedro Lobo, Nuno Lopes, George Mitenkov. Proposes `b<N>` byte type to represent raw memory data, enabling per-byte poison tracking and paving the way for undef removal.
- [Leaving the Sea of Nodes](https://v8.dev/blog/leaving-the-sea-of-nodes) — V8 team. Post-mortem on 10 years of Sea of Nodes in TurboFan: effect chain complexity, poor cache locality, limited floating benefits for effectful operations, compilation speed issues. Replaced with CFG-based Turboshaft, halving compile time.
- [A Simple Reply](https://github.com/SeaOfNodes/Simple/blob/main/ASimpleReply.md) — Cliff Click. Rebuttal to V8's SoN criticism: argues problems stem from JS's lack of strong typing, not SoN itself. Strong typing (Java, Rust) provides ECA naturally, simplifying effect management. Worklist algorithms solve visitation order. Dead code elimination is near-free with reference counting.
- [VPlan: Vectorization Plan](https://llvm.org/docs/VectorizationPlan.html) — LLVM. Hierarchical CFG with nested SESE regions and recipe-based transformations for vectorization. Key ideas: plan-then-execute (analysis doesn't modify IR), multiple candidates with cost estimation, recipes naturally record transformation provenance. Relevant to tuffy's "analysis is also a transformation" and rewrite path tracing goals.

## Memory Model and Pointer Semantics

- [Pointers Are Complicated, or: What's in a Byte?](https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html) — Ralf Jung, 2018. Argues pointers are not integers; proposes abstract pointer model (allocation ID + offset) preserving provenance. Defines bytes as `Bits(u8) | PtrFragment(Pointer, n) | Uninit`. Directly relevant to tuffy's byte type and uninitialized memory model.
- [Pointers Are Complicated II, or: We Need Better Language Specs](https://www.ralfj.de/blog/2020/12/14/provenance.html) — Ralf Jung, 2020. Shows three individually-correct LLVM optimizations that produce wrong results when combined, due to unspecified pointer provenance. Concludes: pointers have provenance, integers do not; ptr-to-int-to-ptr roundtrips are not no-ops.
- [Pointers Are Complicated III, or: Pointer-Integer Casts Exposed](https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html) — Ralf Jung, 2022. Proposes "provenance exposure" model: ptr-to-int casts have side effects (exposing provenance), int-to-ptr casts are non-deterministic. Rust's Strict Provenance API (`ptr.addr()`, `with_addr()`) offers a cleaner alternative. Relevant to tuffy's pointer representation design.
- [Uninit](https://www.ralfj.de/blog/2019/07/14/uninit.html) — Ralf Jung, 2019. Uninitialized memory is not "random bits" but a distinct abstract state (`None`). Any operation on uninit values is UB. Validates tuffy's decision to allow uninitialized memory at the memory level while keeping values as concrete-or-poison.
- [Do We Really Need Undefined Behavior?](https://www.ralfj.de/blog/2021/11/24/ub-necessary.html) — Ralf Jung, 2021. Argues unrestricted UB is necessary for practical optimization (register allocation, constant folding). Platform-specific UB would make even basic codegen impossible. Supports tuffy's poison-based UB model as a principled middle ground.
- [Clarifying the Semantics of ptrtoint](https://discourse.llvm.org/t/clarifiying-the-semantics-of-ptrtoint/83987) — LLVM discussion. Proposes separating `ptrtoint` (full bitwise representation) from `ptrtoaddr` (address only). Highlights that compiler-level provenance and hardware provenance (CHERI) are distinct. Relevant to tuffy's pointer representation: need to decide whether ptr-to-int exposes provenance or just address.

## ABI and Calling Conventions

- [RFC: An ABI Lowering Library for LLVM](https://discourse.llvm.org/t/rfc-an-abi-lowering-library-for-llvm/84495) — nikic (Nikita Popov). Proposes a standalone LLVMABI library with its own type system dedicated to ABI lowering, extracting logic currently duplicated across frontends (Clang, Rust, etc.). Key design: independent type system capturing only ABI-relevant information, per-target calling convention implementations, ABIArgInfo results guiding IR generation. Layered to depend only on LLVM Support, with a C API for non-C++ frontends. Directly relevant to tuffy's plan for a dedicated ABI library that maps `int` parameters/returns to concrete register classes and calling conventions.

## Testing and Validation

- [RFC: Upstreaming LLVM UB-Aware Interpreter](https://discourse.llvm.org/t/rfc-upstreaming-llvm-ub-aware-interpreter/89645) — dtcxzyw. Proposes upstreaming llubi, a UB-aware LLVM IR interpreter that detects undefined behavior during execution and properly propagates poison values. Key motivation: reducing miscompilation reproducers directly on LLVM IR (minutes vs hours with C-level tools). Separate implementation from legacy ExecutionEngine because GenericValue cannot represent poison or pointer provenance. Relevant to tuffy's IR interpreter design.
- [llvm-ub-aware-interpreter (llubi)](https://github.com/dtcxzyw/llvm-ub-aware-interpreter) — dtcxzyw. Implementation of UB-aware LLVM IR interpreter. Detects guardable UBs at execution time, tracks poison propagation, integrates with llvm-reduce for test case minimization and Csmith/Rustlantis for fuzzing. Treats undef as zero (practical simplification). Does not model pointer aliasing or full provenance. Directly informs tuffy's interpreter design, though tuffy's poison-only model (no undef) and four-state bytes enable a cleaner implementation.
