# Feature Name: `tuffy_pipeline`

- Status: Draft
- Created: 2026-02-07
- Completed: N/A

## Summary

This RFC defines the compilation pipeline design for the tuffy compiler, focusing on three core constraints: value-level analysis encoded as IR transformations, automatic debug info preservation via origin chains, and automatic profiling info preservation with merging semantics.

## Motivation

Compiler pipelines face recurring engineering problems that erode correctness and developer productivity:

- **Phase ordering**: In LLVM, analyses like KnownBits and DemandedBits live in side tables disconnected from the IR. When a transform modifies the IR without updating these tables, analysis results become stale. Subsequent passes either use stale data (miscompilation) or must conservatively discard and recompute (lost optimization opportunities). This is the root cause of many phase ordering bugs.
- **Debug info loss**: LLVM requires each optimization pass to manually preserve debug info. In practice, many passes silently drop it. The result is poor debugging experience at higher optimization levels — a well-known pain point for all LLVM-based compilers.
- **Profiling info loss**: Profile-guided optimization data (branch weights, execution counts) suffers the same manual-maintenance problem. Transforms that restructure control flow or merge/split blocks often discard profile annotations.

Tuffy's pipeline addresses these by making preservation automatic at the infrastructure level, rather than relying on per-pass discipline.

## Guide-level explanation

### Pass classification

Tuffy distinguishes two categories of analysis:

**Structural analyses** (side table, on-demand):
- Dominator tree
- Loop tree
- Post-dominator tree

These are cheaply recomputable from the CFG and do not carry semantic information that could be irreversibly lost by transforms. They live in traditional side tables and are invalidated/recomputed as needed.

**Value-level analyses** (encoded in IR, transform passes):
- KnownBits — which bits of a value are provably 0 or 1
- DemandedBits — which bits of a value are actually needed at each use site
- MemSSA refinement — splitting memory version chains as alias analysis improves

These carry semantic facts about values that, if lost, cannot be recovered without re-deriving from first principles. In tuffy, these are **transform passes** — they read the IR, compute results, and write those results back into the IR (on use-edge annotations or memory tokens). They are scheduled in the pipeline alongside optimization passes, not invoked as side analyses.

This follows the "analysis is also a transformation" principle: there is no distinction between "analysis pass" and "optimization pass" for value-level information. Both modify the IR.

### Origin chain

Every instruction in the IR carries an **origin** — a reference to the instruction(s) it was derived from. When a transform creates a new instruction, the builder API **requires** specifying an origin. This is a mandatory parameter, not optional metadata.

```
// Builder API enforces origin
let new_add = builder.build_add(lhs, rhs, origin: old_mul.origin());
```

The origin chain serves two purposes:

1. **Debug info derivation**: Debug information (source locations, variable mappings) is not stored on every instruction. Instead, it is **computed** from the origin chain and current IR values. As long as the chain is unbroken, debug info can be derived for any instruction by tracing back to its origin.

2. **Profiling info association**: Profiling data (execution counts, branch weights) is associated with instructions via origin. When transforms merge or split instructions, profile data is **merged** accordingly — this is valid because profile data ultimately serves code generation decisions, not source-level tracing.

### Origin in practice

Most transforms have a natural origin for new instructions:

| Transform | New instruction | Origin source |
|-----------|----------------|---------------|
| Strength reduction | `shl %x, 1` replacing `mul %x, 2` | The original `mul` |
| Loop canonicalization | Preheader branch | Latch branch |
| Instruction combining | `add %a, %c` from `add(add(%a, %b), %c)` | Both original `add` instructions |
| Dead code elimination | (no new instructions) | N/A |
| Loop unrolling | Duplicated loop body | Original loop body instructions |

When multiple origins contribute, the origin is a set. The debug info derivation picks the most specific source location from the set.

### Pipeline structure

A tuffy compilation pipeline is a sequence of passes:

```
MIR translation
  → [value-level analysis: initial KnownBits/DemandedBits]
  → [optimization passes interleaved with value-level analysis updates]
  → legalization
  → instruction selection
  → register allocation
  → machine code emission
```

Value-level analysis passes can be scheduled at any point. Since they are transforms (they modify the IR), the pass manager treats them identically to optimization passes.

## Reference-level explanation

### Origin representation

```
struct Origin {
    sources: SmallVec<[InstructionId; 1]>,
}
```

Most instructions have a single origin (1-element SmallVec). Merged instructions carry multiple origins. The `SmallVec<[_; 1]>` avoids heap allocation in the common case.

### Debug info derivation

Debug info is stored in a separate table indexed by `InstructionId`:

```
struct DebugInfoTable {
    /// Maps original (pre-optimization) instruction IDs to source locations
    source_locations: HashMap<InstructionId, SourceLocation>,
    /// Maps original instruction IDs to variable bindings
    variable_bindings: HashMap<InstructionId, Vec<VariableBinding>>,
}
```

To query the source location of a current instruction:
1. Follow its origin chain to find original instruction IDs
2. Look up those IDs in the debug info table
3. If multiple origins, pick the most specific (innermost) source location

This design means optimization passes never touch debug info directly. The table is write-once (populated during MIR translation) and read-only thereafter.

### Profiling info

Profile data is stored similarly:

```
struct ProfileData {
    /// Execution counts per original basic block
    block_counts: HashMap<BasicBlockId, u64>,
    /// Branch weights per original terminator
    branch_weights: HashMap<InstructionId, Vec<(BasicBlockId, u32)>>,
}
```

When a transform merges blocks or restructures control flow, the profile data for new blocks is computed by summing or averaging the profile data of their origins. This is done automatically by the infrastructure when blocks are created via the builder API.

### Builder API enforcement

The instruction builder requires origin at construction:

```
impl Builder {
    fn build_add(&mut self, lhs: Value, rhs: Value, origin: Origin) -> Value;
    fn build_load(&mut self, ty: ByteType, ptr: Value, mem: MemToken, origin: Origin) -> Value;
    // ... all build methods require origin
}
```

There is no way to create an instruction without specifying an origin. This is a compile-time guarantee, not a runtime check.

### Value-level analysis as transform

A KnownBits analysis pass operates as:

```
fn run_known_bits_analysis(func: &mut Function) {
    for inst in func.instructions_reverse_postorder() {
        let known = compute_known_bits(inst, func);
        for use_edge in func.uses_of(inst) {
            use_edge.update_known_bits(known);  // modifies IR in-place
        }
    }
}
```

This is registered in the pass manager as a regular transform pass. The pass manager does not distinguish it from an optimization pass.

## Drawbacks

- **Origin overhead**: Every instruction carries an origin reference. For single-origin instructions this is one `InstructionId` (typically 4 bytes), but merged instructions allocate. In practice, most instructions have single origins, so the overhead is modest.
- **Debug info derivation cost**: Computing debug info on demand (rather than storing it per-instruction) adds cost at debug info emission time. This is acceptable because debug info emission happens once at the end of compilation.
- **Profile merging heuristics**: Automatically merging profile data during transforms may produce inaccurate estimates. However, this is no worse than the status quo (where profile data is often silently dropped), and the merged data is still useful for code generation heuristics.

## Rationale and alternatives

### Why encode value-level analysis in IR?

The alternative is LLVM's approach: side-table analyses invalidated by transforms. This creates phase ordering problems — the order in which analyses and transforms run affects the final result. By encoding analysis results in the IR, every pass sees the most recent information, and transforms that don't affect a particular annotation leave it intact.

### Why origin chains instead of per-instruction debug info?

**Alternative: LLVM's DebugLoc approach.** Each instruction carries a `DebugLoc` that passes must manually preserve. Rejected because it relies on per-pass discipline and fails in practice — many LLVM passes silently drop debug locations.

**Alternative: Debug info as IR instructions (LLVM's dbg.value).** Intrinsic calls represent debug info in the IR. Rejected because these pseudo-instructions complicate every transform (must be moved, cloned, or deleted alongside real instructions) and are still frequently mishandled.

Origin chains move the burden from pass authors to the infrastructure. Pass authors specify "where did this instruction come from" (which they always know), and the infrastructure handles debug/profile info automatically.

### Why allow profile merging?

Profile data is inherently approximate (sampled, potentially stale). Merging during transforms preserves the relative hotness information that matters for code generation, even if absolute counts shift. The alternative — dropping profile data when transforms can't preserve it exactly — is strictly worse.

## Prior art

- **LLVM DebugLoc**: Per-instruction debug location, manually maintained by passes. Known to be fragile; significant ongoing effort to improve preservation.
- **LLVM dbg.value/dbg.declare**: Debug info as intrinsic calls in IR. Adds complexity to every transform.
- **GCC tree-ssa**: Similar side-table analysis approach with phase ordering issues.
- **MLIR**: Operation-level location tracking with fusion semantics for merged operations. Closer to tuffy's origin chain concept.

## Unresolved questions

- **Origin chain compression**: Long optimization pipelines may create deep origin chains. Should origins be transitively compressed (point directly to the original MIR instruction) or kept as a full chain?
- **Pass ordering strategy**: How should the pass manager decide when to schedule value-level analysis passes? Fixed schedule, or demand-driven?
- **Profile data merging policy**: What specific merging rules apply for different transform types (block merging, loop unrolling, function inlining)?

## Future possibilities

- **Differential debugging**: Origin chains enable automatic bisection — given a miscompiled instruction, trace its origin chain to identify which transform introduced the bug.
- **Optimization reports**: Origin chains combined with rewrite path traces provide detailed optimization reports showing what happened to each source-level operation.
- **Selective optimization**: Profile data preservation enables fine-grained PGO where hot and cold paths receive different optimization strategies throughout the pipeline.
