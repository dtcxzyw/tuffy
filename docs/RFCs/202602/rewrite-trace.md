# Feature Name: `tuffy_rewrite_trace`

- Status: Draft
- Created: 2026-02-07
- Completed: N/A

## Summary

This RFC defines the rewrite path tracing infrastructure for the tuffy compiler. Every transform emits a machine-readable trace entry recording the rewrite rule, local context, before/after IR fragments, and decision rationale. A replay tool can re-execute the optimization sequence from a trace, enabling regression bisection, policy locking, and transform auditing.

## Motivation

When a compiler optimization causes a performance regression or miscompilation, diagnosing the root cause is notoriously difficult:

- **Black-box pipeline**: the optimization pipeline is opaque — developers see input IR and output IR, but not the chain of decisions that produced the result.
- **Non-reproducible decisions**: heuristic decisions (cost model thresholds, unrolling factors) depend on analysis state that is not recorded. Changing the compiler version may silently change decisions.
- **Manual bisection**: finding which transform caused a regression requires manually enabling/disabling passes, a tedious and error-prone process.

Rewrite path tracing makes the optimization pipeline fully transparent and reproducible. Every decision is recorded, and the entire optimization sequence can be replayed mechanically.

## Guide-level explanation

### Trace entries

Each time a transform fires, it emits a **trace entry** containing:

1. **Rule identity**: which rewrite rule fired, and where in the pipeline
2. **Local context**: the preconditions that enabled the transform (known bits, ranges, constants)
3. **Before/after IR**: the local IR fragment before and after the rewrite
4. **Decision rationale**: for equivalence transforms, the proof reference; for heuristic transforms, the cost model inputs and outputs

### Trace format

Traces are structured, machine-readable data. Example (equivalence transform):

```json
{
  "seq": 42,
  "rule": "strength_reduce_mul_pow2",
  "stage": "early_simplification",
  "iteration": 2,
  "function": "@compute",
  "region": "loop.0",
  "context": {
    "%C": {"kind": "const", "value": 8, "properties": ["is_power_of_2"]},
    "%x": {"kind": "known_bits", "known_zeros": "0xFFFFFFFF00000000"}
  },
  "before": {"instructions": ["%r = mul %x, %C"]},
  "after": {"instructions": ["%r = shl %x, 3"]},
  "decision": {
    "kind": "equivalence",
    "proof_ref": "Tuffy.Rewrites.StrengthReduce.mul_pow2"
  }
}
```

Example (heuristic transform):

```json
{
  "seq": 87,
  "rule": "loop_unroll",
  "stage": "loop_optimization",
  "function": "@process",
  "region": "loop.2",
  "context": {
    "trip_count": 4,
    "body_instruction_count": 12,
    "body_has_calls": false
  },
  "before": {"instructions": ["region.loop { ... }"]},
  "after": {"instructions": ["region.sequence { ... }"]},
  "decision": {
    "kind": "cost_model",
    "before_cost": {"estimated_cycles": 48, "code_size": 24},
    "after_cost": {"estimated_cycles": 16, "code_size": 96},
    "threshold": "unroll if speedup > 2x",
    "speedup": 3.0
  }
}
```

### Replay

A replay tool reads a trace and re-executes the same transforms on a given IR:

```
tuffy-replay --trace=opt_trace.json --input=before.tir --output=after.tir
```

At each step, the replay tool:
1. Matches the pattern from the trace entry against the current IR
2. Verifies the preconditions still hold
3. Applies the rewrite
4. If a precondition fails or the pattern doesn't match, reports a **divergence**

Divergences indicate that the IR or compiler has changed in a way that invalidates the recorded optimization sequence.

### Use cases

| Use case | How trace helps |
|----------|----------------|
| **Regression bisect** | Replay trace step by step, compare decisions with new compiler version, find first divergence |
| **Policy locking** | Save trace as a "policy file", replay forces the same decisions on recompilation |
| **Transform audit** | Review each trace entry to verify optimization rationale |
| **Optimization report** | Generate human-readable report from trace showing what happened to each hot function |
| **Debugging** | When a miscompilation is found, trace pinpoints which transform introduced the bug |

### Overhead control

Tracing is **optional**, controlled by compiler flag:

- `--emit-trace=none` (default): no tracing, zero overhead
- `--emit-trace=decisions`: record rule + decision only (lightweight)
- `--emit-trace=full`: record rule + context + before/after IR + decision (detailed)

When disabled, trace emission code is compiled out via conditional compilation, ensuring zero runtime cost.

### Relationship to other features

- **Origin chain**: tracks instruction-level lineage (where did this instruction come from). Trace tracks transform-level decisions (why was this rewrite applied). Complementary, not overlapping.
- **Policy-mechanism separation**: trace is the execution record of a policy. Replaying a trace = enforcing a policy. Locking to a versioned policy = saving and replaying a trace.
- **Transform equivalence declaration**: trace entries reference the declaration (equivalence or refinement) and, for verified rules, the Lean 4 proof.

## Reference-level explanation

### Trace data structures

```
struct Trace {
    metadata: TraceMetadata,
    entries: Vec<TraceEntry>,
}

struct TraceMetadata {
    compiler_version: String,
    pipeline_config: PipelineConfig,
    target_triple: String,
    timestamp: String,
}

struct TraceEntry {
    seq: u64,
    rule: String,
    stage: String,
    iteration: u32,
    function: String,
    region: Option<String>,
    context: Vec<ContextFact>,
    before: IrFragment,
    after: IrFragment,
    decision: Decision,
}

enum ContextFact {
    Const { name: String, value: BigInt, properties: Vec<String> },
    KnownBits { name: String, known_zeros: BitSet, known_ones: BitSet },
    Range { name: String, min: BigInt, max: BigInt },
    AssertSext { name: String, width: u32 },
    AssertZext { name: String, width: u32 },
}

struct IrFragment {
    instructions: Vec<String>,
}

enum Decision {
    Equivalence {
        proof_ref: Option<String>,
    },
    CostModel {
        before_cost: CostEstimate,
        after_cost: CostEstimate,
        threshold: String,
    },
}

struct CostEstimate {
    estimated_cycles: Option<u64>,
    code_size: Option<u64>,
    custom: HashMap<String, String>,
}
```

### Trace emission

The pass infrastructure provides a trace emitter that transforms call:

```
impl TraceEmitter {
    fn emit(&mut self, entry: TraceEntry);
    fn is_enabled(&self) -> bool;
}
```

In declarative rewrite rules, trace emission is automatic — the codegen generator produces trace emission code alongside the transform code. The context is extracted from the pattern match bindings, and the decision is derived from the rule's `TransformKind`.

For the lightweight `--emit-trace=decisions` mode, `before`/`after` IR fragments and detailed context are omitted.

### Replay engine

```
struct ReplayEngine {
    trace: Trace,
    current_step: usize,
}

enum ReplayResult {
    Success,
    Divergence {
        step: u64,
        expected_rule: String,
        reason: DivergenceReason,
    },
}

enum DivergenceReason {
    PatternNotFound,
    PreconditionFailed { fact: String, expected: String, actual: String },
    DifferentDecision { expected: Decision, actual: Decision },
}
```

The replay engine processes trace entries sequentially. At each step, it attempts to apply the recorded transform. If the pattern matches and preconditions hold, the transform is applied. Otherwise, a divergence is reported with diagnostic information.

### Serialization

Traces are serialized as JSON for interoperability. For large traces, streaming JSON (one entry per line, JSONL format) avoids loading the entire trace into memory.

```
tuffy --emit-trace=full -o output program.tir > trace.jsonl
```

## Drawbacks

- **Trace size**: full traces with before/after IR fragments can be large for complex programs. The `decisions` mode mitigates this.
- **Replay brittleness**: replaying a trace on a different compiler version may diverge early if IR normalization changes, even if the final result is equivalent.
- **Serialization cost**: even with conditional compilation, the trace data structures add code complexity.

## Rationale and alternatives

### Why machine-readable structured traces?

**Alternative: human-readable logs (like LLVM's -pass-remarks).** Rejected because logs cannot be replayed. They are useful for human inspection but do not enable mechanical regression bisection or policy locking.

**Alternative: IR snapshots at each stage.** Recording full IR after each pass is expensive and doesn't capture the decision rationale. Traces are more compact and more informative.

### Why JSON/JSONL?

Widely supported, human-inspectable, easy to process with standard tools. Binary formats would be more compact but harder to debug and less interoperable.

### Why optional with zero overhead when disabled?

Tracing is a development and debugging tool. Production builds should not pay any cost for it. Conditional compilation ensures this.

## Prior art

- **LLVM -pass-remarks**: human-readable optimization remarks. Useful but not machine-replayable.
- **LLVM opt-bisect-limit**: binary search for which pass causes a bug. Coarser than trace-based bisection (pass-level vs transform-level).
- **GCC -fdump-tree-***: dumps IR at various stages. Snapshots, not decision traces.
- **Alive2**: extracts local function-to-function rewrites for verification. Inspires tuffy's local context extraction in trace entries.

## Unresolved questions

- **Trace stability**: how to handle trace replay across compiler versions when IR normalization changes? Should traces include a format version for compatibility?
- **Partial replay**: should the replay tool support replaying only a subset of trace entries (e.g., only transforms in a specific function)?
- **Trace diffing**: should there be a tool to diff two traces (e.g., from two compiler versions) and highlight decision changes?

## Future possibilities

- **Trace-guided optimization**: use traces from previous compilations to warm-start the optimizer, skipping exploration of decisions already known to be good.
- **Trace visualization**: graphical tool showing the optimization pipeline as a sequence of local rewrites, with drill-down into context and decisions.
- **Community trace sharing**: share traces for known-good optimization sequences on specific workloads, enabling reproducible performance.
