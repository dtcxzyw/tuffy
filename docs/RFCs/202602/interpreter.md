# Feature Name: `tuffy_interpreter`

- Status: Draft
- Created: 2026-02-07
- Completed: N/A

## Summary

This RFC defines the design of the tuffy IR interpreter, a miri-like execution engine that directly interprets tuffy IR with full UB detection, poison tracking, pointer provenance enforcement, and four-state byte memory semantics. The interpreter serves as the primary testing and validation tool for transform correctness.

## Motivation

Compiler testing traditionally relies on end-to-end execution: compile a program, run it, check the output. This approach has two fundamental limitations:

- **Coarse granularity**: end-to-end tests only detect bugs that manifest as observable output differences. Silent UB, provenance violations, and poison mishandling may not produce wrong outputs on any particular test input.
- **Slow reduction**: when a miscompilation is found, reducing the reproducer from a full program to a minimal IR fragment requires expensive tools (creduce, llvm-reduce) operating at the source or LLVM IR level.

The LLVM UB-aware interpreter (llubi) demonstrated that an IR-level interpreter with UB detection can reduce miscompilation reproducers from hours to minutes. Tuffy's IR design — poison-only UB model, four-state bytes, abstract pointer provenance — is inherently more amenable to precise interpretation than LLVM IR.

## Guide-level explanation

### Core capabilities

The tuffy interpreter executes IR functions directly, maintaining a concrete machine state:

- **Infinite precision integers**: implemented via arbitrary-precision integer library (e.g., `num-bigint`). No overflow, no wrapping — arithmetic is mathematical.
- **Four-state byte memory**: each byte in the interpreter's memory is one of `Bits(u8)`, `PtrFragment(AllocId, usize)`, `Uninit`, or `Poison`.
- **Pointer provenance tracking**: every pointer carries an `(AllocId, offset)` pair. Out-of-bounds access, use-after-free, and provenance violations are detected.
- **Poison propagation**: poison values propagate through computations. Using poison as a branch condition, storing poison to observable memory, or violating an assert node is flagged as UB.
- **Assert node enforcement**: `assertsext(v, N)` and `assertzext(v, N)` are checked at runtime; violations produce poison (and are reported as UB).

### Execution modes

The interpreter supports multiple execution modes:

| Mode | Purpose |
|------|---------|
| **Normal** | Execute and produce output, report UB as warnings |
| **Strict** | Abort on first UB detection |
| **Differential** | Execute two IR versions (pre/post optimization), compare results |
| **Reduce** | Deterministic execution for use with IR reducer tools |

### Differential testing

The primary use case for transform validation:

```
tuffy-interp --differential --before=pre_opt.tir --after=post_opt.tir --input=test_case
```

The interpreter runs both IR versions on the same input and reports any behavioral divergence. Combined with a fuzzer, this provides high-confidence testing of individual transforms.

### UB detection

The interpreter detects and reports:

| UB category | Detection mechanism |
|-------------|-------------------|
| Assert node violation | Runtime range check on `assertsext`/`assertzext` |
| Uninit read | Memory byte is `Uninit` at load time |
| Poison observation | Poison used as branch condition or stored to observable memory |
| Out-of-bounds access | Pointer offset exceeds allocation bounds |
| Use-after-free | Access to freed allocation |
| Provenance violation | Pointer used with wrong `AllocId` |
| Division by zero | Divisor is zero |
| Null dereference | Pointer with null address |

### Integration with fuzzing

The interpreter integrates with fuzzing tools:

- **Rustlantis**: generates random Rust programs, compiles with tuffy, runs through interpreter
- **IR-level fuzzer**: generates random tuffy IR fragments, runs through optimization pipeline, differential-tests with interpreter
- **Reducer**: when a bug is found, an IR reducer (similar to llvm-reduce) minimizes the reproducer using the interpreter as the oracle

## Reference-level explanation

### Value representation

```
enum Value {
    Int(BigInt),
    Bytes(Vec<AbstractByte>),
    Ptr(Pointer),
    Float(f32),
    Double(f64),
    Vec(Vec<Value>),
    Poison,
}

enum AbstractByte {
    Bits(u8),
    PtrFragment(AllocId, usize),
    Uninit,
    Poison,
}

struct Pointer {
    alloc_id: AllocId,
    offset: usize,
    address_space: u32,
}
```

### Memory model

```
struct Memory {
    allocations: HashMap<AllocId, Allocation>,
    next_alloc_id: AllocId,
}

struct Allocation {
    bytes: Vec<AbstractByte>,
    size: usize,
    alive: bool,
}

impl Memory {
    fn alloc(&mut self, size: usize) -> Pointer;
    fn free(&mut self, ptr: Pointer) -> Result<(), UBError>;
    fn load(&self, ptr: Pointer, size: usize) -> Result<Vec<AbstractByte>, UBError>;
    fn store(&mut self, ptr: Pointer, bytes: Vec<AbstractByte>) -> Result<(), UBError>;
}
```

Every memory operation checks:
1. `ptr.alloc_id` refers to a live allocation
2. `ptr.offset + size <= allocation.size`
3. Provenance matches (the pointer was derived from this allocation)

### Instruction execution

Each instruction maps directly to a Rust function:

```
fn exec_add(a: &Value, b: &Value) -> Value {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Value::Int(x + y),
        (Value::Poison, _) | (_, Value::Poison) => Value::Poison,
        _ => panic!("type error"),
    }
}

fn exec_assertsext(v: &Value, n: u32) -> Value {
    match v {
        Value::Int(x) => {
            let min = -(BigInt::one() << (n - 1));
            let max = (BigInt::one() << (n - 1)) - 1;
            if *x >= min && *x <= max {
                Value::Int(x.clone())
            } else {
                Value::Poison  // UB: report to user
            }
        }
        Value::Poison => Value::Poison,
        _ => panic!("type error"),
    }
}
```

### Bytecast semantics

`bytecast` between `int` and `b<N>` follows the IR semantics:

- `int → b<N>`: extract the low N bits of the integer as bytes. If the integer is poison, all bytes are `AbstractByte::Poison`.
- `b<N> → int`: if any byte is `Uninit` or `Poison`, the result is `Value::Poison`. If any byte is `PtrFragment`, the result is `Value::Poison` (pointer-to-integer cast must use `ptrtoint`). Otherwise, assemble bytes into an integer.

### Hierarchical CFG execution

The interpreter walks the hierarchical CFG:

- **Region.Loop**: execute the loop body repeatedly until the exit branch is taken
- **Region.Branch**: evaluate the condition, execute the corresponding sub-region
- **Region.Sequence**: execute sub-regions in order
- **BasicBlock**: execute instructions sequentially, then the terminator

### MemSSA handling

The interpreter ignores MemSSA tokens — they are compile-time analysis artifacts. The interpreter uses its own concrete memory state for all load/store operations.

## Drawbacks

- **Performance**: arbitrary-precision integers and per-byte tracking are slower than native execution. The interpreter is not suitable for running large programs at scale.
- **Incomplete semantics**: some IR features (atomics, concurrency) are difficult to interpret faithfully. Single-threaded sequential execution is a simplification.
- **Maintenance burden**: the interpreter must be kept in sync with IR semantics changes. Every new instruction or semantic change requires interpreter updates.

## Rationale and alternatives

### Why a custom interpreter instead of lowering to LLVM and using lli?

Lowering to LLVM IR loses tuffy-specific semantics (infinite precision integers, four-state bytes, provenance). The whole point of the interpreter is to validate tuffy IR semantics directly, not after translation.

### Why arbitrary-precision integers in the interpreter?

The IR defines `int` as infinite precision. The interpreter must faithfully implement this — using fixed-width integers would mask overflow bugs that the IR semantics are designed to prevent.

### Why not use Miri directly?

Miri interprets Rust MIR, not tuffy IR. The tuffy interpreter operates on tuffy IR after optimization, catching bugs introduced by transforms. Miri and the tuffy interpreter serve complementary roles: Miri validates Rust semantics, the tuffy interpreter validates tuffy IR semantics.

## Prior art

- **Miri**: Rust MIR interpreter with UB detection, pointer provenance tracking, and abstract memory model. Primary inspiration for tuffy's interpreter design.
- **llubi (LLVM UB-aware interpreter)**: LLVM IR interpreter with poison tracking and UB detection. Demonstrated the value of IR-level interpretation for miscompilation debugging. Limited by LLVM's undef/poison duality and lack of provenance tracking.
- **lli (LLVM interpreter)**: basic LLVM IR interpreter without UB awareness. Insufficient for correctness validation.
- **KLEE**: symbolic execution engine for LLVM IR. More powerful but much slower; tuffy's interpreter focuses on concrete execution for speed.

## Unresolved questions

- **Atomic semantics**: how should the interpreter handle atomic operations? Sequential consistency by default, or model relaxed memory?
- **External function calls**: how to handle calls to external functions (libc, system calls)? Stub library, or FFI to native implementations?
- **Vector operations**: should the interpreter support scalable vectors, or only fixed-width vectors with a concrete vscale?
- **Performance optimization**: are there opportunities to fast-path common cases (e.g., when all bytes are `Bits`, skip per-byte tracking)?

## Future possibilities

- **Symbolic execution**: extend the interpreter to support symbolic values, enabling exhaustive exploration of execution paths for bounded verification.
- **Interactive debugging**: step-through execution with inspection of IR values, memory state, and provenance at each instruction.
- **Coverage-guided fuzzing**: instrument the interpreter to report coverage, guiding the fuzzer toward unexplored paths.
- **Regression test generation**: automatically generate minimal test cases from fuzzer-discovered bugs, adding them to the test suite.
