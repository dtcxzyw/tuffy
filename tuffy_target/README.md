# tuffy_target

Target abstraction layer for backend code generation.

## Design

Defines the traits and shared data structures that all target backends must implement. Separates target-independent logic (instruction selection helpers, relocation types) from target-specific implementations.

## Modules

### `backend.rs` — Backend Trait

The `Backend` trait is the main interface each target implements:

- `compile_function` — compile a single IR function to machine code.
- `emit_object` — emit compiled functions and static data as an object file.
- `generate_allocator_stubs` — generate allocator forwarding stubs (e.g., `__rust_alloc` → `__rdl_alloc`).
- `generate_entry_point` — generate the C `main` entry point and `lang_start`.

Backends are responsible for their own ABI lowering. Machine-specific details
such as secondary return registers or byval stack copies must be derived from
the IR and target rules inside the backend, not passed in from the frontend via
side metadata.

### `isel.rs` — Instruction Selection Helpers

Target-independent building blocks shared across all backends:

- `VRegMap` — maps IR `ValueRef` to `VReg` (separate namespaces for instruction results and block args).
- `StackMap` — tracks stack slot allocations (offset from frame pointer).
- `CmpMap<CC>` — tracks comparison results for fused branch emission (generic over target-specific condition codes).
- `VRegAlloc` — sequential virtual register allocator with optional fixed physical register constraints.
- `IselResult<I>` — result of instruction selection (generic over target-specific instruction type).

### `types.rs` — Shared Output Types

- `CompiledFunction` — compiled machine code with relocations, optional debug artifacts, and binding attributes (weak, local).
- `StaticData` — static data blob with relocations and section placement (writable vs read-only).

### `reloc.rs` — Relocation Types

- `RelocKind` — `Call` (PC-relative PLT), `PcRel` (PC-relative data), `Abs64` (absolute 64-bit).
- `Relocation` — offset + symbol name + kind.
- `EncodeResult` — encoded machine code bytes + relocations.

## Dependencies

- `tuffy_ir` — IR definitions
- `tuffy_regalloc` — register allocator types (`VReg`, `PReg`)
