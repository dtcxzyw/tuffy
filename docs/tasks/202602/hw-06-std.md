# Standard Library Integration

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-09
- Parent: docs/tasks/202602/hello-world.md

## Description

Even with linking support, a `println!("Hello, world!")` binary requires the standard library runtime to initialize. The compiler must provide certain lang items and shims that std expects from the codegen backend.

Key deliverables:
- Generate allocator shim (the `__rust_alloc` family of symbols)
- Handle `#[panic_handler]` and unwinding stubs (abort strategy initially)
- Support `#[lang = "start"]` entry point that std uses to call `main`
- Compile `core`, `alloc`, `std` through tuffy (or fall back to prebuilt rlibs)
- Verify with `println!("Hello, world!")` end-to-end

## Affected Modules

- `rustc_codegen_tuffy/src/lib.rs` — allocator_module generation, lang item handling
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — must handle enough MIR to compile std shims
