# Move legalization pass from tuffy_target_x86 to tuffy_codegen

- Status: Draft
- Created: 2026-02-28
- Completed: N/A
- Parent: N/A

## Description

Currently the entire legalization pass (`legalize.rs`, ~1574 lines) lives in `tuffy_target_x86`. However, legalization is fundamentally a target-independent algorithm: walk the IR, find ops/types that the target cannot handle natively, and rewrite them into sequences of legal ops. Only the *legality query* ("can this target handle op X on type Y?") is target-specific.

The goal is to split legalization into:

1. **Target-independent legalization driver** (in `tuffy_codegen` or `tuffy_target`) — walks IR, queries legality, applies rewrite rules.
2. **Target legality interface** (in `tuffy_target`) — a trait that each backend implements to declare which (op, type) combinations have direct machine instruction mappings.
3. **x86 legality declaration** (in `tuffy_target_x86`) — implements the trait, declaring what x86-64 supports natively.

### Current state

`tuffy_target_x86/src/legalize.rs` contains:

- i128/u128 detection (`is_128`, `has_128bit_values`)
- Value mapping infrastructure (`VMap`, `Mapped`)
- Full IR rewrite engine (`run_legalize`, `walk_region`, `walk_block_insts`, `copy_inst`)
- ~30 operation-specific lowering functions (`leg_add`, `leg_sub`, `leg_mul`, `leg_shl`, `leg_shr`, `leg_icmp`, `leg_load_128`, `leg_store_128`, etc.)
- ABI metadata remapping (`X86AbiMetadata` handling)

Of these, the rewrite engine and most lowering patterns are generic (splitting N-bit ops into N/2-bit pairs). The x86-specific parts are:
- Which ops/types need legalization (legality query)
- ABI metadata handling (`X86AbiMetadata`)
- Specific register conventions (RDX capture for wide returns)

### Target state

```
tuffy_target/src/legality.rs    — LegalityInfo trait
tuffy_codegen/src/legalize.rs   — target-independent legalization driver + rewrite rules
tuffy_target_x86/src/legality.rs — X86LegalityInfo impl (replaces legalize.rs)
```

## Subtasks

1. Design `LegalityInfo` trait in `tuffy_target` — declare which (op, annotation-width) pairs are legal
2. Move the legalization driver (IR walk, value mapping, block remapping) to `tuffy_codegen`
3. Extract generic rewrite rules (wide int splitting) into the driver
4. Implement `X86LegalityInfo` in `tuffy_target_x86` — express x86-64 legality as trait impl
5. Refactor ABI metadata handling to work through the target abstraction
6. Remove `tuffy_target_x86/src/legalize.rs`
7. Verify `cargo test` and `cargo clippy` pass
8. Run rustlantis fuzzing seeds to confirm no regressions

## Affected Modules

- `tuffy_target/src/` — new `LegalityInfo` trait
- `tuffy_codegen/src/` — new legalization driver
- `tuffy_target_x86/src/legalize.rs` — to be replaced by legality declaration
- `tuffy_target_x86/src/backend.rs` — update pipeline to use new legalization
