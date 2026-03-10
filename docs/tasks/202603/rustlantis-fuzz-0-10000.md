# Rustlantis Fuzz Seeds 0-10000

- **Status:** Completed
- **Created:** 2026-03-29
- **Completed:** 2026-03-29

## Description

Run rustlantis differential fuzzing on seeds 0-10000, fixing all crashes and
miscompilations found.

## Affected Modules

- `rustc_codegen_tuffy`

## Summary

### Initial Run (Seeds 0-1000)

- PASS: 977, FAIL: 24, CRASH: 0

All 24 failures shared the same root cause: the `core::sync::atomic::atomic_load`
function was miscompiled, causing `LazyLock`/`Once` initialization to fail
silently. The hash output from `DefaultHasher` was corrupted because the hasher
was never initialized.

### Root Cause

The `translate_memory_intrinsic` code path in `call.rs` was missing the
stack-local store-back logic that exists in the `translate_intrinsic` path.

In the `atomic_load` function, a `switchInt` on the `Ordering` parameter
dispatches to different basic blocks, each calling a different atomic intrinsic
(`atomic_load_relaxed`, `atomic_load_acquire`, `atomic_load_seqcst`). All write
their result to the same MIR local and converge on a common return block.

The pre-scan correctly promoted this local to a stack slot (since it is assigned
in multiple BBs). However, when `translate_memory_intrinsic` handled the atomic
load, it set the local to the raw SSA value via `locals.set()` without storing
it into the stack slot. Only the last-translated path's SSA value survived in
the local map, so the function always returned the Relaxed path's value
regardless of which ordering was actually taken at runtime.

### Fix

Added stack-local store-back logic to the `translate_memory_intrinsic` code path
in `call.rs`, mirroring the existing logic in the `translate_intrinsic` path.
After the intrinsic sets the local, the code now checks if the destination is a
stack local and stores the result into the slot.

### Verification

- Seeds 0-1000: PASS=1001, FAIL=0, CRASH=0
- Seeds 0-10000: PASS=10001, FAIL=0, CRASH=0
