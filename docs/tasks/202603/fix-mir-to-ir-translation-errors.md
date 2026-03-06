# Fix MIR-to-IR Translation Errors

- Status: Draft
- Created: 2026-03-06
- Completed: N/A
- Parent: N/A

## Description

Fix critical translation errors discovered during code audit of `rustc_codegen_tuffy/src/mir_to_ir`. These errors cause incorrect IR generation for atomic operations, pointer arithmetic, and floating-point comparisons.

## Subtasks

- Fix atomic operations to use correct IR instructions
- Fix pointer offset to use ptradd instead of integer add
- Verify float comparison NaN semantics

## Affected Modules

- `rustc_codegen_tuffy/src/mir_to_ir/intrinsic.rs`
- `rustc_codegen_tuffy/src/mir_to_ir/rvalue.rs`

## Issues to Fix

### 1. Atomic Operations Use Wrong IR Instructions (Critical)

**Location**: `intrinsic.rs:703-978`

**Problem**: All atomic intrinsics (`atomic_load_*`, `atomic_store_*`, `atomic_cxchg_*`, etc.) are lowered to plain `load`/`store` instead of atomic IR instructions.

**Fix Required**:
- `atomic_load_*` → `load.atomic.<ordering>`
- `atomic_store_*` → `store.atomic.<ordering>`
- `atomic_cxchg_*` → `cmpxchg.<success_ord>.<failure_ord>`
- `atomic_xchg_*` → `rmw.xchg.<ordering>`
- `atomic_and/or/xor/xadd/xsub_*` → `rmw.<op>.<ordering>`
- `atomic_fence_*` → `fence.<ordering>`

Map MIR memory orderings (Relaxed/Acquire/Release/AcqRel/SeqCst) to IR orderings.

**Test**: `tests/codegen/atomic_ops.rs`

### 2. Pointer Offset Uses Integer Add Instead of PtrAdd (Medium)

**Location**: `rvalue.rs:1332-1365`

**Problem**: `BinOp::Offset` uses integer addition instead of `ptradd`, losing pointer provenance.

**Fix Required**:
```rust
BinOp::Offset => {
    let ptr = self.coerce_to_ptr(l_raw);
    let byte_offset = if elem_size == 1 {
        r
    } else {
        let sz = self.builder.iconst(elem_size as i64, Origin::synthetic());
        self.builder.mul(r.into(), sz.into(), None, Origin::synthetic())
    };
    self.builder.ptradd(ptr.into(), byte_offset.into(), 0, Origin::synthetic())
}
```

**Test**: `tests/codegen/ptr_offset.rs`

### 3. Float Ne Comparison May Have Wrong NaN Semantics (Low)

**Location**: `rvalue.rs:1196-1210`

**Problem**: `BinOp::Ne` uses `FCmpOp::UNe` instead of `!(OEq)`. Verify if this matches Rust semantics.

**Investigation Required**: Check if `UNe` is equivalent to `!(OEq)` for Rust's `!=` operator.

**Test**: `tests/codegen/float_cmp.rs`

## Implementation Steps

1. Add atomic instruction builders to `tuffy_ir::builder::Builder`
2. Implement memory ordering conversion helper
3. Update `translate_memory_intrinsic` to use atomic instructions
4. Fix `BinOp::Offset` to use `ptradd`
5. Verify float comparison semantics and fix if needed
6. Run codegen tests to verify fixes
7. Update `docs/mir_to_tuffy_ir.md` to reflect any changes in translation behavior
8. Run UI tests and rustlantis for regression testing

## References

- IR Spec: `docs/spec/instructions.md` (atomic ops: lines 503-551, ptradd: lines 589-595)
- Lean IR Types: `lean/TuffyLean/IR/Types.lean` (MemoryOrdering: lines 166-173)
- MIR Semantics: `rustc_middle::mir::syntax`
