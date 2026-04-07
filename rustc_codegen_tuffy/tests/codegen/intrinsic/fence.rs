// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn core::sync::atomic::compiler_fence(_1: core::sync::atomic::Ordering) -> () {
// CHECK:     debug order => _1;
// CHECK:     let mut _0: ();
// CHECK:     let mut _2: isize;
// CHECK:     let _3: !;
// CHECK:     let mut _4: core::fmt::Arguments<'_>;
// CHECK:     let mut _5: &str;
// CHECK:     scope 1 (inlined core::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _5;
// CHECK:         let mut _6: core::ptr::NonNull<u8>;
// CHECK:         let mut _7: *const u8;
// CHECK:         let mut _8: core::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _9: usize;
// CHECK:         let mut _10: usize;
// CHECK:         let mut _11: usize;
// CHECK:         scope 2 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _5;
// CHECK:             let mut _12: *const str;
// CHECK:         }
// CHECK:         scope 3 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _5;
// CHECK:             let _13: &[u8];
// CHECK:             scope 4 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _5;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _2 = discriminant(_1);
// CHECK:         switchInt(move _2) -> [0: bb2, 1: bb5, 2: bb6, 3: bb4, 4: bb3, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const "there is no such thing as a relaxed fence";
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_12);
// CHECK:         _12 = &raw const (*_5);
// CHECK:         _7 = copy _12 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_12);
// CHECK:         _6 = copy _7 as core::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_13);
// CHECK:         _13 = const "there is no such thing as a relaxed fence" as &[u8] (Transmute);
// CHECK:         _11 = PtrMetadata(copy _13);
// CHECK:         StorageDead(_13);
// CHECK:         _10 = Shl(move _11, const 1_i32);
// CHECK:         StorageDead(_11);
// CHECK:         _9 = BitOr(move _10, const 1_usize);
// CHECK:         StorageDead(_10);
// CHECK:         _8 = move _9 as core::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_9);
// CHECK:         _4 = core::fmt::Arguments::<'_> { template: move _6, args: move _8 };
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         _3 = core::panicking::panic_fmt(move _4) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = core::intrinsics::atomic_singlethreadfence::<core::intrinsics::AtomicOrdering::SeqCst>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _0 = core::intrinsics::atomic_singlethreadfence::<core::intrinsics::AtomicOrdering::AcqRel>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _0 = core::intrinsics::atomic_singlethreadfence::<core::intrinsics::AtomicOrdering::Release>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = core::intrinsics::atomic_singlethreadfence::<core::intrinsics::AtomicOrdering::Acquire>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc1 (size: 41, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 20 72 65 6c 61 │  thing as a rela
// CHECK:     0x20 │ 78 65 64 20 66 65 6e 63 65                      │ xed fence
// CHECK: }
// CHECK: data @.Lstr.0 = "there is no such thing as a relaxed fence"
// CHECK: data @.Lloc_file.1 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.2 = "..." relocs [0: @.Lloc_file.1]
// CHECK: func @_RNvNtNtC$HASH_4core4sync6atomic14compiler_fenceC$HASH_5fence(int:i8) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i8 = param 0
// CHECK:     v2: ptr = stack_slot 1 align 1
// CHECK:     v3: mem = store.1 v1, v2, v0
// CHECK:     v4: ptr = stack_slot 16 align 8
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: int:i8 = load.1 v2, v3
// CHECK:     v7: int:i64 = iconst 0
// CHECK:     v8: bool = icmp.eq v6, v7
// CHECK:     brif v8, bb7(v3), bb8(v3)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13: mem = fence.seqcst v12
// CHECK:     br bb6(v13)
// CHECK:
// CHECK:   bb3(v15: mem):
// CHECK:     v16: mem = fence.seqcst v15
// CHECK:     br bb6(v16)
// CHECK:
// CHECK:   bb4(v18: mem):
// CHECK:     v19: mem = fence.seqcst v18
// CHECK:     br bb6(v19)
// CHECK:
// CHECK:   bb5(v21: mem):
// CHECK:     v22: mem = fence.seqcst v21
// CHECK:     br bb6(v22)
// CHECK:
// CHECK:   bb6(v24: mem):
// CHECK:     ret v24
// CHECK:
// CHECK:   bb7(v26: mem):
// CHECK:     v27: ptr = symbol_addr @.Lstr.0
// CHECK:     v28: int:i64 = iconst 41
// CHECK:     v29: mem = store.8 v27, v5, v26
// CHECK:     v30: int:i64 = iconst 8
// CHECK:     v31: ptr = ptradd v5, v30
// CHECK:     v32: mem = store.8 v28, v31, v29
// CHECK:     v33: int:i64 = iconst 41
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: ptr = load.8 v5, v36
// CHECK:     v38: int:i64 = iconst 8
// CHECK:     v39: ptr = ptradd v5, v38
// CHECK:     v40: int:i64 = load.8 v39, v36
// CHECK:     v41: ptr = stack_slot 16
// CHECK:     v42: mem = store.8 v37, v41, v36
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v41, v43
// CHECK:     v45: mem = store.8 v40, v44, v42
// CHECK:     v46: int:i64 = iconst 8
// CHECK:     v47: ptr = ptradd v5, v46
// CHECK:     v48: int:i64 = load.8 v47, v45
// CHECK:     v49: int:i64 = iconst 8
// CHECK:     v50: ptr = ptradd v41, v49
// CHECK:     v51: mem = store.8 v48, v50, v45
// CHECK:     v52: ptr = load.8 v41, v51
// CHECK:     v53: ptr = symbol_addr @.Lstr.0
// CHECK:     v54: int:i64 = iconst 41
// CHECK:     v55: int:i32 = iconst 1
// CHECK:     v56: int:i64 = iconst 63
// CHECK:     v57: int:i64 = and v55, v56
// CHECK:     v58: int:i64 = shl v54:u64, v57
// CHECK:     v59: int:u64 = zext v58, 64
// CHECK:     v60: int:i64 = iconst 1
// CHECK:     v61: int:i64 = or v59, v60:u64
// CHECK:     v62: int:u64 = zext v61, 64
// CHECK:     v63: mem = store.8 v52, v4, v51
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v4, v64
// CHECK:     v66: mem = store.8 v62, v65, v63
// CHECK:     v67: int:i64 = load.8 v4, v66
// CHECK:     v68: int:i64 = iconst 8
// CHECK:     v69: ptr = ptradd v4, v68
// CHECK:     v70: int:i64 = load.8 v69, v66
// CHECK:     v71: ptr = symbol_addr @.Lloc.2
// CHECK:     v72: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v73: mem = call v72(v67, v70, v71), v66
// CHECK:     v74: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v76: mem):
// CHECK:     v77: int:i64 = iconst 1
// CHECK:     v78: bool = icmp.eq v6, v77
// CHECK:     brif v78, bb5(v76), bb9(v76)
// CHECK:
// CHECK:   bb9(v80: mem):
// CHECK:     v81: int:i64 = iconst 2
// CHECK:     v82: bool = icmp.eq v6, v81
// CHECK:     brif v82, bb4(v80), bb10(v80)
// CHECK:
// CHECK:   bb10(v84: mem):
// CHECK:     v85: int:i64 = iconst 3
// CHECK:     v86: bool = icmp.eq v6, v85
// CHECK:     brif v86, bb3(v84), bb11(v84)
// CHECK:
// CHECK:   bb11(v88: mem):
// CHECK:     v89: int:i64 = iconst 4
// CHECK:     v90: bool = icmp.eq v6, v89
// CHECK:     brif v90, bb2(v88), bb1(v88)
// CHECK: }
// CHECK:
// CHECK: fn core::sync::atomic::fence(_1: core::sync::atomic::Ordering) -> () {
// CHECK:     debug order => _1;
// CHECK:     let mut _0: ();
// CHECK:     let mut _2: isize;
// CHECK:     let _3: !;
// CHECK:     let mut _4: core::fmt::Arguments<'_>;
// CHECK:     let mut _5: &str;
// CHECK:     scope 1 (inlined core::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _5;
// CHECK:         let mut _6: core::ptr::NonNull<u8>;
// CHECK:         let mut _7: *const u8;
// CHECK:         let mut _8: core::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _9: usize;
// CHECK:         let mut _10: usize;
// CHECK:         let mut _11: usize;
// CHECK:         scope 2 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _5;
// CHECK:             let mut _12: *const str;
// CHECK:         }
// CHECK:         scope 3 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _5;
// CHECK:             let _13: &[u8];
// CHECK:             scope 4 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _5;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _2 = discriminant(_1);
// CHECK:         switchInt(move _2) -> [0: bb2, 1: bb5, 2: bb6, 3: bb4, 4: bb3, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const "there is no such thing as a relaxed fence";
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_12);
// CHECK:         _12 = &raw const (*_5);
// CHECK:         _7 = copy _12 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_12);
// CHECK:         _6 = copy _7 as core::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_13);
// CHECK:         _13 = const "there is no such thing as a relaxed fence" as &[u8] (Transmute);
// CHECK:         _11 = PtrMetadata(copy _13);
// CHECK:         StorageDead(_13);
// CHECK:         _10 = Shl(move _11, const 1_i32);
// CHECK:         StorageDead(_11);
// CHECK:         _9 = BitOr(move _10, const 1_usize);
// CHECK:         StorageDead(_10);
// CHECK:         _8 = move _9 as core::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_9);
// CHECK:         _4 = core::fmt::Arguments::<'_> { template: move _6, args: move _8 };
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         _3 = core::panicking::panic_fmt(move _4) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = core::intrinsics::atomic_fence::<core::intrinsics::AtomicOrdering::SeqCst>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _0 = core::intrinsics::atomic_fence::<core::intrinsics::AtomicOrdering::AcqRel>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _0 = core::intrinsics::atomic_fence::<core::intrinsics::AtomicOrdering::Release>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = core::intrinsics::atomic_fence::<core::intrinsics::AtomicOrdering::Acquire>() -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc1 (size: 41, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 20 72 65 6c 61 │  thing as a rela
// CHECK:     0x20 │ 78 65 64 20 66 65 6e 63 65                      │ xed fence
// CHECK: }
// CHECK: data @.Lloc_file.3 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.4 = "..." relocs [0: @.Lloc_file.3]
// CHECK: func @_RNvNtNtC$HASH_4core4sync6atomic5fenceC$HASH_5fence(int:i8) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i8 = param 0
// CHECK:     v2: ptr = stack_slot 1 align 1
// CHECK:     v3: mem = store.1 v1, v2, v0
// CHECK:     v4: ptr = stack_slot 16 align 8
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: int:i8 = load.1 v2, v3
// CHECK:     v7: int:i64 = iconst 0
// CHECK:     v8: bool = icmp.eq v6, v7
// CHECK:     brif v8, bb7(v3), bb8(v3)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13: mem = fence.seqcst v12
// CHECK:     br bb6(v13)
// CHECK:
// CHECK:   bb3(v15: mem):
// CHECK:     v16: mem = fence.seqcst v15
// CHECK:     br bb6(v16)
// CHECK:
// CHECK:   bb4(v18: mem):
// CHECK:     v19: mem = fence.seqcst v18
// CHECK:     br bb6(v19)
// CHECK:
// CHECK:   bb5(v21: mem):
// CHECK:     v22: mem = fence.seqcst v21
// CHECK:     br bb6(v22)
// CHECK:
// CHECK:   bb6(v24: mem):
// CHECK:     ret v24
// CHECK:
// CHECK:   bb7(v26: mem):
// CHECK:     v27: ptr = symbol_addr @.Lstr.0
// CHECK:     v28: int:i64 = iconst 41
// CHECK:     v29: mem = store.8 v27, v5, v26
// CHECK:     v30: int:i64 = iconst 8
// CHECK:     v31: ptr = ptradd v5, v30
// CHECK:     v32: mem = store.8 v28, v31, v29
// CHECK:     v33: int:i64 = iconst 41
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: ptr = load.8 v5, v36
// CHECK:     v38: int:i64 = iconst 8
// CHECK:     v39: ptr = ptradd v5, v38
// CHECK:     v40: int:i64 = load.8 v39, v36
// CHECK:     v41: ptr = stack_slot 16
// CHECK:     v42: mem = store.8 v37, v41, v36
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v41, v43
// CHECK:     v45: mem = store.8 v40, v44, v42
// CHECK:     v46: int:i64 = iconst 8
// CHECK:     v47: ptr = ptradd v5, v46
// CHECK:     v48: int:i64 = load.8 v47, v45
// CHECK:     v49: int:i64 = iconst 8
// CHECK:     v50: ptr = ptradd v41, v49
// CHECK:     v51: mem = store.8 v48, v50, v45
// CHECK:     v52: ptr = load.8 v41, v51
// CHECK:     v53: ptr = symbol_addr @.Lstr.0
// CHECK:     v54: int:i64 = iconst 41
// CHECK:     v55: int:i32 = iconst 1
// CHECK:     v56: int:i64 = iconst 63
// CHECK:     v57: int:i64 = and v55, v56
// CHECK:     v58: int:i64 = shl v54:u64, v57
// CHECK:     v59: int:u64 = zext v58, 64
// CHECK:     v60: int:i64 = iconst 1
// CHECK:     v61: int:i64 = or v59, v60:u64
// CHECK:     v62: int:u64 = zext v61, 64
// CHECK:     v63: mem = store.8 v52, v4, v51
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v4, v64
// CHECK:     v66: mem = store.8 v62, v65, v63
// CHECK:     v67: int:i64 = load.8 v4, v66
// CHECK:     v68: int:i64 = iconst 8
// CHECK:     v69: ptr = ptradd v4, v68
// CHECK:     v70: int:i64 = load.8 v69, v66
// CHECK:     v71: ptr = symbol_addr @.Lloc.4
// CHECK:     v72: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v73: mem = call v72(v67, v70, v71), v66
// CHECK:     v74: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v76: mem):
// CHECK:     v77: int:i64 = iconst 1
// CHECK:     v78: bool = icmp.eq v6, v77
// CHECK:     brif v78, bb5(v76), bb9(v76)
// CHECK:
// CHECK:   bb9(v80: mem):
// CHECK:     v81: int:i64 = iconst 2
// CHECK:     v82: bool = icmp.eq v6, v81
// CHECK:     brif v82, bb4(v80), bb10(v80)
// CHECK:
// CHECK:   bb10(v84: mem):
// CHECK:     v85: int:i64 = iconst 3
// CHECK:     v86: bool = icmp.eq v6, v85
// CHECK:     brif v86, bb3(v84), bb11(v84)
// CHECK:
// CHECK:   bb11(v88: mem):
// CHECK:     v89: int:i64 = iconst 4
// CHECK:     v90: bool = icmp.eq v6, v89
// CHECK:     brif v90, bb2(v88), bb1(v88)
// CHECK: }
// CHECK:
// CHECK: fn acquire_compiler_fence() -> () {
// CHECK:     let mut _0: ();
// CHECK:     let _1: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         _1 = core::sync::atomic::compiler_fence(const core::sync::atomic::Ordering::Acquire) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @acquire_compiler_fence() {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i8 = iconst 2
// CHECK:     v2: ptr = symbol_addr @_RNvNtNtC$HASH_4core4sync6atomic14compiler_fenceC$HASH_5fence
// CHECK:     v3: mem = call v2(v1), v0
// CHECK:     v4: int:i64 = iconst 0
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v6
// CHECK: }
// CHECK:
// CHECK: fn seqcst_fence() -> () {
// CHECK:     let mut _0: ();
// CHECK:     let _1: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         _1 = core::sync::atomic::fence(const core::sync::atomic::Ordering::SeqCst) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @seqcst_fence() {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i8 = iconst 4
// CHECK:     v2: ptr = symbol_addr @_RNvNtNtC$HASH_4core4sync6atomic5fenceC$HASH_5fence
// CHECK:     v3: mem = call v2(v1), v0
// CHECK:     v4: int:i64 = iconst 0
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v6
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::sync::atomic::{Ordering, compiler_fence, fence};

#[no_mangle]
pub fn seqcst_fence() {
    fence(Ordering::SeqCst);
}

#[no_mangle]
pub fn acquire_compiler_fence() {
    compiler_fence(Ordering::Acquire);
}
