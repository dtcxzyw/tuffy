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
// CHECK:     v5: int:i8 = load.1 v2, v3
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb7(v3), bb8(v3)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v11: mem):
// CHECK:     v12: mem = fence.seqcst v11
// CHECK:     br bb6(v12)
// CHECK:
// CHECK:   bb3(v14: mem):
// CHECK:     v15: mem = fence.seqcst v14
// CHECK:     br bb6(v15)
// CHECK:
// CHECK:   bb4(v17: mem):
// CHECK:     v18: mem = fence.seqcst v17
// CHECK:     br bb6(v18)
// CHECK:
// CHECK:   bb5(v20: mem):
// CHECK:     v21: mem = fence.seqcst v20
// CHECK:     br bb6(v21)
// CHECK:
// CHECK:   bb6(v23: mem):
// CHECK:     ret v23
// CHECK:
// CHECK:   bb7(v25: mem):
// CHECK:     v26: ptr = symbol_addr @.Lstr.0
// CHECK:     v27: int:i64 = iconst 41
// CHECK:     v28: ptr = symbol_addr @.Lstr.0
// CHECK:     v29: int:i64 = iconst 41
// CHECK:     v30: int:i32 = iconst 1
// CHECK:     v31: int:i64 = iconst 63
// CHECK:     v32: int:i64 = and v30, v31
// CHECK:     v33: int:i64 = shl v29:u64, v32
// CHECK:     v34: int:u64 = zext v33, 64
// CHECK:     v35: int:i64 = iconst 1
// CHECK:     v36: int:i64 = or v34, v35:u64
// CHECK:     v37: int:u64 = zext v36, 64
// CHECK:     v38: mem = store.8 v26, v4, v25
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v4, v39
// CHECK:     v41: mem = store.8 v37, v40, v38
// CHECK:     v42: int:i64 = load.8 v4, v41
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v4, v43
// CHECK:     v45: int:i64 = load.8 v44, v41
// CHECK:     v46: ptr = symbol_addr @.Lloc.2
// CHECK:     v47: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v48: mem = call v47(v42, v45, v46), v41
// CHECK:     v49: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v51: mem):
// CHECK:     v52: int:i64 = iconst 1
// CHECK:     v53: bool = icmp.eq v5, v52
// CHECK:     brif v53, bb5(v51), bb9(v51)
// CHECK:
// CHECK:   bb9(v55: mem):
// CHECK:     v56: int:i64 = iconst 2
// CHECK:     v57: bool = icmp.eq v5, v56
// CHECK:     brif v57, bb4(v55), bb10(v55)
// CHECK:
// CHECK:   bb10(v59: mem):
// CHECK:     v60: int:i64 = iconst 3
// CHECK:     v61: bool = icmp.eq v5, v60
// CHECK:     brif v61, bb3(v59), bb11(v59)
// CHECK:
// CHECK:   bb11(v63: mem):
// CHECK:     v64: int:i64 = iconst 4
// CHECK:     v65: bool = icmp.eq v5, v64
// CHECK:     brif v65, bb2(v63), bb1(v63)
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
// CHECK:     v5: int:i8 = load.1 v2, v3
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb7(v3), bb8(v3)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v11: mem):
// CHECK:     v12: mem = fence.seqcst v11
// CHECK:     br bb6(v12)
// CHECK:
// CHECK:   bb3(v14: mem):
// CHECK:     v15: mem = fence.seqcst v14
// CHECK:     br bb6(v15)
// CHECK:
// CHECK:   bb4(v17: mem):
// CHECK:     v18: mem = fence.seqcst v17
// CHECK:     br bb6(v18)
// CHECK:
// CHECK:   bb5(v20: mem):
// CHECK:     v21: mem = fence.seqcst v20
// CHECK:     br bb6(v21)
// CHECK:
// CHECK:   bb6(v23: mem):
// CHECK:     ret v23
// CHECK:
// CHECK:   bb7(v25: mem):
// CHECK:     v26: ptr = symbol_addr @.Lstr.0
// CHECK:     v27: int:i64 = iconst 41
// CHECK:     v28: ptr = symbol_addr @.Lstr.0
// CHECK:     v29: int:i64 = iconst 41
// CHECK:     v30: int:i32 = iconst 1
// CHECK:     v31: int:i64 = iconst 63
// CHECK:     v32: int:i64 = and v30, v31
// CHECK:     v33: int:i64 = shl v29:u64, v32
// CHECK:     v34: int:u64 = zext v33, 64
// CHECK:     v35: int:i64 = iconst 1
// CHECK:     v36: int:i64 = or v34, v35:u64
// CHECK:     v37: int:u64 = zext v36, 64
// CHECK:     v38: mem = store.8 v26, v4, v25
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v4, v39
// CHECK:     v41: mem = store.8 v37, v40, v38
// CHECK:     v42: int:i64 = load.8 v4, v41
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v4, v43
// CHECK:     v45: int:i64 = load.8 v44, v41
// CHECK:     v46: ptr = symbol_addr @.Lloc.4
// CHECK:     v47: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v48: mem = call v47(v42, v45, v46), v41
// CHECK:     v49: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v51: mem):
// CHECK:     v52: int:i64 = iconst 1
// CHECK:     v53: bool = icmp.eq v5, v52
// CHECK:     brif v53, bb5(v51), bb9(v51)
// CHECK:
// CHECK:   bb9(v55: mem):
// CHECK:     v56: int:i64 = iconst 2
// CHECK:     v57: bool = icmp.eq v5, v56
// CHECK:     brif v57, bb4(v55), bb10(v55)
// CHECK:
// CHECK:   bb10(v59: mem):
// CHECK:     v60: int:i64 = iconst 3
// CHECK:     v61: bool = icmp.eq v5, v60
// CHECK:     brif v61, bb3(v59), bb11(v59)
// CHECK:
// CHECK:   bb11(v63: mem):
// CHECK:     v64: int:i64 = iconst 4
// CHECK:     v65: bool = icmp.eq v5, v64
// CHECK:     brif v65, bb2(v63), bb1(v63)
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
