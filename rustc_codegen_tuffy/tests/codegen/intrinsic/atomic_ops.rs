// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn std::sync::atomic::atomic_load(_1: *const T, _2: std::sync::atomic::Ordering) -> T {
// CHECK:     debug dst => _1;
// CHECK:     debug order => _2;
// CHECK:     let mut _0: T;
// CHECK:     let mut _3: isize;
// CHECK:     let _4: !;
// CHECK:     let mut _5: std::fmt::Arguments<'_>;
// CHECK:     let _6: !;
// CHECK:     let mut _7: std::fmt::Arguments<'_>;
// CHECK:     let mut _8: &str;
// CHECK:     let mut _17: &str;
// CHECK:     scope 1 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _8;
// CHECK:         let mut _9: std::ptr::NonNull<u8>;
// CHECK:         let mut _10: *const u8;
// CHECK:         let mut _11: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _12: usize;
// CHECK:         let mut _13: usize;
// CHECK:         let mut _14: usize;
// CHECK:         scope 2 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _8;
// CHECK:             let mut _15: *const str;
// CHECK:         }
// CHECK:         scope 3 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _8;
// CHECK:             let _16: &[u8];
// CHECK:             scope 4 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _8;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 5 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _17;
// CHECK:         let mut _18: std::ptr::NonNull<u8>;
// CHECK:         let mut _19: *const u8;
// CHECK:         let mut _20: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _21: usize;
// CHECK:         let mut _22: usize;
// CHECK:         let mut _23: usize;
// CHECK:         scope 6 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _17;
// CHECK:             let mut _24: *const str;
// CHECK:         }
// CHECK:         scope 7 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _17;
// CHECK:             let _25: &[u8];
// CHECK:             scope 8 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _17;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = discriminant(_2);
// CHECK:         switchInt(move _3) -> [0: bb6, 1: bb3, 2: bb5, 3: bb2, 4: bb4, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = const "there is no such thing as an acquire-release load";
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_15);
// CHECK:         _15 = &raw const (*_8);
// CHECK:         _10 = copy _15 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_15);
// CHECK:         _9 = copy _10 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_10);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_16);
// CHECK:         _16 = const "there is no such thing as an acquire-release load" as &[u8] (Transmute);
// CHECK:         _14 = PtrMetadata(copy _16);
// CHECK:         StorageDead(_16);
// CHECK:         _13 = Shl(move _14, const 1_i32);
// CHECK:         StorageDead(_14);
// CHECK:         _12 = BitOr(move _13, const 1_usize);
// CHECK:         StorageDead(_13);
// CHECK:         _11 = move _12 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_12);
// CHECK:         _7 = std::fmt::Arguments::<'_> { template: move _9, args: move _11 };
// CHECK:         StorageDead(_11);
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         _6 = std::rt::panic_fmt(move _7) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = const "there is no such thing as a release load";
// CHECK:         StorageLive(_18);
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_24);
// CHECK:         _24 = &raw const (*_17);
// CHECK:         _19 = copy _24 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_24);
// CHECK:         _18 = copy _19 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_19);
// CHECK:         StorageLive(_20);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_23);
// CHECK:         StorageLive(_25);
// CHECK:         _25 = const "there is no such thing as a release load" as &[u8] (Transmute);
// CHECK:         _23 = PtrMetadata(copy _25);
// CHECK:         StorageDead(_25);
// CHECK:         _22 = Shl(move _23, const 1_i32);
// CHECK:         StorageDead(_23);
// CHECK:         _21 = BitOr(move _22, const 1_usize);
// CHECK:         StorageDead(_22);
// CHECK:         _20 = move _21 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_21);
// CHECK:         _5 = std::fmt::Arguments::<'_> { template: move _18, args: move _20 };
// CHECK:         StorageDead(_20);
// CHECK:         StorageDead(_18);
// CHECK:         StorageDead(_17);
// CHECK:         _4 = std::rt::panic_fmt(move _5) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _0 = std::intrinsics::atomic_load::<T, std::intrinsics::AtomicOrdering::SeqCst>(move _1) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _0 = std::intrinsics::atomic_load::<T, std::intrinsics::AtomicOrdering::Acquire>(move _1) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = std::intrinsics::atomic_load::<T, std::intrinsics::AtomicOrdering::Relaxed>(move _1) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc2 (size: 40, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 20 72 65 6c 65 │  thing as a rele
// CHECK:     0x20 │ 61 73 65 20 6c 6f 61 64                         │ ase load
// CHECK: }
// CHECK:
// CHECK: alloc1 (size: 49, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 6e 20 61 63 71 │  thing as an acq
// CHECK:     0x20 │ 75 69 72 65 2d 72 65 6c 65 61 73 65 20 6c 6f 61 │ uire-release loa
// CHECK:     0x30 │ 64                                              │ d
// CHECK: }
// CHECK: data @.Lstr.0 = "there is no such thing as an acquire-release load"
// CHECK: data @.Lloc_file.1 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.2 = "..." relocs [0: @.Lloc_file.1]
// CHECK: data @.Lstr.3 = "there is no such thing as a release load"
// CHECK: data @.Lloc_file.4 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.5 = "..." relocs [0: @.Lloc_file.4]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic11atomic_loadmEC$HASH_10atomic_ops(ptr, int:i8) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i8 = param 1
// CHECK:     v3: ptr = stack_slot 1 align 1
// CHECK:     v4: mem = store.1 v2, v3, v0
// CHECK:     v5: ptr = stack_slot 4 align 4
// CHECK:     v6: ptr = stack_slot 16 align 8
// CHECK:     v7: ptr = stack_slot 16 align 8
// CHECK:     v8: int:i8 = load.1 v3, v4
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     v10: bool = icmp.eq v8, v9
// CHECK:     brif v10, bb6(v4), bb8(v4)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v14: mem):
// CHECK:     v15: mem, v16: int:i32 = load.atomic.seqcst v1, v14
// CHECK:     v17: mem = store.4 v16, v5, v15
// CHECK:     br bb7(v17)
// CHECK:
// CHECK:   bb3(v19: mem):
// CHECK:     v20: ptr = symbol_addr @.Lstr.0
// CHECK:     v21: int:i64 = iconst 49
// CHECK:     v22: ptr = symbol_addr @.Lstr.0
// CHECK:     v23: int:i64 = iconst 49
// CHECK:     v24: int:i32 = iconst 1
// CHECK:     v25: int:i64 = iconst 63
// CHECK:     v26: int:i64 = and v24, v25
// CHECK:     v27: int:i64 = shl v23:u64, v26
// CHECK:     v28: int:u64 = zext v27, 64
// CHECK:     v29: int:i64 = iconst 1
// CHECK:     v30: int:i64 = or v28, v29:u64
// CHECK:     v31: int:u64 = zext v30, 64
// CHECK:     v32: mem = store.8 v20, v7, v19
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v7, v33
// CHECK:     v35: mem = store.8 v31, v34, v32
// CHECK:     v36: int:i64 = load.8 v7, v35
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v7, v37
// CHECK:     v39: int:i64 = load.8 v38, v35
// CHECK:     v40: ptr = symbol_addr @.Lloc.2
// CHECK:     v41: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v42: mem = call v41(v36, v39, v40), v35
// CHECK:     v43: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v45: mem):
// CHECK:     v46: mem, v47: int:i32 = load.atomic.seqcst v1, v45
// CHECK:     v48: mem = store.4 v47, v5, v46
// CHECK:     br bb7(v48)
// CHECK:
// CHECK:   bb5(v50: mem):
// CHECK:     v51: ptr = symbol_addr @.Lstr.3
// CHECK:     v52: int:i64 = iconst 40
// CHECK:     v53: ptr = symbol_addr @.Lstr.3
// CHECK:     v54: int:i64 = iconst 40
// CHECK:     v55: int:i32 = iconst 1
// CHECK:     v56: int:i64 = iconst 63
// CHECK:     v57: int:i64 = and v55, v56
// CHECK:     v58: int:i64 = shl v54:u64, v57
// CHECK:     v59: int:u64 = zext v58, 64
// CHECK:     v60: int:i64 = iconst 1
// CHECK:     v61: int:i64 = or v59, v60:u64
// CHECK:     v62: int:u64 = zext v61, 64
// CHECK:     v63: mem = store.8 v51, v6, v50
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v6, v64
// CHECK:     v66: mem = store.8 v62, v65, v63
// CHECK:     v67: int:i64 = load.8 v6, v66
// CHECK:     v68: int:i64 = iconst 8
// CHECK:     v69: ptr = ptradd v6, v68
// CHECK:     v70: int:i64 = load.8 v69, v66
// CHECK:     v71: ptr = symbol_addr @.Lloc.5
// CHECK:     v72: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v73: mem = call v72(v67, v70, v71), v66
// CHECK:     v74: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb6(v76: mem):
// CHECK:     v77: mem, v78: int:i32 = load.atomic.seqcst v1, v76
// CHECK:     v79: mem = store.4 v78, v5, v77
// CHECK:     br bb7(v79)
// CHECK:
// CHECK:   bb7(v81: mem):
// CHECK:     v82: int:u32 = load.4 v5, v81
// CHECK:     ret v82, v81
// CHECK:
// CHECK:   bb8(v84: mem):
// CHECK:     v85: int:i64 = iconst 1
// CHECK:     v86: bool = icmp.eq v8, v85
// CHECK:     brif v86, bb5(v84), bb9(v84)
// CHECK:
// CHECK:   bb9(v88: mem):
// CHECK:     v89: int:i64 = iconst 2
// CHECK:     v90: bool = icmp.eq v8, v89
// CHECK:     brif v90, bb4(v88), bb10(v88)
// CHECK:
// CHECK:   bb10(v92: mem):
// CHECK:     v93: int:i64 = iconst 3
// CHECK:     v94: bool = icmp.eq v8, v93
// CHECK:     brif v94, bb3(v92), bb11(v92)
// CHECK:
// CHECK:   bb11(v96: mem):
// CHECK:     v97: int:i64 = iconst 4
// CHECK:     v98: bool = icmp.eq v8, v97
// CHECK:     brif v98, bb2(v96), bb1(v96)
// CHECK: }
// CHECK:
// CHECK: fn std::sync::atomic::atomic_store(_1: *mut T, _2: T, _3: std::sync::atomic::Ordering) -> () {
// CHECK:     debug dst => _1;
// CHECK:     debug val => _2;
// CHECK:     debug order => _3;
// CHECK:     let mut _0: ();
// CHECK:     let mut _4: isize;
// CHECK:     let _5: !;
// CHECK:     let mut _6: std::fmt::Arguments<'_>;
// CHECK:     let _7: !;
// CHECK:     let mut _8: std::fmt::Arguments<'_>;
// CHECK:     let mut _9: &str;
// CHECK:     let mut _18: &str;
// CHECK:     scope 1 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _9;
// CHECK:         let mut _10: std::ptr::NonNull<u8>;
// CHECK:         let mut _11: *const u8;
// CHECK:         let mut _12: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _13: usize;
// CHECK:         let mut _14: usize;
// CHECK:         let mut _15: usize;
// CHECK:         scope 2 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _9;
// CHECK:             let mut _16: *const str;
// CHECK:         }
// CHECK:         scope 3 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _9;
// CHECK:             let _17: &[u8];
// CHECK:             scope 4 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _9;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 5 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _18;
// CHECK:         let mut _19: std::ptr::NonNull<u8>;
// CHECK:         let mut _20: *const u8;
// CHECK:         let mut _21: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _22: usize;
// CHECK:         let mut _23: usize;
// CHECK:         let mut _24: usize;
// CHECK:         scope 6 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _18;
// CHECK:             let mut _25: *const str;
// CHECK:         }
// CHECK:         scope 7 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _18;
// CHECK:             let _26: &[u8];
// CHECK:             scope 8 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _18;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _4 = discriminant(_3);
// CHECK:         switchInt(move _4) -> [0: bb6, 1: bb5, 2: bb3, 3: bb2, 4: bb4, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = const "there is no such thing as an acquire-release store";
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_16);
// CHECK:         _16 = &raw const (*_9);
// CHECK:         _11 = copy _16 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_16);
// CHECK:         _10 = copy _11 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = const "there is no such thing as an acquire-release store" as &[u8] (Transmute);
// CHECK:         _15 = PtrMetadata(copy _17);
// CHECK:         StorageDead(_17);
// CHECK:         _14 = Shl(move _15, const 1_i32);
// CHECK:         StorageDead(_15);
// CHECK:         _13 = BitOr(move _14, const 1_usize);
// CHECK:         StorageDead(_14);
// CHECK:         _12 = move _13 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_13);
// CHECK:         _8 = std::fmt::Arguments::<'_> { template: move _10, args: move _12 };
// CHECK:         StorageDead(_12);
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_9);
// CHECK:         _7 = std::rt::panic_fmt(move _8) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_18);
// CHECK:         _18 = const "there is no such thing as an acquire store";
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_20);
// CHECK:         StorageLive(_25);
// CHECK:         _25 = &raw const (*_18);
// CHECK:         _20 = copy _25 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_25);
// CHECK:         _19 = copy _20 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_20);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_23);
// CHECK:         StorageLive(_24);
// CHECK:         StorageLive(_26);
// CHECK:         _26 = const "there is no such thing as an acquire store" as &[u8] (Transmute);
// CHECK:         _24 = PtrMetadata(copy _26);
// CHECK:         StorageDead(_26);
// CHECK:         _23 = Shl(move _24, const 1_i32);
// CHECK:         StorageDead(_24);
// CHECK:         _22 = BitOr(move _23, const 1_usize);
// CHECK:         StorageDead(_23);
// CHECK:         _21 = move _22 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_22);
// CHECK:         _6 = std::fmt::Arguments::<'_> { template: move _19, args: move _21 };
// CHECK:         StorageDead(_21);
// CHECK:         StorageDead(_19);
// CHECK:         StorageDead(_18);
// CHECK:         _5 = std::rt::panic_fmt(move _6) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _0 = std::intrinsics::atomic_store::<T, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _0 = std::intrinsics::atomic_store::<T, std::intrinsics::AtomicOrdering::Release>(move _1, move _2) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = std::intrinsics::atomic_store::<T, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc9 (size: 42, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 6e 20 61 63 71 │  thing as an acq
// CHECK:     0x20 │ 75 69 72 65 20 73 74 6f 72 65                   │ uire store
// CHECK: }
// CHECK:
// CHECK: alloc8 (size: 50, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 6e 20 61 63 71 │  thing as an acq
// CHECK:     0x20 │ 75 69 72 65 2d 72 65 6c 65 61 73 65 20 73 74 6f │ uire-release sto
// CHECK:     0x30 │ 72 65                                           │ re
// CHECK: }
// CHECK: data @.Lstr.6 = "there is no such thing as an acquire-release store"
// CHECK: data @.Lloc_file.7 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.8 = "..." relocs [0: @.Lloc_file.7]
// CHECK: data @.Lstr.9 = "there is no such thing as an acquire store"
// CHECK: data @.Lloc_file.10 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.11 = "..." relocs [0: @.Lloc_file.10]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic12atomic_storemEC$HASH_10atomic_ops(ptr, int:u32, int:i8) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:i8 = param 2
// CHECK:     v4: ptr = stack_slot 1 align 1
// CHECK:     v5: mem = store.1 v3, v4, v0
// CHECK:     v6: ptr = stack_slot 16 align 8
// CHECK:     v7: ptr = stack_slot 16 align 8
// CHECK:     v8: int:i8 = load.1 v4, v5
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     v10: bool = icmp.eq v8, v9
// CHECK:     brif v10, bb6(v5), bb8(v5)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v14: mem):
// CHECK:     v15: mem = store.atomic.seqcst v2, v1, v14
// CHECK:     br bb7(v15)
// CHECK:
// CHECK:   bb3(v17: mem):
// CHECK:     v18: ptr = symbol_addr @.Lstr.6
// CHECK:     v19: int:i64 = iconst 50
// CHECK:     v20: ptr = symbol_addr @.Lstr.6
// CHECK:     v21: int:i64 = iconst 50
// CHECK:     v22: int:i32 = iconst 1
// CHECK:     v23: int:i64 = iconst 63
// CHECK:     v24: int:i64 = and v22, v23
// CHECK:     v25: int:i64 = shl v21:u64, v24
// CHECK:     v26: int:u64 = zext v25, 64
// CHECK:     v27: int:i64 = iconst 1
// CHECK:     v28: int:i64 = or v26, v27:u64
// CHECK:     v29: int:u64 = zext v28, 64
// CHECK:     v30: mem = store.8 v18, v7, v17
// CHECK:     v31: int:i64 = iconst 8
// CHECK:     v32: ptr = ptradd v7, v31
// CHECK:     v33: mem = store.8 v29, v32, v30
// CHECK:     v34: int:i64 = load.8 v7, v33
// CHECK:     v35: int:i64 = iconst 8
// CHECK:     v36: ptr = ptradd v7, v35
// CHECK:     v37: int:i64 = load.8 v36, v33
// CHECK:     v38: ptr = symbol_addr @.Lloc.8
// CHECK:     v39: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v40: mem = call v39(v34, v37, v38), v33
// CHECK:     v41: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v43: mem):
// CHECK:     v44: ptr = symbol_addr @.Lstr.9
// CHECK:     v45: int:i64 = iconst 42
// CHECK:     v46: ptr = symbol_addr @.Lstr.9
// CHECK:     v47: int:i64 = iconst 42
// CHECK:     v48: int:i32 = iconst 1
// CHECK:     v49: int:i64 = iconst 63
// CHECK:     v50: int:i64 = and v48, v49
// CHECK:     v51: int:i64 = shl v47:u64, v50
// CHECK:     v52: int:u64 = zext v51, 64
// CHECK:     v53: int:i64 = iconst 1
// CHECK:     v54: int:i64 = or v52, v53:u64
// CHECK:     v55: int:u64 = zext v54, 64
// CHECK:     v56: mem = store.8 v44, v6, v43
// CHECK:     v57: int:i64 = iconst 8
// CHECK:     v58: ptr = ptradd v6, v57
// CHECK:     v59: mem = store.8 v55, v58, v56
// CHECK:     v60: int:i64 = load.8 v6, v59
// CHECK:     v61: int:i64 = iconst 8
// CHECK:     v62: ptr = ptradd v6, v61
// CHECK:     v63: int:i64 = load.8 v62, v59
// CHECK:     v64: ptr = symbol_addr @.Lloc.11
// CHECK:     v65: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v66: mem = call v65(v60, v63, v64), v59
// CHECK:     v67: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb5(v69: mem):
// CHECK:     v70: mem = store.atomic.seqcst v2, v1, v69
// CHECK:     br bb7(v70)
// CHECK:
// CHECK:   bb6(v72: mem):
// CHECK:     v73: mem = store.atomic.seqcst v2, v1, v72
// CHECK:     br bb7(v73)
// CHECK:
// CHECK:   bb7(v75: mem):
// CHECK:     ret v75
// CHECK:
// CHECK:   bb8(v77: mem):
// CHECK:     v78: int:i64 = iconst 1
// CHECK:     v79: bool = icmp.eq v8, v78
// CHECK:     brif v79, bb5(v77), bb9(v77)
// CHECK:
// CHECK:   bb9(v81: mem):
// CHECK:     v82: int:i64 = iconst 2
// CHECK:     v83: bool = icmp.eq v8, v82
// CHECK:     brif v83, bb4(v81), bb10(v81)
// CHECK:
// CHECK:   bb10(v85: mem):
// CHECK:     v86: int:i64 = iconst 3
// CHECK:     v87: bool = icmp.eq v8, v86
// CHECK:     brif v87, bb3(v85), bb11(v85)
// CHECK:
// CHECK:   bb11(v89: mem):
// CHECK:     v90: int:i64 = iconst 4
// CHECK:     v91: bool = icmp.eq v8, v90
// CHECK:     brif v91, bb2(v89), bb1(v89)
// CHECK: }
// CHECK:
// CHECK: fn std::sync::atomic::atomic_compare_exchange(_1: *mut T, _2: T, _3: T, _4: std::sync::atomic::Ordering, _5: std::sync::atomic::Ordering) -> std::result::Result<T, T> {
// CHECK:     debug dst => _1;
// CHECK:     debug old => _2;
// CHECK:     debug new => _3;
// CHECK:     debug success => _4;
// CHECK:     debug failure => _5;
// CHECK:     let mut _0: std::result::Result<T, T>;
// CHECK:     let _6: T;
// CHECK:     let _7: bool;
// CHECK:     let mut _8: (T, bool);
// CHECK:     let mut _9: isize;
// CHECK:     let mut _10: isize;
// CHECK:     let mut _11: isize;
// CHECK:     let mut _12: isize;
// CHECK:     let mut _13: isize;
// CHECK:     let mut _14: isize;
// CHECK:     let mut _15: isize;
// CHECK:     let _16: !;
// CHECK:     let mut _17: std::fmt::Arguments<'_>;
// CHECK:     let _18: !;
// CHECK:     let mut _19: std::fmt::Arguments<'_>;
// CHECK:     let mut _20: &str;
// CHECK:     let mut _29: &str;
// CHECK:     scope 1 {
// CHECK:         debug val => _6;
// CHECK:         debug ok => _7;
// CHECK:     }
// CHECK:     scope 2 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _20;
// CHECK:         let mut _21: std::ptr::NonNull<u8>;
// CHECK:         let mut _22: *const u8;
// CHECK:         let mut _23: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _24: usize;
// CHECK:         let mut _25: usize;
// CHECK:         let mut _26: usize;
// CHECK:         scope 3 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _20;
// CHECK:             let mut _27: *const str;
// CHECK:         }
// CHECK:         scope 4 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _20;
// CHECK:             let _28: &[u8];
// CHECK:             scope 5 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _20;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 6 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _29;
// CHECK:         let mut _30: std::ptr::NonNull<u8>;
// CHECK:         let mut _31: *const u8;
// CHECK:         let mut _32: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _33: usize;
// CHECK:         let mut _34: usize;
// CHECK:         let mut _35: usize;
// CHECK:         scope 7 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _29;
// CHECK:             let mut _36: *const str;
// CHECK:         }
// CHECK:         scope 8 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _29;
// CHECK:             let _37: &[u8];
// CHECK:             scope 9 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _29;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_8);
// CHECK:         _14 = discriminant(_4);
// CHECK:         switchInt(move _14) -> [0: bb2, 1: bb4, 2: bb3, 3: bb5, 4: bb6, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _15 = discriminant(_5);
// CHECK:         switchInt(move _15) -> [1: bb8, 3: bb9, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _9 = discriminant(_5);
// CHECK:         switchInt(move _9) -> [0: bb24, 2: bb23, 4: bb22, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _10 = discriminant(_5);
// CHECK:         switchInt(move _10) -> [0: bb21, 2: bb20, 4: bb19, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _11 = discriminant(_5);
// CHECK:         switchInt(move _11) -> [0: bb18, 2: bb17, 4: bb16, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _12 = discriminant(_5);
// CHECK:         switchInt(move _12) -> [0: bb15, 2: bb14, 4: bb13, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _13 = discriminant(_5);
// CHECK:         switchInt(move _13) -> [0: bb12, 2: bb11, 4: bb10, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_20);
// CHECK:         _20 = const "there is no such thing as a release failure ordering";
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_27);
// CHECK:         _27 = &raw const (*_20);
// CHECK:         _22 = copy _27 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_27);
// CHECK:         _21 = copy _22 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_22);
// CHECK:         StorageLive(_23);
// CHECK:         StorageLive(_24);
// CHECK:         StorageLive(_25);
// CHECK:         StorageLive(_26);
// CHECK:         StorageLive(_28);
// CHECK:         _28 = const "there is no such thing as a release failure ordering" as &[u8] (Transmute);
// CHECK:         _26 = PtrMetadata(copy _28);
// CHECK:         StorageDead(_28);
// CHECK:         _25 = Shl(move _26, const 1_i32);
// CHECK:         StorageDead(_26);
// CHECK:         _24 = BitOr(move _25, const 1_usize);
// CHECK:         StorageDead(_25);
// CHECK:         _23 = move _24 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_24);
// CHECK:         _19 = std::fmt::Arguments::<'_> { template: move _21, args: move _23 };
// CHECK:         StorageDead(_23);
// CHECK:         StorageDead(_21);
// CHECK:         StorageDead(_20);
// CHECK:         _18 = std::rt::panic_fmt(move _19) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         StorageLive(_17);
// CHECK:         StorageLive(_29);
// CHECK:         _29 = const "there is no such thing as an acquire-release failure ordering";
// CHECK:         StorageLive(_30);
// CHECK:         StorageLive(_31);
// CHECK:         StorageLive(_36);
// CHECK:         _36 = &raw const (*_29);
// CHECK:         _31 = copy _36 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_36);
// CHECK:         _30 = copy _31 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_31);
// CHECK:         StorageLive(_32);
// CHECK:         StorageLive(_33);
// CHECK:         StorageLive(_34);
// CHECK:         StorageLive(_35);
// CHECK:         StorageLive(_37);
// CHECK:         _37 = const "there is no such thing as an acquire-release failure ordering" as &[u8] (Transmute);
// CHECK:         _35 = PtrMetadata(copy _37);
// CHECK:         StorageDead(_37);
// CHECK:         _34 = Shl(move _35, const 1_i32);
// CHECK:         StorageDead(_35);
// CHECK:         _33 = BitOr(move _34, const 1_usize);
// CHECK:         StorageDead(_34);
// CHECK:         _32 = move _33 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_33);
// CHECK:         _17 = std::fmt::Arguments::<'_> { template: move _30, args: move _32 };
// CHECK:         StorageDead(_32);
// CHECK:         StorageDead(_30);
// CHECK:         StorageDead(_29);
// CHECK:         _16 = std::rt::panic_fmt(move _17) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::SeqCst, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::SeqCst, std::intrinsics::AtomicOrdering::Acquire>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::SeqCst, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::AcqRel, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::AcqRel, std::intrinsics::AtomicOrdering::Acquire>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::AcqRel, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb16: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Release, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb17: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Release, std::intrinsics::AtomicOrdering::Acquire>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb18: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Release, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb19: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Acquire, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb20: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Acquire, std::intrinsics::AtomicOrdering::Acquire>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb21: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Acquire, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb22: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Relaxed, std::intrinsics::AtomicOrdering::SeqCst>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb23: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Relaxed, std::intrinsics::AtomicOrdering::Acquire>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb24: {
// CHECK:         _8 = std::intrinsics::atomic_cxchg::<T, std::intrinsics::AtomicOrdering::Relaxed, std::intrinsics::AtomicOrdering::Relaxed>(move _1, move _2, move _3) -> [return: bb25, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb25: {
// CHECK:         _6 = copy (_8.0: T);
// CHECK:         _7 = copy (_8.1: bool);
// CHECK:         StorageDead(_8);
// CHECK:         switchInt(copy _7) -> [0: bb27, otherwise: bb26];
// CHECK:     }
// CHECK:
// CHECK:     bb26: {
// CHECK:         _0 = std::result::Result::<T, T>::Ok(copy _6);
// CHECK:         goto -> bb28;
// CHECK:     }
// CHECK:
// CHECK:     bb27: {
// CHECK:         _0 = std::result::Result::<T, T>::Err(copy _6);
// CHECK:         goto -> bb28;
// CHECK:     }
// CHECK:
// CHECK:     bb28: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc31 (size: 61, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 6e 20 61 63 71 │  thing as an acq
// CHECK:     0x20 │ 75 69 72 65 2d 72 65 6c 65 61 73 65 20 66 61 69 │ uire-release fai
// CHECK:     0x30 │ 6c 75 72 65 20 6f 72 64 65 72 69 6e 67          │ lure ordering
// CHECK: }
// CHECK:
// CHECK: alloc30 (size: 52, align: 1) {
// CHECK:     0x00 │ 74 68 65 72 65 20 69 73 20 6e 6f 20 73 75 63 68 │ there is no such
// CHECK:     0x10 │ 20 74 68 69 6e 67 20 61 73 20 61 20 72 65 6c 65 │  thing as a rele
// CHECK:     0x20 │ 61 73 65 20 66 61 69 6c 75 72 65 20 6f 72 64 65 │ ase failure orde
// CHECK:     0x30 │ 72 69 6e 67                                     │ ring
// CHECK: }
// CHECK: data @.Lstr.12 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lloc_file.13 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.14 = "..." relocs [0: @.Lloc_file.13]
// CHECK: data @.Lstr.15 = "there is no such thing as a release failure ordering"
// CHECK: data @.Lloc_file.16 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.17 = "..." relocs [0: @.Lloc_file.16]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic23atomic_compare_exchangemEC$HASH_10atomic_ops(ptr, int:u32, int:u32, int:i8, int:i8) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: int:i8 = param 3
// CHECK:     v5: ptr = stack_slot 1 align 1
// CHECK:     v6: int:i8 = param 4
// CHECK:     v7: ptr = stack_slot 1 align 1
// CHECK:     v8: mem = store.1 v4, v5, v0
// CHECK:     v9: mem = store.1 v6, v7, v8
// CHECK:     v10: ptr = stack_slot 8 align 4
// CHECK:     v11: ptr = stack_slot 8 align 4
// CHECK:     v12: ptr = stack_slot 16 align 8
// CHECK:     v13: ptr = stack_slot 16 align 8
// CHECK:     v14: int:i8 = load.1 v5, v9
// CHECK:     v15: int:i64 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb17(v9), bb29(v9)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: int:i8 = load.1 v7, v18
// CHECK:     v20: int:i64 = iconst 0
// CHECK:     v21: bool = icmp.eq v19, v20
// CHECK:     brif v21, bb4(v18), bb33(v18)
// CHECK:
// CHECK:   bb2(v23: mem):
// CHECK:     v24: mem, v25: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v23
// CHECK:     v26: bool = icmp.eq v25, v2
// CHECK:     v27: mem = store.4 v25, v10, v24
// CHECK:     v28: int:i64 = iconst 4
// CHECK:     v29: ptr = ptradd v10, v28
// CHECK:     v30: mem = store.1 v26, v29, v27
// CHECK:     br bb25(v30)
// CHECK:
// CHECK:   bb3(v32: mem):
// CHECK:     v33: mem, v34: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v32
// CHECK:     v35: bool = icmp.eq v34, v2
// CHECK:     v36: mem = store.4 v34, v10, v33
// CHECK:     v37: int:i64 = iconst 4
// CHECK:     v38: ptr = ptradd v10, v37
// CHECK:     v39: mem = store.1 v35, v38, v36
// CHECK:     br bb25(v39)
// CHECK:
// CHECK:   bb4(v41: mem):
// CHECK:     v42: mem, v43: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v41
// CHECK:     v44: bool = icmp.eq v43, v2
// CHECK:     v45: mem = store.4 v43, v10, v42
// CHECK:     v46: int:i64 = iconst 4
// CHECK:     v47: ptr = ptradd v10, v46
// CHECK:     v48: mem = store.1 v44, v47, v45
// CHECK:     br bb25(v48)
// CHECK:
// CHECK:   bb5(v50: mem):
// CHECK:     v51: int:i8 = load.1 v7, v50
// CHECK:     v52: int:i64 = iconst 0
// CHECK:     v53: bool = icmp.eq v51, v52
// CHECK:     brif v53, bb8(v50), bb35(v50)
// CHECK:
// CHECK:   bb6(v55: mem):
// CHECK:     v56: mem, v57: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v55
// CHECK:     v58: bool = icmp.eq v57, v2
// CHECK:     v59: mem = store.4 v57, v10, v56
// CHECK:     v60: int:i64 = iconst 4
// CHECK:     v61: ptr = ptradd v10, v60
// CHECK:     v62: mem = store.1 v58, v61, v59
// CHECK:     br bb25(v62)
// CHECK:
// CHECK:   bb7(v64: mem):
// CHECK:     v65: mem, v66: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v64
// CHECK:     v67: bool = icmp.eq v66, v2
// CHECK:     v68: mem = store.4 v66, v10, v65
// CHECK:     v69: int:i64 = iconst 4
// CHECK:     v70: ptr = ptradd v10, v69
// CHECK:     v71: mem = store.1 v67, v70, v68
// CHECK:     br bb25(v71)
// CHECK:
// CHECK:   bb8(v73: mem):
// CHECK:     v74: mem, v75: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v73
// CHECK:     v76: bool = icmp.eq v75, v2
// CHECK:     v77: mem = store.4 v75, v10, v74
// CHECK:     v78: int:i64 = iconst 4
// CHECK:     v79: ptr = ptradd v10, v78
// CHECK:     v80: mem = store.1 v76, v79, v77
// CHECK:     br bb25(v80)
// CHECK:
// CHECK:   bb9(v82: mem):
// CHECK:     v83: int:i8 = load.1 v7, v82
// CHECK:     v84: int:i64 = iconst 0
// CHECK:     v85: bool = icmp.eq v83, v84
// CHECK:     brif v85, bb12(v82), bb37(v82)
// CHECK:
// CHECK:   bb10(v87: mem):
// CHECK:     v88: mem, v89: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v87
// CHECK:     v90: bool = icmp.eq v89, v2
// CHECK:     v91: mem = store.4 v89, v10, v88
// CHECK:     v92: int:i64 = iconst 4
// CHECK:     v93: ptr = ptradd v10, v92
// CHECK:     v94: mem = store.1 v90, v93, v91
// CHECK:     br bb25(v94)
// CHECK:
// CHECK:   bb11(v96: mem):
// CHECK:     v97: mem, v98: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v96
// CHECK:     v99: bool = icmp.eq v98, v2
// CHECK:     v100: mem = store.4 v98, v10, v97
// CHECK:     v101: int:i64 = iconst 4
// CHECK:     v102: ptr = ptradd v10, v101
// CHECK:     v103: mem = store.1 v99, v102, v100
// CHECK:     br bb25(v103)
// CHECK:
// CHECK:   bb12(v105: mem):
// CHECK:     v106: mem, v107: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v105
// CHECK:     v108: bool = icmp.eq v107, v2
// CHECK:     v109: mem = store.4 v107, v10, v106
// CHECK:     v110: int:i64 = iconst 4
// CHECK:     v111: ptr = ptradd v10, v110
// CHECK:     v112: mem = store.1 v108, v111, v109
// CHECK:     br bb25(v112)
// CHECK:
// CHECK:   bb13(v114: mem):
// CHECK:     v115: int:i8 = load.1 v7, v114
// CHECK:     v116: int:i64 = iconst 0
// CHECK:     v117: bool = icmp.eq v115, v116
// CHECK:     brif v117, bb16(v114), bb39(v114)
// CHECK:
// CHECK:   bb14(v119: mem):
// CHECK:     v120: mem, v121: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v119
// CHECK:     v122: bool = icmp.eq v121, v2
// CHECK:     v123: mem = store.4 v121, v10, v120
// CHECK:     v124: int:i64 = iconst 4
// CHECK:     v125: ptr = ptradd v10, v124
// CHECK:     v126: mem = store.1 v122, v125, v123
// CHECK:     br bb25(v126)
// CHECK:
// CHECK:   bb15(v128: mem):
// CHECK:     v129: mem, v130: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v128
// CHECK:     v131: bool = icmp.eq v130, v2
// CHECK:     v132: mem = store.4 v130, v10, v129
// CHECK:     v133: int:i64 = iconst 4
// CHECK:     v134: ptr = ptradd v10, v133
// CHECK:     v135: mem = store.1 v131, v134, v132
// CHECK:     br bb25(v135)
// CHECK:
// CHECK:   bb16(v137: mem):
// CHECK:     v138: mem, v139: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v137
// CHECK:     v140: bool = icmp.eq v139, v2
// CHECK:     v141: mem = store.4 v139, v10, v138
// CHECK:     v142: int:i64 = iconst 4
// CHECK:     v143: ptr = ptradd v10, v142
// CHECK:     v144: mem = store.1 v140, v143, v141
// CHECK:     br bb25(v144)
// CHECK:
// CHECK:   bb17(v146: mem):
// CHECK:     v147: int:i8 = load.1 v7, v146
// CHECK:     v148: int:i64 = iconst 0
// CHECK:     v149: bool = icmp.eq v147, v148
// CHECK:     brif v149, bb24(v146), bb41(v146)
// CHECK:
// CHECK:   bb18(v151: mem):
// CHECK:     v152: int:i8 = load.1 v7, v151
// CHECK:     v153: int:i64 = iconst 1
// CHECK:     v154: bool = icmp.eq v152, v153
// CHECK:     brif v154, bb21(v151), bb43(v151)
// CHECK:
// CHECK:   bb19(v156: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb20(v158: mem):
// CHECK:     v159: ptr = symbol_addr @.Lstr.12
// CHECK:     v160: int:i64 = iconst 61
// CHECK:     v161: ptr = symbol_addr @.Lstr.12
// CHECK:     v162: int:i64 = iconst 61
// CHECK:     v163: int:i32 = iconst 1
// CHECK:     v164: int:i64 = iconst 63
// CHECK:     v165: int:i64 = and v163, v164
// CHECK:     v166: int:i64 = shl v162:u64, v165
// CHECK:     v167: int:u64 = zext v166, 64
// CHECK:     v168: int:i64 = iconst 1
// CHECK:     v169: int:i64 = or v167, v168:u64
// CHECK:     v170: int:u64 = zext v169, 64
// CHECK:     v171: mem = store.8 v159, v12, v158
// CHECK:     v172: int:i64 = iconst 8
// CHECK:     v173: ptr = ptradd v12, v172
// CHECK:     v174: mem = store.8 v170, v173, v171
// CHECK:     v175: int:i64 = load.8 v12, v174
// CHECK:     v176: int:i64 = iconst 8
// CHECK:     v177: ptr = ptradd v12, v176
// CHECK:     v178: int:i64 = load.8 v177, v174
// CHECK:     v179: ptr = symbol_addr @.Lloc.14
// CHECK:     v180: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v181: mem = call v180(v175, v178, v179), v174
// CHECK:     v182: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb21(v184: mem):
// CHECK:     v185: ptr = symbol_addr @.Lstr.15
// CHECK:     v186: int:i64 = iconst 52
// CHECK:     v187: ptr = symbol_addr @.Lstr.15
// CHECK:     v188: int:i64 = iconst 52
// CHECK:     v189: int:i32 = iconst 1
// CHECK:     v190: int:i64 = iconst 63
// CHECK:     v191: int:i64 = and v189, v190
// CHECK:     v192: int:i64 = shl v188:u64, v191
// CHECK:     v193: int:u64 = zext v192, 64
// CHECK:     v194: int:i64 = iconst 1
// CHECK:     v195: int:i64 = or v193, v194:u64
// CHECK:     v196: int:u64 = zext v195, 64
// CHECK:     v197: mem = store.8 v185, v13, v184
// CHECK:     v198: int:i64 = iconst 8
// CHECK:     v199: ptr = ptradd v13, v198
// CHECK:     v200: mem = store.8 v196, v199, v197
// CHECK:     v201: int:i64 = load.8 v13, v200
// CHECK:     v202: int:i64 = iconst 8
// CHECK:     v203: ptr = ptradd v13, v202
// CHECK:     v204: int:i64 = load.8 v203, v200
// CHECK:     v205: ptr = symbol_addr @.Lloc.17
// CHECK:     v206: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v207: mem = call v206(v201, v204, v205), v200
// CHECK:     v208: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb22(v210: mem):
// CHECK:     v211: mem, v212: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v210
// CHECK:     v213: bool = icmp.eq v212, v2
// CHECK:     v214: mem = store.4 v212, v10, v211
// CHECK:     v215: int:i64 = iconst 4
// CHECK:     v216: ptr = ptradd v10, v215
// CHECK:     v217: mem = store.1 v213, v216, v214
// CHECK:     br bb25(v217)
// CHECK:
// CHECK:   bb23(v219: mem):
// CHECK:     v220: mem, v221: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v219
// CHECK:     v222: bool = icmp.eq v221, v2
// CHECK:     v223: mem = store.4 v221, v10, v220
// CHECK:     v224: int:i64 = iconst 4
// CHECK:     v225: ptr = ptradd v10, v224
// CHECK:     v226: mem = store.1 v222, v225, v223
// CHECK:     br bb25(v226)
// CHECK:
// CHECK:   bb24(v228: mem):
// CHECK:     v229: mem, v230: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v228
// CHECK:     v231: bool = icmp.eq v230, v2
// CHECK:     v232: mem = store.4 v230, v10, v229
// CHECK:     v233: int:i64 = iconst 4
// CHECK:     v234: ptr = ptradd v10, v233
// CHECK:     v235: mem = store.1 v231, v234, v232
// CHECK:     br bb25(v235)
// CHECK:
// CHECK:   bb25(v237: mem):
// CHECK:     v238: int:u32 = load.4 v10, v237
// CHECK:     v239: int:i64 = iconst 4
// CHECK:     v240: ptr = ptradd v10, v239
// CHECK:     v241: bool = load.1 v240, v237
// CHECK:     v242: int:u64 = iconst 1
// CHECK:     v243: int:u64 = iconst 0
// CHECK:     v244: int:u64 = select v241, v242, v243
// CHECK:     v245: int:i64 = iconst 255
// CHECK:     v246: int:u64 = and v244, v245
// CHECK:     v247: int:i8 = iconst 0
// CHECK:     v248: bool = icmp.eq v246, v247
// CHECK:     brif v248, bb27(v237), bb26(v237)
// CHECK:
// CHECK:   bb26(v250: mem):
// CHECK:     v251: int:i64 = iconst 0
// CHECK:     v252: mem = store.8 v251, v11, v250
// CHECK:     v253: int:i64 = iconst 4
// CHECK:     v254: ptr = ptradd v11, v253
// CHECK:     v255: mem = store.4 v238, v254, v252
// CHECK:     v256: int:i64 = iconst 0
// CHECK:     v257: mem = store.4 v256, v11, v255
// CHECK:     br bb28(v257)
// CHECK:
// CHECK:   bb27(v259: mem):
// CHECK:     v260: int:i64 = iconst 0
// CHECK:     v261: mem = store.8 v260, v11, v259
// CHECK:     v262: int:i64 = iconst 4
// CHECK:     v263: ptr = ptradd v11, v262
// CHECK:     v264: mem = store.4 v238, v263, v261
// CHECK:     v265: int:i64 = iconst 1
// CHECK:     v266: mem = store.4 v265, v11, v264
// CHECK:     br bb28(v266)
// CHECK:
// CHECK:   bb28(v268: mem):
// CHECK:     v269: int:i32 = load.4 v11, v268
// CHECK:     v270: int:i64 = iconst 4
// CHECK:     v271: ptr = ptradd v11, v270
// CHECK:     v272: int:i32 = load.4 v271, v268
// CHECK:     ret v269, v272, v268
// CHECK:
// CHECK:   bb29(v274: mem):
// CHECK:     v275: int:i64 = iconst 1
// CHECK:     v276: bool = icmp.eq v14, v275
// CHECK:     brif v276, bb13(v274), bb30(v274)
// CHECK:
// CHECK:   bb30(v278: mem):
// CHECK:     v279: int:i64 = iconst 2
// CHECK:     v280: bool = icmp.eq v14, v279
// CHECK:     brif v280, bb9(v278), bb31(v278)
// CHECK:
// CHECK:   bb31(v282: mem):
// CHECK:     v283: int:i64 = iconst 3
// CHECK:     v284: bool = icmp.eq v14, v283
// CHECK:     brif v284, bb5(v282), bb32(v282)
// CHECK:
// CHECK:   bb32(v286: mem):
// CHECK:     v287: int:i64 = iconst 4
// CHECK:     v288: bool = icmp.eq v14, v287
// CHECK:     brif v288, bb1(v286), bb19(v286)
// CHECK:
// CHECK:   bb33(v290: mem):
// CHECK:     v291: int:i64 = iconst 2
// CHECK:     v292: bool = icmp.eq v19, v291
// CHECK:     brif v292, bb3(v290), bb34(v290)
// CHECK:
// CHECK:   bb34(v294: mem):
// CHECK:     v295: int:i64 = iconst 4
// CHECK:     v296: bool = icmp.eq v19, v295
// CHECK:     brif v296, bb2(v294), bb18(v294)
// CHECK:
// CHECK:   bb35(v298: mem):
// CHECK:     v299: int:i64 = iconst 2
// CHECK:     v300: bool = icmp.eq v51, v299
// CHECK:     brif v300, bb7(v298), bb36(v298)
// CHECK:
// CHECK:   bb36(v302: mem):
// CHECK:     v303: int:i64 = iconst 4
// CHECK:     v304: bool = icmp.eq v51, v303
// CHECK:     brif v304, bb6(v302), bb18(v302)
// CHECK:
// CHECK:   bb37(v306: mem):
// CHECK:     v307: int:i64 = iconst 2
// CHECK:     v308: bool = icmp.eq v83, v307
// CHECK:     brif v308, bb11(v306), bb38(v306)
// CHECK:
// CHECK:   bb38(v310: mem):
// CHECK:     v311: int:i64 = iconst 4
// CHECK:     v312: bool = icmp.eq v83, v311
// CHECK:     brif v312, bb10(v310), bb18(v310)
// CHECK:
// CHECK:   bb39(v314: mem):
// CHECK:     v315: int:i64 = iconst 2
// CHECK:     v316: bool = icmp.eq v115, v315
// CHECK:     brif v316, bb15(v314), bb40(v314)
// CHECK:
// CHECK:   bb40(v318: mem):
// CHECK:     v319: int:i64 = iconst 4
// CHECK:     v320: bool = icmp.eq v115, v319
// CHECK:     brif v320, bb14(v318), bb18(v318)
// CHECK:
// CHECK:   bb41(v322: mem):
// CHECK:     v323: int:i64 = iconst 2
// CHECK:     v324: bool = icmp.eq v147, v323
// CHECK:     brif v324, bb23(v322), bb42(v322)
// CHECK:
// CHECK:   bb42(v326: mem):
// CHECK:     v327: int:i64 = iconst 4
// CHECK:     v328: bool = icmp.eq v147, v327
// CHECK:     brif v328, bb22(v326), bb18(v326)
// CHECK:
// CHECK:   bb43(v330: mem):
// CHECK:     v331: int:i64 = iconst 3
// CHECK:     v332: bool = icmp.eq v152, v331
// CHECK:     brif v332, bb20(v330), bb19(v330)
// CHECK: }
// CHECK:
// CHECK: fn atomic_compare_exchange(_1: &std::sync::atomic::Atomic<u32>, _2: u32, _3: u32) -> std::result::Result<u32, u32> {
// CHECK:     debug ptr => _1;
// CHECK:     debug expected => _2;
// CHECK:     debug new => _3;
// CHECK:     let mut _0: std::result::Result<u32, u32>;
// CHECK:     scope 1 (inlined std::sync::atomic::Atomic::<u32>::compare_exchange) {
// CHECK:         let mut _4: *mut u32;
// CHECK:         scope 2 (inlined std::sync::atomic::Atomic::<u32>::as_ptr) {
// CHECK:             scope 3 (inlined std::cell::UnsafeCell::<std::sync::atomic::private::Align4<u32>>::get) {
// CHECK:                 let mut _5: *const std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>;
// CHECK:             }
// CHECK:             scope 4 (inlined std::ptr::mut_ptr::<impl *mut std::sync::atomic::private::Align4<u32>>::cast::<u32>) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _5 = &raw const ((*_1).0: std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>);
// CHECK:         _4 = copy _5 as *mut u32 (PtrToPtr);
// CHECK:         _0 = std::sync::atomic::atomic_compare_exchange::<u32>(move _4, move _2, move _3, const std::sync::atomic::Ordering::SeqCst, const std::sync::atomic::Ordering::SeqCst) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @atomic_compare_exchange(ptr, int:u32, int:u32) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = stack_slot 8 align 4
// CHECK:     v5: int:i8 = iconst 4
// CHECK:     v6: int:i8 = iconst 4
// CHECK:     v7: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic23atomic_compare_exchangemEC$HASH_10atomic_ops
// CHECK:     v8: mem, v9: int:i32 = call v7(v1, v2, v3, v5, v6), v0 -> int:i32
// CHECK:     v10: mem = store.4 v9, v4, v8
// CHECK:     v11: int:i32 = call_ret2 v8
// CHECK:     v12: int:i64 = iconst 4
// CHECK:     v13: ptr = ptradd v4, v12
// CHECK:     v14: mem = store.4 v11, v13, v10
// CHECK:     br bb1(v14)
// CHECK:
// CHECK:   bb1(v16: mem):
// CHECK:     v17: int:i32 = load.4 v4, v16
// CHECK:     v18: int:i64 = iconst 4
// CHECK:     v19: ptr = ptradd v4, v18
// CHECK:     v20: int:i32 = load.4 v19, v16
// CHECK:     ret v17, v20, v16
// CHECK: }
// CHECK:
// CHECK: fn atomic_fetch_add(_1: &std::sync::atomic::Atomic<u32>, _2: u32) -> u32 {
// CHECK:     debug ptr => _1;
// CHECK:     debug val => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined std::sync::atomic::Atomic::<u32>::fetch_add) {
// CHECK:         let mut _3: *mut u32;
// CHECK:         scope 2 (inlined std::sync::atomic::Atomic::<u32>::as_ptr) {
// CHECK:             scope 3 (inlined std::cell::UnsafeCell::<std::sync::atomic::private::Align4<u32>>::get) {
// CHECK:                 let mut _4: *const std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>;
// CHECK:             }
// CHECK:             scope 4 (inlined std::ptr::mut_ptr::<impl *mut std::sync::atomic::private::Align4<u32>>::cast::<u32>) {
// CHECK:             }
// CHECK:         }
// CHECK:         scope 5 (inlined std::sync::atomic::atomic_add::<u32, u32>) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _4 = &raw const ((*_1).0: std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>);
// CHECK:         _3 = copy _4 as *mut u32 (PtrToPtr);
// CHECK:         _0 = std::intrinsics::atomic_xadd::<u32, u32, std::intrinsics::AtomicOrdering::AcqRel>(move _3, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @atomic_fetch_add(ptr, int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: mem, v4: int:i32 = rmw.add.seqcst v1, v2, v0
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
// CHECK: fn atomic_load_relaxed(_1: &std::sync::atomic::Atomic<u32>) -> u32 {
// CHECK:     debug ptr => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined std::sync::atomic::Atomic::<u32>::load) {
// CHECK:         let mut _2: *const u32;
// CHECK:         scope 2 (inlined std::sync::atomic::Atomic::<u32>::as_ptr) {
// CHECK:             scope 3 (inlined std::cell::UnsafeCell::<std::sync::atomic::private::Align4<u32>>::get) {
// CHECK:                 let mut _3: *const std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>;
// CHECK:             }
// CHECK:             scope 4 (inlined std::ptr::mut_ptr::<impl *mut std::sync::atomic::private::Align4<u32>>::cast::<u32>) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = &raw const ((*_1).0: std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>);
// CHECK:         _2 = copy _3 as *const u32 (PtrToPtr);
// CHECK:         _0 = std::sync::atomic::atomic_load::<u32>(move _2, const std::sync::atomic::Ordering::Relaxed) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @atomic_load_relaxed(ptr) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i8 = iconst 0
// CHECK:     v3: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic11atomic_loadmEC$HASH_10atomic_ops
// CHECK:     v4: mem, v5: int:u32 = call v3(v1, v2), v0 -> int:u32
// CHECK:     br bb1(v4)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:
// CHECK: fn atomic_store_release(_1: &std::sync::atomic::Atomic<u32>, _2: u32) -> () {
// CHECK:     debug ptr => _1;
// CHECK:     debug val => _2;
// CHECK:     let mut _0: ();
// CHECK:     scope 1 (inlined std::sync::atomic::Atomic::<u32>::store) {
// CHECK:         let _3: ();
// CHECK:         let mut _4: *mut u32;
// CHECK:         scope 2 (inlined std::sync::atomic::Atomic::<u32>::as_ptr) {
// CHECK:             scope 3 (inlined std::cell::UnsafeCell::<std::sync::atomic::private::Align4<u32>>::get) {
// CHECK:                 let mut _5: *const std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>;
// CHECK:             }
// CHECK:             scope 4 (inlined std::ptr::mut_ptr::<impl *mut std::sync::atomic::private::Align4<u32>>::cast::<u32>) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _5 = &raw const ((*_1).0: std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>);
// CHECK:         _4 = copy _5 as *mut u32 (PtrToPtr);
// CHECK:         _3 = std::sync::atomic::atomic_store::<u32>(move _4, move _2, const std::sync::atomic::Ordering::Release) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @atomic_store_release(ptr, int:u32) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:i8 = iconst 1
// CHECK:     v4: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic12atomic_storemEC$HASH_10atomic_ops
// CHECK:     v5: mem = call v4(v1, v2, v3), v0
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v8
// CHECK: }
// CHECK:
// CHECK: fn atomic_swap(_1: &std::sync::atomic::Atomic<u32>, _2: u32) -> u32 {
// CHECK:     debug ptr => _1;
// CHECK:     debug val => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined std::sync::atomic::Atomic::<u32>::swap) {
// CHECK:         let mut _3: *mut u32;
// CHECK:         scope 2 (inlined std::sync::atomic::Atomic::<u32>::as_ptr) {
// CHECK:             scope 3 (inlined std::cell::UnsafeCell::<std::sync::atomic::private::Align4<u32>>::get) {
// CHECK:                 let mut _4: *const std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>;
// CHECK:             }
// CHECK:             scope 4 (inlined std::ptr::mut_ptr::<impl *mut std::sync::atomic::private::Align4<u32>>::cast::<u32>) {
// CHECK:             }
// CHECK:         }
// CHECK:         scope 5 (inlined std::sync::atomic::atomic_swap::<u32>) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _4 = &raw const ((*_1).0: std::cell::UnsafeCell<std::sync::atomic::private::Align4<u32>>);
// CHECK:         _3 = copy _4 as *mut u32 (PtrToPtr);
// CHECK:         _0 = std::intrinsics::atomic_xchg::<u32, std::intrinsics::AtomicOrdering::Acquire>(move _3, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @atomic_swap(ptr, int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: mem, v4: int:i32 = rmw.xchg.seqcst v1, v2, v0
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:

use std::sync::atomic::{AtomicU32, Ordering};

#[no_mangle]
pub fn atomic_load_relaxed(ptr: &AtomicU32) -> u32 {
    // Should use load.atomic.relaxed, not plain load
    ptr.load(Ordering::Relaxed)
}

#[no_mangle]
pub fn atomic_store_release(ptr: &AtomicU32, val: u32) {
    // Should use store.atomic.release, not plain store
    ptr.store(val, Ordering::Release);
}

#[no_mangle]
pub fn atomic_fetch_add(ptr: &AtomicU32, val: u32) -> u32 {
    // Should use rmw.add.acqrel, not load + add + store
    ptr.fetch_add(val, Ordering::AcqRel)
}

#[no_mangle]
pub fn atomic_compare_exchange(ptr: &AtomicU32, expected: u32, new: u32) -> Result<u32, u32> {
    // Should use cmpxchg.seqcst.seqcst, not load + icmp + select + store
    ptr.compare_exchange(expected, new, Ordering::SeqCst, Ordering::SeqCst)
}

#[no_mangle]
pub fn atomic_swap(ptr: &AtomicU32, val: u32) -> u32 {
    // Should use rmw.xchg.acquire, not load + store
    ptr.swap(val, Ordering::Acquire)
}
