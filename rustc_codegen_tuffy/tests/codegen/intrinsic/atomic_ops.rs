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
// CHECK: data @.Lstr.1 = "there is no such thing as an acquire-release load"
// CHECK: data @.Lloc_file.2 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.3 = "..." relocs [0: @.Lloc_file.2]
// CHECK: data @.Lstr.4 = "there is no such thing as a release load"
// CHECK: data @.Lstr.5 = "there is no such thing as a release load"
// CHECK: data @.Lloc_file.6 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.7 = "..." relocs [0: @.Lloc_file.6]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic11atomic_loadmEC$HASH_10atomic_ops(ptr, int:i8) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i8 = param 1
// CHECK:     v3: ptr = stack_slot 1
// CHECK:     v4: mem = store.1 v2, v3, v0
// CHECK:     v5: ptr = stack_slot 4
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: int:i8 = load.1 v3, v4
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v4), bb8(v4)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.0
// CHECK:     v18: int:i64 = iconst 49
// CHECK:     v19: mem = store.8 v17, v8, v16
// CHECK:     v20: int:i64 = iconst 8
// CHECK:     v21: ptr = ptradd v8, v20
// CHECK:     v22: mem = store.8 v18, v21, v19
// CHECK:     v23: int:i64 = iconst 49
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v8, v24
// CHECK:     v26: mem = store.8 v23, v25, v22
// CHECK:     v27: ptr = load.8 v8, v26
// CHECK:     v28: int:i64 = iconst 8
// CHECK:     v29: ptr = ptradd v8, v28
// CHECK:     v30: int:i64 = load.8 v29, v26
// CHECK:     v31: ptr = stack_slot 16
// CHECK:     v32: mem = store.8 v27, v31, v26
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v31, v33
// CHECK:     v35: mem = store.8 v30, v34, v32
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v8, v36
// CHECK:     v38: int:i64 = load.8 v37, v35
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v31, v39
// CHECK:     v41: mem = store.8 v38, v40, v35
// CHECK:     v42: ptr = load.8 v31, v41
// CHECK:     v43: ptr = symbol_addr @.Lstr.1
// CHECK:     v44: int:i64 = iconst 49
// CHECK:     v45: int:i32 = iconst 1
// CHECK:     v46: int:i64 = iconst 63
// CHECK:     v47: int:i64 = and v45, v46
// CHECK:     v48: int:i64 = shl v44:u64, v47
// CHECK:     v49: int:u64 = zext v48, 64
// CHECK:     v50: int:i64 = iconst 1
// CHECK:     v51: int:i64 = or v49, v50:u64
// CHECK:     v52: int:u64 = zext v51, 64
// CHECK:     v53: mem = store.8 v42, v7, v41
// CHECK:     v54: int:i64 = iconst 8
// CHECK:     v55: ptr = ptradd v7, v54
// CHECK:     v56: mem = store.8 v52, v55, v53
// CHECK:     v57: int:i64 = load.8 v7, v56
// CHECK:     v58: int:i64 = iconst 8
// CHECK:     v59: ptr = ptradd v7, v58
// CHECK:     v60: int:i64 = load.8 v59, v56
// CHECK:     v61: ptr = symbol_addr @.Lloc.3
// CHECK:     v62: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v63: mem = call v62(v57, v60, v61), v56
// CHECK:     v64: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v66: mem):
// CHECK:     v67: ptr = symbol_addr @.Lstr.4
// CHECK:     v68: int:i64 = iconst 40
// CHECK:     v69: mem = store.8 v67, v9, v66
// CHECK:     v70: int:i64 = iconst 8
// CHECK:     v71: ptr = ptradd v9, v70
// CHECK:     v72: mem = store.8 v68, v71, v69
// CHECK:     v73: int:i64 = iconst 40
// CHECK:     v74: int:i64 = iconst 8
// CHECK:     v75: ptr = ptradd v9, v74
// CHECK:     v76: mem = store.8 v73, v75, v72
// CHECK:     v77: ptr = load.8 v9, v76
// CHECK:     v78: int:i64 = iconst 8
// CHECK:     v79: ptr = ptradd v9, v78
// CHECK:     v80: int:i64 = load.8 v79, v76
// CHECK:     v81: ptr = stack_slot 16
// CHECK:     v82: mem = store.8 v77, v81, v76
// CHECK:     v83: int:i64 = iconst 8
// CHECK:     v84: ptr = ptradd v81, v83
// CHECK:     v85: mem = store.8 v80, v84, v82
// CHECK:     v86: int:i64 = iconst 8
// CHECK:     v87: ptr = ptradd v9, v86
// CHECK:     v88: int:i64 = load.8 v87, v85
// CHECK:     v89: int:i64 = iconst 8
// CHECK:     v90: ptr = ptradd v81, v89
// CHECK:     v91: mem = store.8 v88, v90, v85
// CHECK:     v92: ptr = load.8 v81, v91
// CHECK:     v93: ptr = symbol_addr @.Lstr.5
// CHECK:     v94: int:i64 = iconst 40
// CHECK:     v95: int:i32 = iconst 1
// CHECK:     v96: int:i64 = iconst 63
// CHECK:     v97: int:i64 = and v95, v96
// CHECK:     v98: int:i64 = shl v94:u64, v97
// CHECK:     v99: int:u64 = zext v98, 64
// CHECK:     v100: int:i64 = iconst 1
// CHECK:     v101: int:i64 = or v99, v100:u64
// CHECK:     v102: int:u64 = zext v101, 64
// CHECK:     v103: mem = store.8 v92, v6, v91
// CHECK:     v104: int:i64 = iconst 8
// CHECK:     v105: ptr = ptradd v6, v104
// CHECK:     v106: mem = store.8 v102, v105, v103
// CHECK:     v107: int:i64 = load.8 v6, v106
// CHECK:     v108: int:i64 = iconst 8
// CHECK:     v109: ptr = ptradd v6, v108
// CHECK:     v110: int:i64 = load.8 v109, v106
// CHECK:     v111: ptr = symbol_addr @.Lloc.7
// CHECK:     v112: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v113: mem = call v112(v107, v110, v111), v106
// CHECK:     v114: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v116: mem):
// CHECK:     v117: mem, v118: int:i64 = load.atomic.seqcst v1, v116
// CHECK:     v119: mem = store.4 v118, v5, v117
// CHECK:     br bb7(v119)
// CHECK:
// CHECK:   bb5(v121: mem):
// CHECK:     v122: mem, v123: int:i64 = load.atomic.seqcst v1, v121
// CHECK:     v124: mem = store.4 v123, v5, v122
// CHECK:     br bb7(v124)
// CHECK:
// CHECK:   bb6(v126: mem):
// CHECK:     v127: mem, v128: int:i64 = load.atomic.seqcst v1, v126
// CHECK:     v129: mem = store.4 v128, v5, v127
// CHECK:     br bb7(v129)
// CHECK:
// CHECK:   bb7(v131: mem):
// CHECK:     v132: int:u32 = load.4 v5, v131
// CHECK:     ret v132, v131
// CHECK:
// CHECK:   bb8(v134: mem):
// CHECK:     v135: int:i64 = iconst 1
// CHECK:     v136: bool = icmp.eq v10, v135
// CHECK:     brif v136, bb3(v134), bb9(v134)
// CHECK:
// CHECK:   bb9(v138: mem):
// CHECK:     v139: int:i64 = iconst 2
// CHECK:     v140: bool = icmp.eq v10, v139
// CHECK:     brif v140, bb5(v138), bb10(v138)
// CHECK:
// CHECK:   bb10(v142: mem):
// CHECK:     v143: int:i64 = iconst 3
// CHECK:     v144: bool = icmp.eq v10, v143
// CHECK:     brif v144, bb2(v142), bb11(v142)
// CHECK:
// CHECK:   bb11(v146: mem):
// CHECK:     v147: int:i64 = iconst 4
// CHECK:     v148: bool = icmp.eq v10, v147
// CHECK:     brif v148, bb4(v146), bb1(v146)
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
// CHECK: data @.Lstr.8 = "there is no such thing as an acquire-release store"
// CHECK: data @.Lstr.9 = "there is no such thing as an acquire-release store"
// CHECK: data @.Lloc_file.10 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.11 = "..." relocs [0: @.Lloc_file.10]
// CHECK: data @.Lstr.12 = "there is no such thing as an acquire store"
// CHECK: data @.Lstr.13 = "there is no such thing as an acquire store"
// CHECK: data @.Lloc_file.14 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.15 = "..." relocs [0: @.Lloc_file.14]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic12atomic_storemEC$HASH_10atomic_ops(ptr, int:u32, int:i8) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:i8 = param 2
// CHECK:     v4: ptr = stack_slot 1
// CHECK:     v5: mem = store.1 v3, v4, v0
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: int:i8 = load.1 v4, v5
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v5), bb8(v5)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.8
// CHECK:     v18: int:i64 = iconst 50
// CHECK:     v19: mem = store.8 v17, v8, v16
// CHECK:     v20: int:i64 = iconst 8
// CHECK:     v21: ptr = ptradd v8, v20
// CHECK:     v22: mem = store.8 v18, v21, v19
// CHECK:     v23: int:i64 = iconst 50
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v8, v24
// CHECK:     v26: mem = store.8 v23, v25, v22
// CHECK:     v27: ptr = load.8 v8, v26
// CHECK:     v28: int:i64 = iconst 8
// CHECK:     v29: ptr = ptradd v8, v28
// CHECK:     v30: int:i64 = load.8 v29, v26
// CHECK:     v31: ptr = stack_slot 16
// CHECK:     v32: mem = store.8 v27, v31, v26
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v31, v33
// CHECK:     v35: mem = store.8 v30, v34, v32
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v8, v36
// CHECK:     v38: int:i64 = load.8 v37, v35
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v31, v39
// CHECK:     v41: mem = store.8 v38, v40, v35
// CHECK:     v42: ptr = load.8 v31, v41
// CHECK:     v43: ptr = symbol_addr @.Lstr.9
// CHECK:     v44: int:i64 = iconst 50
// CHECK:     v45: int:i32 = iconst 1
// CHECK:     v46: int:i64 = iconst 63
// CHECK:     v47: int:i64 = and v45, v46
// CHECK:     v48: int:i64 = shl v44:u64, v47
// CHECK:     v49: int:u64 = zext v48, 64
// CHECK:     v50: int:i64 = iconst 1
// CHECK:     v51: int:i64 = or v49, v50:u64
// CHECK:     v52: int:u64 = zext v51, 64
// CHECK:     v53: mem = store.8 v42, v7, v41
// CHECK:     v54: int:i64 = iconst 8
// CHECK:     v55: ptr = ptradd v7, v54
// CHECK:     v56: mem = store.8 v52, v55, v53
// CHECK:     v57: int:i64 = load.8 v7, v56
// CHECK:     v58: int:i64 = iconst 8
// CHECK:     v59: ptr = ptradd v7, v58
// CHECK:     v60: int:i64 = load.8 v59, v56
// CHECK:     v61: ptr = symbol_addr @.Lloc.11
// CHECK:     v62: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v63: mem = call v62(v57, v60, v61), v56
// CHECK:     v64: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v66: mem):
// CHECK:     v67: ptr = symbol_addr @.Lstr.12
// CHECK:     v68: int:i64 = iconst 42
// CHECK:     v69: mem = store.8 v67, v9, v66
// CHECK:     v70: int:i64 = iconst 8
// CHECK:     v71: ptr = ptradd v9, v70
// CHECK:     v72: mem = store.8 v68, v71, v69
// CHECK:     v73: int:i64 = iconst 42
// CHECK:     v74: int:i64 = iconst 8
// CHECK:     v75: ptr = ptradd v9, v74
// CHECK:     v76: mem = store.8 v73, v75, v72
// CHECK:     v77: ptr = load.8 v9, v76
// CHECK:     v78: int:i64 = iconst 8
// CHECK:     v79: ptr = ptradd v9, v78
// CHECK:     v80: int:i64 = load.8 v79, v76
// CHECK:     v81: ptr = stack_slot 16
// CHECK:     v82: mem = store.8 v77, v81, v76
// CHECK:     v83: int:i64 = iconst 8
// CHECK:     v84: ptr = ptradd v81, v83
// CHECK:     v85: mem = store.8 v80, v84, v82
// CHECK:     v86: int:i64 = iconst 8
// CHECK:     v87: ptr = ptradd v9, v86
// CHECK:     v88: int:i64 = load.8 v87, v85
// CHECK:     v89: int:i64 = iconst 8
// CHECK:     v90: ptr = ptradd v81, v89
// CHECK:     v91: mem = store.8 v88, v90, v85
// CHECK:     v92: ptr = load.8 v81, v91
// CHECK:     v93: ptr = symbol_addr @.Lstr.13
// CHECK:     v94: int:i64 = iconst 42
// CHECK:     v95: int:i32 = iconst 1
// CHECK:     v96: int:i64 = iconst 63
// CHECK:     v97: int:i64 = and v95, v96
// CHECK:     v98: int:i64 = shl v94:u64, v97
// CHECK:     v99: int:u64 = zext v98, 64
// CHECK:     v100: int:i64 = iconst 1
// CHECK:     v101: int:i64 = or v99, v100:u64
// CHECK:     v102: int:u64 = zext v101, 64
// CHECK:     v103: mem = store.8 v92, v6, v91
// CHECK:     v104: int:i64 = iconst 8
// CHECK:     v105: ptr = ptradd v6, v104
// CHECK:     v106: mem = store.8 v102, v105, v103
// CHECK:     v107: int:i64 = load.8 v6, v106
// CHECK:     v108: int:i64 = iconst 8
// CHECK:     v109: ptr = ptradd v6, v108
// CHECK:     v110: int:i64 = load.8 v109, v106
// CHECK:     v111: ptr = symbol_addr @.Lloc.15
// CHECK:     v112: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v113: mem = call v112(v107, v110, v111), v106
// CHECK:     v114: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v116: mem):
// CHECK:     v117: mem = store.atomic.seqcst v2, v1, v116
// CHECK:     br bb7(v117)
// CHECK:
// CHECK:   bb5(v119: mem):
// CHECK:     v120: mem = store.atomic.seqcst v2, v1, v119
// CHECK:     br bb7(v120)
// CHECK:
// CHECK:   bb6(v122: mem):
// CHECK:     v123: mem = store.atomic.seqcst v2, v1, v122
// CHECK:     br bb7(v123)
// CHECK:
// CHECK:   bb7(v125: mem):
// CHECK:     ret v125
// CHECK:
// CHECK:   bb8(v127: mem):
// CHECK:     v128: int:i64 = iconst 1
// CHECK:     v129: bool = icmp.eq v10, v128
// CHECK:     brif v129, bb5(v127), bb9(v127)
// CHECK:
// CHECK:   bb9(v131: mem):
// CHECK:     v132: int:i64 = iconst 2
// CHECK:     v133: bool = icmp.eq v10, v132
// CHECK:     brif v133, bb3(v131), bb10(v131)
// CHECK:
// CHECK:   bb10(v135: mem):
// CHECK:     v136: int:i64 = iconst 3
// CHECK:     v137: bool = icmp.eq v10, v136
// CHECK:     brif v137, bb2(v135), bb11(v135)
// CHECK:
// CHECK:   bb11(v139: mem):
// CHECK:     v140: int:i64 = iconst 4
// CHECK:     v141: bool = icmp.eq v10, v140
// CHECK:     brif v141, bb4(v139), bb1(v139)
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
// CHECK: data @.Lstr.16 = "there is no such thing as a release failure ordering"
// CHECK: data @.Lstr.17 = "there is no such thing as a release failure ordering"
// CHECK: data @.Lloc_file.18 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.19 = "..." relocs [0: @.Lloc_file.18]
// CHECK: data @.Lstr.20 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lstr.21 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lloc_file.22 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.23 = "..." relocs [0: @.Lloc_file.22]
// CHECK: func @_RINvNtNtC$HASH_4core4sync6atomic23atomic_compare_exchangemEC$HASH_10atomic_ops(ptr, int:u32, int:u32, int:i8, int:i8) -> int:i64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: int:i8 = param 3
// CHECK:     v5: ptr = stack_slot 1
// CHECK:     v6: int:i8 = param 4
// CHECK:     v7: ptr = stack_slot 1
// CHECK:     v8: mem = store.1 v4, v5, v0
// CHECK:     v9: mem = store.1 v6, v7, v8
// CHECK:     v10: ptr = stack_slot 8
// CHECK:     v11: ptr = stack_slot 8
// CHECK:     v12: ptr = stack_slot 16
// CHECK:     v13: ptr = stack_slot 16
// CHECK:     v14: ptr = stack_slot 16
// CHECK:     v15: ptr = stack_slot 16
// CHECK:     v16: int:i8 = load.1 v5, v9
// CHECK:     v17: int:i64 = iconst 0
// CHECK:     v18: bool = icmp.eq v16, v17
// CHECK:     brif v18, bb2(v9), bb29(v9)
// CHECK:
// CHECK:   bb1(v20: mem):
// CHECK:     v21: int:i8 = load.1 v7, v20
// CHECK:     v22: int:i64 = iconst 1
// CHECK:     v23: bool = icmp.eq v21, v22
// CHECK:     brif v23, bb8(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26: int:i8 = load.1 v7, v25
// CHECK:     v27: int:i64 = iconst 0
// CHECK:     v28: bool = icmp.eq v26, v27
// CHECK:     brif v28, bb24(v25), bb34(v25)
// CHECK:
// CHECK:   bb3(v30: mem):
// CHECK:     v31: int:i8 = load.1 v7, v30
// CHECK:     v32: int:i64 = iconst 0
// CHECK:     v33: bool = icmp.eq v31, v32
// CHECK:     brif v33, bb21(v30), bb36(v30)
// CHECK:
// CHECK:   bb4(v35: mem):
// CHECK:     v36: int:i8 = load.1 v7, v35
// CHECK:     v37: int:i64 = iconst 0
// CHECK:     v38: bool = icmp.eq v36, v37
// CHECK:     brif v38, bb18(v35), bb38(v35)
// CHECK:
// CHECK:   bb5(v40: mem):
// CHECK:     v41: int:i8 = load.1 v7, v40
// CHECK:     v42: int:i64 = iconst 0
// CHECK:     v43: bool = icmp.eq v41, v42
// CHECK:     brif v43, bb15(v40), bb40(v40)
// CHECK:
// CHECK:   bb6(v45: mem):
// CHECK:     v46: int:i8 = load.1 v7, v45
// CHECK:     v47: int:i64 = iconst 0
// CHECK:     v48: bool = icmp.eq v46, v47
// CHECK:     brif v48, bb12(v45), bb42(v45)
// CHECK:
// CHECK:   bb7(v50: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v52: mem):
// CHECK:     v53: ptr = symbol_addr @.Lstr.16
// CHECK:     v54: int:i64 = iconst 52
// CHECK:     v55: mem = store.8 v53, v14, v52
// CHECK:     v56: int:i64 = iconst 8
// CHECK:     v57: ptr = ptradd v14, v56
// CHECK:     v58: mem = store.8 v54, v57, v55
// CHECK:     v59: int:i64 = iconst 52
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v14, v60
// CHECK:     v62: mem = store.8 v59, v61, v58
// CHECK:     v63: ptr = load.8 v14, v62
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v14, v64
// CHECK:     v66: int:i64 = load.8 v65, v62
// CHECK:     v67: ptr = stack_slot 16
// CHECK:     v68: mem = store.8 v63, v67, v62
// CHECK:     v69: int:i64 = iconst 8
// CHECK:     v70: ptr = ptradd v67, v69
// CHECK:     v71: mem = store.8 v66, v70, v68
// CHECK:     v72: int:i64 = iconst 8
// CHECK:     v73: ptr = ptradd v14, v72
// CHECK:     v74: int:i64 = load.8 v73, v71
// CHECK:     v75: int:i64 = iconst 8
// CHECK:     v76: ptr = ptradd v67, v75
// CHECK:     v77: mem = store.8 v74, v76, v71
// CHECK:     v78: ptr = load.8 v67, v77
// CHECK:     v79: ptr = symbol_addr @.Lstr.17
// CHECK:     v80: int:i64 = iconst 52
// CHECK:     v81: int:i32 = iconst 1
// CHECK:     v82: int:i64 = iconst 63
// CHECK:     v83: int:i64 = and v81, v82
// CHECK:     v84: int:i64 = shl v80:u64, v83
// CHECK:     v85: int:u64 = zext v84, 64
// CHECK:     v86: int:i64 = iconst 1
// CHECK:     v87: int:i64 = or v85, v86:u64
// CHECK:     v88: int:u64 = zext v87, 64
// CHECK:     v89: mem = store.8 v78, v13, v77
// CHECK:     v90: int:i64 = iconst 8
// CHECK:     v91: ptr = ptradd v13, v90
// CHECK:     v92: mem = store.8 v88, v91, v89
// CHECK:     v93: int:i64 = load.8 v13, v92
// CHECK:     v94: int:i64 = iconst 8
// CHECK:     v95: ptr = ptradd v13, v94
// CHECK:     v96: int:i64 = load.8 v95, v92
// CHECK:     v97: ptr = symbol_addr @.Lloc.19
// CHECK:     v98: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v99: mem = call v98(v93, v96, v97), v92
// CHECK:     v100: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb9(v102: mem):
// CHECK:     v103: ptr = symbol_addr @.Lstr.20
// CHECK:     v104: int:i64 = iconst 61
// CHECK:     v105: mem = store.8 v103, v15, v102
// CHECK:     v106: int:i64 = iconst 8
// CHECK:     v107: ptr = ptradd v15, v106
// CHECK:     v108: mem = store.8 v104, v107, v105
// CHECK:     v109: int:i64 = iconst 61
// CHECK:     v110: int:i64 = iconst 8
// CHECK:     v111: ptr = ptradd v15, v110
// CHECK:     v112: mem = store.8 v109, v111, v108
// CHECK:     v113: ptr = load.8 v15, v112
// CHECK:     v114: int:i64 = iconst 8
// CHECK:     v115: ptr = ptradd v15, v114
// CHECK:     v116: int:i64 = load.8 v115, v112
// CHECK:     v117: ptr = stack_slot 16
// CHECK:     v118: mem = store.8 v113, v117, v112
// CHECK:     v119: int:i64 = iconst 8
// CHECK:     v120: ptr = ptradd v117, v119
// CHECK:     v121: mem = store.8 v116, v120, v118
// CHECK:     v122: int:i64 = iconst 8
// CHECK:     v123: ptr = ptradd v15, v122
// CHECK:     v124: int:i64 = load.8 v123, v121
// CHECK:     v125: int:i64 = iconst 8
// CHECK:     v126: ptr = ptradd v117, v125
// CHECK:     v127: mem = store.8 v124, v126, v121
// CHECK:     v128: ptr = load.8 v117, v127
// CHECK:     v129: ptr = symbol_addr @.Lstr.21
// CHECK:     v130: int:i64 = iconst 61
// CHECK:     v131: int:i32 = iconst 1
// CHECK:     v132: int:i64 = iconst 63
// CHECK:     v133: int:i64 = and v131, v132
// CHECK:     v134: int:i64 = shl v130:u64, v133
// CHECK:     v135: int:u64 = zext v134, 64
// CHECK:     v136: int:i64 = iconst 1
// CHECK:     v137: int:i64 = or v135, v136:u64
// CHECK:     v138: int:u64 = zext v137, 64
// CHECK:     v139: mem = store.8 v128, v12, v127
// CHECK:     v140: int:i64 = iconst 8
// CHECK:     v141: ptr = ptradd v12, v140
// CHECK:     v142: mem = store.8 v138, v141, v139
// CHECK:     v143: int:i64 = load.8 v12, v142
// CHECK:     v144: int:i64 = iconst 8
// CHECK:     v145: ptr = ptradd v12, v144
// CHECK:     v146: int:i64 = load.8 v145, v142
// CHECK:     v147: ptr = symbol_addr @.Lloc.23
// CHECK:     v148: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v149: mem = call v148(v143, v146, v147), v142
// CHECK:     v150: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v152: mem):
// CHECK:     v153: mem, v154: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v152
// CHECK:     v155: bool = icmp.eq v154, v2
// CHECK:     v156: mem = store.4 v154, v10, v153
// CHECK:     v157: int:i64 = iconst 4
// CHECK:     v158: ptr = ptradd v10, v157
// CHECK:     v159: mem = store.1 v155, v158, v156
// CHECK:     br bb25(v159)
// CHECK:
// CHECK:   bb11(v161: mem):
// CHECK:     v162: mem, v163: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v161
// CHECK:     v164: bool = icmp.eq v163, v2
// CHECK:     v165: mem = store.4 v163, v10, v162
// CHECK:     v166: int:i64 = iconst 4
// CHECK:     v167: ptr = ptradd v10, v166
// CHECK:     v168: mem = store.1 v164, v167, v165
// CHECK:     br bb25(v168)
// CHECK:
// CHECK:   bb12(v170: mem):
// CHECK:     v171: mem, v172: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v170
// CHECK:     v173: bool = icmp.eq v172, v2
// CHECK:     v174: mem = store.4 v172, v10, v171
// CHECK:     v175: int:i64 = iconst 4
// CHECK:     v176: ptr = ptradd v10, v175
// CHECK:     v177: mem = store.1 v173, v176, v174
// CHECK:     br bb25(v177)
// CHECK:
// CHECK:   bb13(v179: mem):
// CHECK:     v180: mem, v181: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v179
// CHECK:     v182: bool = icmp.eq v181, v2
// CHECK:     v183: mem = store.4 v181, v10, v180
// CHECK:     v184: int:i64 = iconst 4
// CHECK:     v185: ptr = ptradd v10, v184
// CHECK:     v186: mem = store.1 v182, v185, v183
// CHECK:     br bb25(v186)
// CHECK:
// CHECK:   bb14(v188: mem):
// CHECK:     v189: mem, v190: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v188
// CHECK:     v191: bool = icmp.eq v190, v2
// CHECK:     v192: mem = store.4 v190, v10, v189
// CHECK:     v193: int:i64 = iconst 4
// CHECK:     v194: ptr = ptradd v10, v193
// CHECK:     v195: mem = store.1 v191, v194, v192
// CHECK:     br bb25(v195)
// CHECK:
// CHECK:   bb15(v197: mem):
// CHECK:     v198: mem, v199: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v197
// CHECK:     v200: bool = icmp.eq v199, v2
// CHECK:     v201: mem = store.4 v199, v10, v198
// CHECK:     v202: int:i64 = iconst 4
// CHECK:     v203: ptr = ptradd v10, v202
// CHECK:     v204: mem = store.1 v200, v203, v201
// CHECK:     br bb25(v204)
// CHECK:
// CHECK:   bb16(v206: mem):
// CHECK:     v207: mem, v208: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v206
// CHECK:     v209: bool = icmp.eq v208, v2
// CHECK:     v210: mem = store.4 v208, v10, v207
// CHECK:     v211: int:i64 = iconst 4
// CHECK:     v212: ptr = ptradd v10, v211
// CHECK:     v213: mem = store.1 v209, v212, v210
// CHECK:     br bb25(v213)
// CHECK:
// CHECK:   bb17(v215: mem):
// CHECK:     v216: mem, v217: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v215
// CHECK:     v218: bool = icmp.eq v217, v2
// CHECK:     v219: mem = store.4 v217, v10, v216
// CHECK:     v220: int:i64 = iconst 4
// CHECK:     v221: ptr = ptradd v10, v220
// CHECK:     v222: mem = store.1 v218, v221, v219
// CHECK:     br bb25(v222)
// CHECK:
// CHECK:   bb18(v224: mem):
// CHECK:     v225: mem, v226: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v224
// CHECK:     v227: bool = icmp.eq v226, v2
// CHECK:     v228: mem = store.4 v226, v10, v225
// CHECK:     v229: int:i64 = iconst 4
// CHECK:     v230: ptr = ptradd v10, v229
// CHECK:     v231: mem = store.1 v227, v230, v228
// CHECK:     br bb25(v231)
// CHECK:
// CHECK:   bb19(v233: mem):
// CHECK:     v234: mem, v235: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v233
// CHECK:     v236: bool = icmp.eq v235, v2
// CHECK:     v237: mem = store.4 v235, v10, v234
// CHECK:     v238: int:i64 = iconst 4
// CHECK:     v239: ptr = ptradd v10, v238
// CHECK:     v240: mem = store.1 v236, v239, v237
// CHECK:     br bb25(v240)
// CHECK:
// CHECK:   bb20(v242: mem):
// CHECK:     v243: mem, v244: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v242
// CHECK:     v245: bool = icmp.eq v244, v2
// CHECK:     v246: mem = store.4 v244, v10, v243
// CHECK:     v247: int:i64 = iconst 4
// CHECK:     v248: ptr = ptradd v10, v247
// CHECK:     v249: mem = store.1 v245, v248, v246
// CHECK:     br bb25(v249)
// CHECK:
// CHECK:   bb21(v251: mem):
// CHECK:     v252: mem, v253: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v251
// CHECK:     v254: bool = icmp.eq v253, v2
// CHECK:     v255: mem = store.4 v253, v10, v252
// CHECK:     v256: int:i64 = iconst 4
// CHECK:     v257: ptr = ptradd v10, v256
// CHECK:     v258: mem = store.1 v254, v257, v255
// CHECK:     br bb25(v258)
// CHECK:
// CHECK:   bb22(v260: mem):
// CHECK:     v261: mem, v262: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v260
// CHECK:     v263: bool = icmp.eq v262, v2
// CHECK:     v264: mem = store.4 v262, v10, v261
// CHECK:     v265: int:i64 = iconst 4
// CHECK:     v266: ptr = ptradd v10, v265
// CHECK:     v267: mem = store.1 v263, v266, v264
// CHECK:     br bb25(v267)
// CHECK:
// CHECK:   bb23(v269: mem):
// CHECK:     v270: mem, v271: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v269
// CHECK:     v272: bool = icmp.eq v271, v2
// CHECK:     v273: mem = store.4 v271, v10, v270
// CHECK:     v274: int:i64 = iconst 4
// CHECK:     v275: ptr = ptradd v10, v274
// CHECK:     v276: mem = store.1 v272, v275, v273
// CHECK:     br bb25(v276)
// CHECK:
// CHECK:   bb24(v278: mem):
// CHECK:     v279: mem, v280: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v278
// CHECK:     v281: bool = icmp.eq v280, v2
// CHECK:     v282: mem = store.4 v280, v10, v279
// CHECK:     v283: int:i64 = iconst 4
// CHECK:     v284: ptr = ptradd v10, v283
// CHECK:     v285: mem = store.1 v281, v284, v282
// CHECK:     br bb25(v285)
// CHECK:
// CHECK:   bb25(v287: mem):
// CHECK:     v288: int:i32 = load.4 v10, v287
// CHECK:     v289: int:i64 = iconst 4
// CHECK:     v290: ptr = ptradd v10, v289
// CHECK:     v291: bool = load.1 v290, v287
// CHECK:     v292: int:u64 = iconst 1
// CHECK:     v293: int:u64 = iconst 0
// CHECK:     v294: int:u64 = select v291, v292, v293
// CHECK:     v295: int:i64 = iconst 255
// CHECK:     v296: int:u64 = and v294, v295
// CHECK:     v297: int:i8 = iconst 0
// CHECK:     v298: bool = icmp.eq v296, v297
// CHECK:     brif v298, bb27(v287), bb26(v287)
// CHECK:
// CHECK:   bb26(v300: mem):
// CHECK:     v301: int:i64 = iconst 0
// CHECK:     v302: mem = store.8 v301, v11, v300
// CHECK:     v303: int:i64 = iconst 4
// CHECK:     v304: ptr = ptradd v11, v303
// CHECK:     v305: mem = store.4 v288, v304, v302
// CHECK:     v306: int:i64 = iconst 0
// CHECK:     v307: mem = store.4 v306, v11, v305
// CHECK:     br bb28(v307)
// CHECK:
// CHECK:   bb27(v309: mem):
// CHECK:     v310: int:i64 = iconst 0
// CHECK:     v311: mem = store.8 v310, v11, v309
// CHECK:     v312: int:i64 = iconst 4
// CHECK:     v313: ptr = ptradd v11, v312
// CHECK:     v314: mem = store.4 v288, v313, v311
// CHECK:     v315: int:i64 = iconst 1
// CHECK:     v316: mem = store.4 v315, v11, v314
// CHECK:     br bb28(v316)
// CHECK:
// CHECK:   bb28(v318: mem):
// CHECK:     v319: int:i32 = load.4 v11, v318
// CHECK:     v320: int:i64 = iconst 4
// CHECK:     v321: ptr = ptradd v11, v320
// CHECK:     v322: int:i32 = load.4 v321, v318
// CHECK:     ret v319, v318
// CHECK:
// CHECK:   bb29(v324: mem):
// CHECK:     v325: int:i64 = iconst 1
// CHECK:     v326: bool = icmp.eq v16, v325
// CHECK:     brif v326, bb4(v324), bb30(v324)
// CHECK:
// CHECK:   bb30(v328: mem):
// CHECK:     v329: int:i64 = iconst 2
// CHECK:     v330: bool = icmp.eq v16, v329
// CHECK:     brif v330, bb3(v328), bb31(v328)
// CHECK:
// CHECK:   bb31(v332: mem):
// CHECK:     v333: int:i64 = iconst 3
// CHECK:     v334: bool = icmp.eq v16, v333
// CHECK:     brif v334, bb5(v332), bb32(v332)
// CHECK:
// CHECK:   bb32(v336: mem):
// CHECK:     v337: int:i64 = iconst 4
// CHECK:     v338: bool = icmp.eq v16, v337
// CHECK:     brif v338, bb6(v336), bb7(v336)
// CHECK:
// CHECK:   bb33(v340: mem):
// CHECK:     v341: int:i64 = iconst 3
// CHECK:     v342: bool = icmp.eq v21, v341
// CHECK:     brif v342, bb9(v340), bb7(v340)
// CHECK:
// CHECK:   bb34(v344: mem):
// CHECK:     v345: int:i64 = iconst 2
// CHECK:     v346: bool = icmp.eq v26, v345
// CHECK:     brif v346, bb23(v344), bb35(v344)
// CHECK:
// CHECK:   bb35(v348: mem):
// CHECK:     v349: int:i64 = iconst 4
// CHECK:     v350: bool = icmp.eq v26, v349
// CHECK:     brif v350, bb22(v348), bb1(v348)
// CHECK:
// CHECK:   bb36(v352: mem):
// CHECK:     v353: int:i64 = iconst 2
// CHECK:     v354: bool = icmp.eq v31, v353
// CHECK:     brif v354, bb20(v352), bb37(v352)
// CHECK:
// CHECK:   bb37(v356: mem):
// CHECK:     v357: int:i64 = iconst 4
// CHECK:     v358: bool = icmp.eq v31, v357
// CHECK:     brif v358, bb19(v356), bb1(v356)
// CHECK:
// CHECK:   bb38(v360: mem):
// CHECK:     v361: int:i64 = iconst 2
// CHECK:     v362: bool = icmp.eq v36, v361
// CHECK:     brif v362, bb17(v360), bb39(v360)
// CHECK:
// CHECK:   bb39(v364: mem):
// CHECK:     v365: int:i64 = iconst 4
// CHECK:     v366: bool = icmp.eq v36, v365
// CHECK:     brif v366, bb16(v364), bb1(v364)
// CHECK:
// CHECK:   bb40(v368: mem):
// CHECK:     v369: int:i64 = iconst 2
// CHECK:     v370: bool = icmp.eq v41, v369
// CHECK:     brif v370, bb14(v368), bb41(v368)
// CHECK:
// CHECK:   bb41(v372: mem):
// CHECK:     v373: int:i64 = iconst 4
// CHECK:     v374: bool = icmp.eq v41, v373
// CHECK:     brif v374, bb13(v372), bb1(v372)
// CHECK:
// CHECK:   bb42(v376: mem):
// CHECK:     v377: int:i64 = iconst 2
// CHECK:     v378: bool = icmp.eq v46, v377
// CHECK:     brif v378, bb11(v376), bb43(v376)
// CHECK:
// CHECK:   bb43(v380: mem):
// CHECK:     v381: int:i64 = iconst 4
// CHECK:     v382: bool = icmp.eq v46, v381
// CHECK:     brif v382, bb10(v380), bb1(v380)
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
// CHECK:     v4: ptr = stack_slot 8
// CHECK:     v5: mem = store.8 v1, v4, v0
// CHECK:     v6: ptr = load.8 v4, v5
// CHECK:     v7: int:i64 = iconst 4
// CHECK:     v8: int:i64 = iconst 4
// CHECK:     v9: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic23atomic_compare_exchangemEC$HASH_10atomic_ops
// CHECK:     v10: mem, v11: int:i32 = call v9(v6, v2, v3, v7, v8), v5 -> int:i32
// CHECK:     v12: ptr = stack_slot 8
// CHECK:     v13: mem = store.4 v11, v12, v10
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: int:i64 = iconst 4
// CHECK:     v16: ptr = ptradd v12, v15
// CHECK:     v17: mem = store.4 v14, v16, v13
// CHECK:     br bb1(v17)
// CHECK:
// CHECK:   bb1(v19: mem):
// CHECK:     v20: int:i32 = load.4 v12, v19
// CHECK:     v21: int:i64 = iconst 4
// CHECK:     v22: ptr = ptradd v12, v21
// CHECK:     v23: int:i32 = load.4 v22, v19
// CHECK:     ret v20, v19
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
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int:i64 = rmw.add.seqcst v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
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
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: mem = store.8 v1, v2, v0
// CHECK:     v4: ptr = load.8 v2, v3
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic11atomic_loadmEC$HASH_10atomic_ops
// CHECK:     v7: mem, v8: int:u32 = call v6(v4, v5), v3 -> int:u32
// CHECK:     br bb1(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v8, v10
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
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: int:i64 = iconst 1
// CHECK:     v7: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic12atomic_storemEC$HASH_10atomic_ops
// CHECK:     v8: mem = call v7(v5, v2, v6), v4
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     ret v11
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
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int:i64 = rmw.xchg.seqcst v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
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
