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
// CHECK:     v8: ptr = stack_slot 16 align 8
// CHECK:     v9: ptr = stack_slot 16 align 8
// CHECK:     v10: int:i8 = load.1 v3, v4
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v4), bb8(v4)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: mem, v18: int:i32 = load.atomic.seqcst v1, v16
// CHECK:     v19: mem = store.4 v18, v5, v17
// CHECK:     br bb7(v19)
// CHECK:
// CHECK:   bb3(v21: mem):
// CHECK:     v22: ptr = symbol_addr @.Lstr.0
// CHECK:     v23: int:i64 = iconst 49
// CHECK:     v24: mem = store.8 v22, v8, v21
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v8, v25
// CHECK:     v27: mem = store.8 v23, v26, v24
// CHECK:     v28: int:i64 = iconst 49
// CHECK:     v29: int:i64 = iconst 8
// CHECK:     v30: ptr = ptradd v8, v29
// CHECK:     v31: mem = store.8 v28, v30, v27
// CHECK:     v32: ptr = load.8 v8, v31
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v8, v33
// CHECK:     v35: int:i64 = load.8 v34, v31
// CHECK:     v36: ptr = stack_slot 16
// CHECK:     v37: mem = store.8 v32, v36, v31
// CHECK:     v38: int:i64 = iconst 8
// CHECK:     v39: ptr = ptradd v36, v38
// CHECK:     v40: mem = store.8 v35, v39, v37
// CHECK:     v41: int:i64 = iconst 8
// CHECK:     v42: ptr = ptradd v8, v41
// CHECK:     v43: int:i64 = load.8 v42, v40
// CHECK:     v44: int:i64 = iconst 8
// CHECK:     v45: ptr = ptradd v36, v44
// CHECK:     v46: mem = store.8 v43, v45, v40
// CHECK:     v47: ptr = load.8 v36, v46
// CHECK:     v48: ptr = symbol_addr @.Lstr.0
// CHECK:     v49: int:i64 = iconst 49
// CHECK:     v50: int:i32 = iconst 1
// CHECK:     v51: int:i64 = iconst 63
// CHECK:     v52: int:i64 = and v50, v51
// CHECK:     v53: int:i64 = shl v49:u64, v52
// CHECK:     v54: int:u64 = zext v53, 64
// CHECK:     v55: int:i64 = iconst 1
// CHECK:     v56: int:i64 = or v54, v55:u64
// CHECK:     v57: int:u64 = zext v56, 64
// CHECK:     v58: mem = store.8 v47, v7, v46
// CHECK:     v59: int:i64 = iconst 8
// CHECK:     v60: ptr = ptradd v7, v59
// CHECK:     v61: mem = store.8 v57, v60, v58
// CHECK:     v62: int:i64 = load.8 v7, v61
// CHECK:     v63: int:i64 = iconst 8
// CHECK:     v64: ptr = ptradd v7, v63
// CHECK:     v65: int:i64 = load.8 v64, v61
// CHECK:     v66: ptr = symbol_addr @.Lloc.2
// CHECK:     v67: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v68: mem = call v67(v62, v65, v66), v61
// CHECK:     v69: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v71: mem):
// CHECK:     v72: mem, v73: int:i32 = load.atomic.seqcst v1, v71
// CHECK:     v74: mem = store.4 v73, v5, v72
// CHECK:     br bb7(v74)
// CHECK:
// CHECK:   bb5(v76: mem):
// CHECK:     v77: ptr = symbol_addr @.Lstr.3
// CHECK:     v78: int:i64 = iconst 40
// CHECK:     v79: mem = store.8 v77, v9, v76
// CHECK:     v80: int:i64 = iconst 8
// CHECK:     v81: ptr = ptradd v9, v80
// CHECK:     v82: mem = store.8 v78, v81, v79
// CHECK:     v83: int:i64 = iconst 40
// CHECK:     v84: int:i64 = iconst 8
// CHECK:     v85: ptr = ptradd v9, v84
// CHECK:     v86: mem = store.8 v83, v85, v82
// CHECK:     v87: ptr = load.8 v9, v86
// CHECK:     v88: int:i64 = iconst 8
// CHECK:     v89: ptr = ptradd v9, v88
// CHECK:     v90: int:i64 = load.8 v89, v86
// CHECK:     v91: ptr = stack_slot 16
// CHECK:     v92: mem = store.8 v87, v91, v86
// CHECK:     v93: int:i64 = iconst 8
// CHECK:     v94: ptr = ptradd v91, v93
// CHECK:     v95: mem = store.8 v90, v94, v92
// CHECK:     v96: int:i64 = iconst 8
// CHECK:     v97: ptr = ptradd v9, v96
// CHECK:     v98: int:i64 = load.8 v97, v95
// CHECK:     v99: int:i64 = iconst 8
// CHECK:     v100: ptr = ptradd v91, v99
// CHECK:     v101: mem = store.8 v98, v100, v95
// CHECK:     v102: ptr = load.8 v91, v101
// CHECK:     v103: ptr = symbol_addr @.Lstr.3
// CHECK:     v104: int:i64 = iconst 40
// CHECK:     v105: int:i32 = iconst 1
// CHECK:     v106: int:i64 = iconst 63
// CHECK:     v107: int:i64 = and v105, v106
// CHECK:     v108: int:i64 = shl v104:u64, v107
// CHECK:     v109: int:u64 = zext v108, 64
// CHECK:     v110: int:i64 = iconst 1
// CHECK:     v111: int:i64 = or v109, v110:u64
// CHECK:     v112: int:u64 = zext v111, 64
// CHECK:     v113: mem = store.8 v102, v6, v101
// CHECK:     v114: int:i64 = iconst 8
// CHECK:     v115: ptr = ptradd v6, v114
// CHECK:     v116: mem = store.8 v112, v115, v113
// CHECK:     v117: int:i64 = load.8 v6, v116
// CHECK:     v118: int:i64 = iconst 8
// CHECK:     v119: ptr = ptradd v6, v118
// CHECK:     v120: int:i64 = load.8 v119, v116
// CHECK:     v121: ptr = symbol_addr @.Lloc.5
// CHECK:     v122: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v123: mem = call v122(v117, v120, v121), v116
// CHECK:     v124: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb6(v126: mem):
// CHECK:     v127: mem, v128: int:i32 = load.atomic.seqcst v1, v126
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
// CHECK:     brif v136, bb5(v134), bb9(v134)
// CHECK:
// CHECK:   bb9(v138: mem):
// CHECK:     v139: int:i64 = iconst 2
// CHECK:     v140: bool = icmp.eq v10, v139
// CHECK:     brif v140, bb4(v138), bb10(v138)
// CHECK:
// CHECK:   bb10(v142: mem):
// CHECK:     v143: int:i64 = iconst 3
// CHECK:     v144: bool = icmp.eq v10, v143
// CHECK:     brif v144, bb3(v142), bb11(v142)
// CHECK:
// CHECK:   bb11(v146: mem):
// CHECK:     v147: int:i64 = iconst 4
// CHECK:     v148: bool = icmp.eq v10, v147
// CHECK:     brif v148, bb2(v146), bb1(v146)
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
// CHECK:     v8: ptr = stack_slot 16 align 8
// CHECK:     v9: ptr = stack_slot 16 align 8
// CHECK:     v10: int:i8 = load.1 v4, v5
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v5), bb8(v5)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: mem = store.atomic.seqcst v2, v1, v16
// CHECK:     br bb7(v17)
// CHECK:
// CHECK:   bb3(v19: mem):
// CHECK:     v20: ptr = symbol_addr @.Lstr.6
// CHECK:     v21: int:i64 = iconst 50
// CHECK:     v22: mem = store.8 v20, v8, v19
// CHECK:     v23: int:i64 = iconst 8
// CHECK:     v24: ptr = ptradd v8, v23
// CHECK:     v25: mem = store.8 v21, v24, v22
// CHECK:     v26: int:i64 = iconst 50
// CHECK:     v27: int:i64 = iconst 8
// CHECK:     v28: ptr = ptradd v8, v27
// CHECK:     v29: mem = store.8 v26, v28, v25
// CHECK:     v30: ptr = load.8 v8, v29
// CHECK:     v31: int:i64 = iconst 8
// CHECK:     v32: ptr = ptradd v8, v31
// CHECK:     v33: int:i64 = load.8 v32, v29
// CHECK:     v34: ptr = stack_slot 16
// CHECK:     v35: mem = store.8 v30, v34, v29
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v34, v36
// CHECK:     v38: mem = store.8 v33, v37, v35
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v8, v39
// CHECK:     v41: int:i64 = load.8 v40, v38
// CHECK:     v42: int:i64 = iconst 8
// CHECK:     v43: ptr = ptradd v34, v42
// CHECK:     v44: mem = store.8 v41, v43, v38
// CHECK:     v45: ptr = load.8 v34, v44
// CHECK:     v46: ptr = symbol_addr @.Lstr.6
// CHECK:     v47: int:i64 = iconst 50
// CHECK:     v48: int:i32 = iconst 1
// CHECK:     v49: int:i64 = iconst 63
// CHECK:     v50: int:i64 = and v48, v49
// CHECK:     v51: int:i64 = shl v47:u64, v50
// CHECK:     v52: int:u64 = zext v51, 64
// CHECK:     v53: int:i64 = iconst 1
// CHECK:     v54: int:i64 = or v52, v53:u64
// CHECK:     v55: int:u64 = zext v54, 64
// CHECK:     v56: mem = store.8 v45, v7, v44
// CHECK:     v57: int:i64 = iconst 8
// CHECK:     v58: ptr = ptradd v7, v57
// CHECK:     v59: mem = store.8 v55, v58, v56
// CHECK:     v60: int:i64 = load.8 v7, v59
// CHECK:     v61: int:i64 = iconst 8
// CHECK:     v62: ptr = ptradd v7, v61
// CHECK:     v63: int:i64 = load.8 v62, v59
// CHECK:     v64: ptr = symbol_addr @.Lloc.8
// CHECK:     v65: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v66: mem = call v65(v60, v63, v64), v59
// CHECK:     v67: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v69: mem):
// CHECK:     v70: ptr = symbol_addr @.Lstr.9
// CHECK:     v71: int:i64 = iconst 42
// CHECK:     v72: mem = store.8 v70, v9, v69
// CHECK:     v73: int:i64 = iconst 8
// CHECK:     v74: ptr = ptradd v9, v73
// CHECK:     v75: mem = store.8 v71, v74, v72
// CHECK:     v76: int:i64 = iconst 42
// CHECK:     v77: int:i64 = iconst 8
// CHECK:     v78: ptr = ptradd v9, v77
// CHECK:     v79: mem = store.8 v76, v78, v75
// CHECK:     v80: ptr = load.8 v9, v79
// CHECK:     v81: int:i64 = iconst 8
// CHECK:     v82: ptr = ptradd v9, v81
// CHECK:     v83: int:i64 = load.8 v82, v79
// CHECK:     v84: ptr = stack_slot 16
// CHECK:     v85: mem = store.8 v80, v84, v79
// CHECK:     v86: int:i64 = iconst 8
// CHECK:     v87: ptr = ptradd v84, v86
// CHECK:     v88: mem = store.8 v83, v87, v85
// CHECK:     v89: int:i64 = iconst 8
// CHECK:     v90: ptr = ptradd v9, v89
// CHECK:     v91: int:i64 = load.8 v90, v88
// CHECK:     v92: int:i64 = iconst 8
// CHECK:     v93: ptr = ptradd v84, v92
// CHECK:     v94: mem = store.8 v91, v93, v88
// CHECK:     v95: ptr = load.8 v84, v94
// CHECK:     v96: ptr = symbol_addr @.Lstr.9
// CHECK:     v97: int:i64 = iconst 42
// CHECK:     v98: int:i32 = iconst 1
// CHECK:     v99: int:i64 = iconst 63
// CHECK:     v100: int:i64 = and v98, v99
// CHECK:     v101: int:i64 = shl v97:u64, v100
// CHECK:     v102: int:u64 = zext v101, 64
// CHECK:     v103: int:i64 = iconst 1
// CHECK:     v104: int:i64 = or v102, v103:u64
// CHECK:     v105: int:u64 = zext v104, 64
// CHECK:     v106: mem = store.8 v95, v6, v94
// CHECK:     v107: int:i64 = iconst 8
// CHECK:     v108: ptr = ptradd v6, v107
// CHECK:     v109: mem = store.8 v105, v108, v106
// CHECK:     v110: int:i64 = load.8 v6, v109
// CHECK:     v111: int:i64 = iconst 8
// CHECK:     v112: ptr = ptradd v6, v111
// CHECK:     v113: int:i64 = load.8 v112, v109
// CHECK:     v114: ptr = symbol_addr @.Lloc.11
// CHECK:     v115: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v116: mem = call v115(v110, v113, v114), v109
// CHECK:     v117: int:i64 = iconst 0
// CHECK:     unreachable
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
// CHECK:     brif v133, bb4(v131), bb10(v131)
// CHECK:
// CHECK:   bb10(v135: mem):
// CHECK:     v136: int:i64 = iconst 3
// CHECK:     v137: bool = icmp.eq v10, v136
// CHECK:     brif v137, bb3(v135), bb11(v135)
// CHECK:
// CHECK:   bb11(v139: mem):
// CHECK:     v140: int:i64 = iconst 4
// CHECK:     v141: bool = icmp.eq v10, v140
// CHECK:     brif v141, bb2(v139), bb1(v139)
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
// CHECK:     v14: ptr = stack_slot 16 align 8
// CHECK:     v15: ptr = stack_slot 16 align 8
// CHECK:     v16: int:i8 = load.1 v5, v9
// CHECK:     v17: int:i64 = iconst 0
// CHECK:     v18: bool = icmp.eq v16, v17
// CHECK:     brif v18, bb17(v9), bb29(v9)
// CHECK:
// CHECK:   bb1(v20: mem):
// CHECK:     v21: int:i8 = load.1 v7, v20
// CHECK:     v22: int:i64 = iconst 0
// CHECK:     v23: bool = icmp.eq v21, v22
// CHECK:     brif v23, bb4(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26: mem, v27: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v25
// CHECK:     v28: bool = icmp.eq v27, v2
// CHECK:     v29: mem = store.4 v27, v10, v26
// CHECK:     v30: int:i64 = iconst 4
// CHECK:     v31: ptr = ptradd v10, v30
// CHECK:     v32: mem = store.1 v28, v31, v29
// CHECK:     br bb25(v32)
// CHECK:
// CHECK:   bb3(v34: mem):
// CHECK:     v35: mem, v36: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v34
// CHECK:     v37: bool = icmp.eq v36, v2
// CHECK:     v38: mem = store.4 v36, v10, v35
// CHECK:     v39: int:i64 = iconst 4
// CHECK:     v40: ptr = ptradd v10, v39
// CHECK:     v41: mem = store.1 v37, v40, v38
// CHECK:     br bb25(v41)
// CHECK:
// CHECK:   bb4(v43: mem):
// CHECK:     v44: mem, v45: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v43
// CHECK:     v46: bool = icmp.eq v45, v2
// CHECK:     v47: mem = store.4 v45, v10, v44
// CHECK:     v48: int:i64 = iconst 4
// CHECK:     v49: ptr = ptradd v10, v48
// CHECK:     v50: mem = store.1 v46, v49, v47
// CHECK:     br bb25(v50)
// CHECK:
// CHECK:   bb5(v52: mem):
// CHECK:     v53: int:i8 = load.1 v7, v52
// CHECK:     v54: int:i64 = iconst 0
// CHECK:     v55: bool = icmp.eq v53, v54
// CHECK:     brif v55, bb8(v52), bb35(v52)
// CHECK:
// CHECK:   bb6(v57: mem):
// CHECK:     v58: mem, v59: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v57
// CHECK:     v60: bool = icmp.eq v59, v2
// CHECK:     v61: mem = store.4 v59, v10, v58
// CHECK:     v62: int:i64 = iconst 4
// CHECK:     v63: ptr = ptradd v10, v62
// CHECK:     v64: mem = store.1 v60, v63, v61
// CHECK:     br bb25(v64)
// CHECK:
// CHECK:   bb7(v66: mem):
// CHECK:     v67: mem, v68: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v66
// CHECK:     v69: bool = icmp.eq v68, v2
// CHECK:     v70: mem = store.4 v68, v10, v67
// CHECK:     v71: int:i64 = iconst 4
// CHECK:     v72: ptr = ptradd v10, v71
// CHECK:     v73: mem = store.1 v69, v72, v70
// CHECK:     br bb25(v73)
// CHECK:
// CHECK:   bb8(v75: mem):
// CHECK:     v76: mem, v77: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v75
// CHECK:     v78: bool = icmp.eq v77, v2
// CHECK:     v79: mem = store.4 v77, v10, v76
// CHECK:     v80: int:i64 = iconst 4
// CHECK:     v81: ptr = ptradd v10, v80
// CHECK:     v82: mem = store.1 v78, v81, v79
// CHECK:     br bb25(v82)
// CHECK:
// CHECK:   bb9(v84: mem):
// CHECK:     v85: int:i8 = load.1 v7, v84
// CHECK:     v86: int:i64 = iconst 0
// CHECK:     v87: bool = icmp.eq v85, v86
// CHECK:     brif v87, bb12(v84), bb37(v84)
// CHECK:
// CHECK:   bb10(v89: mem):
// CHECK:     v90: mem, v91: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v89
// CHECK:     v92: bool = icmp.eq v91, v2
// CHECK:     v93: mem = store.4 v91, v10, v90
// CHECK:     v94: int:i64 = iconst 4
// CHECK:     v95: ptr = ptradd v10, v94
// CHECK:     v96: mem = store.1 v92, v95, v93
// CHECK:     br bb25(v96)
// CHECK:
// CHECK:   bb11(v98: mem):
// CHECK:     v99: mem, v100: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v98
// CHECK:     v101: bool = icmp.eq v100, v2
// CHECK:     v102: mem = store.4 v100, v10, v99
// CHECK:     v103: int:i64 = iconst 4
// CHECK:     v104: ptr = ptradd v10, v103
// CHECK:     v105: mem = store.1 v101, v104, v102
// CHECK:     br bb25(v105)
// CHECK:
// CHECK:   bb12(v107: mem):
// CHECK:     v108: mem, v109: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v107
// CHECK:     v110: bool = icmp.eq v109, v2
// CHECK:     v111: mem = store.4 v109, v10, v108
// CHECK:     v112: int:i64 = iconst 4
// CHECK:     v113: ptr = ptradd v10, v112
// CHECK:     v114: mem = store.1 v110, v113, v111
// CHECK:     br bb25(v114)
// CHECK:
// CHECK:   bb13(v116: mem):
// CHECK:     v117: int:i8 = load.1 v7, v116
// CHECK:     v118: int:i64 = iconst 0
// CHECK:     v119: bool = icmp.eq v117, v118
// CHECK:     brif v119, bb16(v116), bb39(v116)
// CHECK:
// CHECK:   bb14(v121: mem):
// CHECK:     v122: mem, v123: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v121
// CHECK:     v124: bool = icmp.eq v123, v2
// CHECK:     v125: mem = store.4 v123, v10, v122
// CHECK:     v126: int:i64 = iconst 4
// CHECK:     v127: ptr = ptradd v10, v126
// CHECK:     v128: mem = store.1 v124, v127, v125
// CHECK:     br bb25(v128)
// CHECK:
// CHECK:   bb15(v130: mem):
// CHECK:     v131: mem, v132: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v130
// CHECK:     v133: bool = icmp.eq v132, v2
// CHECK:     v134: mem = store.4 v132, v10, v131
// CHECK:     v135: int:i64 = iconst 4
// CHECK:     v136: ptr = ptradd v10, v135
// CHECK:     v137: mem = store.1 v133, v136, v134
// CHECK:     br bb25(v137)
// CHECK:
// CHECK:   bb16(v139: mem):
// CHECK:     v140: mem, v141: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v139
// CHECK:     v142: bool = icmp.eq v141, v2
// CHECK:     v143: mem = store.4 v141, v10, v140
// CHECK:     v144: int:i64 = iconst 4
// CHECK:     v145: ptr = ptradd v10, v144
// CHECK:     v146: mem = store.1 v142, v145, v143
// CHECK:     br bb25(v146)
// CHECK:
// CHECK:   bb17(v148: mem):
// CHECK:     v149: int:i8 = load.1 v7, v148
// CHECK:     v150: int:i64 = iconst 0
// CHECK:     v151: bool = icmp.eq v149, v150
// CHECK:     brif v151, bb24(v148), bb41(v148)
// CHECK:
// CHECK:   bb18(v153: mem):
// CHECK:     v154: int:i8 = load.1 v7, v153
// CHECK:     v155: int:i64 = iconst 1
// CHECK:     v156: bool = icmp.eq v154, v155
// CHECK:     brif v156, bb21(v153), bb43(v153)
// CHECK:
// CHECK:   bb19(v158: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb20(v160: mem):
// CHECK:     v161: ptr = symbol_addr @.Lstr.12
// CHECK:     v162: int:i64 = iconst 61
// CHECK:     v163: mem = store.8 v161, v15, v160
// CHECK:     v164: int:i64 = iconst 8
// CHECK:     v165: ptr = ptradd v15, v164
// CHECK:     v166: mem = store.8 v162, v165, v163
// CHECK:     v167: int:i64 = iconst 61
// CHECK:     v168: int:i64 = iconst 8
// CHECK:     v169: ptr = ptradd v15, v168
// CHECK:     v170: mem = store.8 v167, v169, v166
// CHECK:     v171: ptr = load.8 v15, v170
// CHECK:     v172: int:i64 = iconst 8
// CHECK:     v173: ptr = ptradd v15, v172
// CHECK:     v174: int:i64 = load.8 v173, v170
// CHECK:     v175: ptr = stack_slot 16
// CHECK:     v176: mem = store.8 v171, v175, v170
// CHECK:     v177: int:i64 = iconst 8
// CHECK:     v178: ptr = ptradd v175, v177
// CHECK:     v179: mem = store.8 v174, v178, v176
// CHECK:     v180: int:i64 = iconst 8
// CHECK:     v181: ptr = ptradd v15, v180
// CHECK:     v182: int:i64 = load.8 v181, v179
// CHECK:     v183: int:i64 = iconst 8
// CHECK:     v184: ptr = ptradd v175, v183
// CHECK:     v185: mem = store.8 v182, v184, v179
// CHECK:     v186: ptr = load.8 v175, v185
// CHECK:     v187: ptr = symbol_addr @.Lstr.12
// CHECK:     v188: int:i64 = iconst 61
// CHECK:     v189: int:i32 = iconst 1
// CHECK:     v190: int:i64 = iconst 63
// CHECK:     v191: int:i64 = and v189, v190
// CHECK:     v192: int:i64 = shl v188:u64, v191
// CHECK:     v193: int:u64 = zext v192, 64
// CHECK:     v194: int:i64 = iconst 1
// CHECK:     v195: int:i64 = or v193, v194:u64
// CHECK:     v196: int:u64 = zext v195, 64
// CHECK:     v197: mem = store.8 v186, v12, v185
// CHECK:     v198: int:i64 = iconst 8
// CHECK:     v199: ptr = ptradd v12, v198
// CHECK:     v200: mem = store.8 v196, v199, v197
// CHECK:     v201: int:i64 = load.8 v12, v200
// CHECK:     v202: int:i64 = iconst 8
// CHECK:     v203: ptr = ptradd v12, v202
// CHECK:     v204: int:i64 = load.8 v203, v200
// CHECK:     v205: ptr = symbol_addr @.Lloc.14
// CHECK:     v206: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v207: mem = call v206(v201, v204, v205), v200
// CHECK:     v208: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb21(v210: mem):
// CHECK:     v211: ptr = symbol_addr @.Lstr.15
// CHECK:     v212: int:i64 = iconst 52
// CHECK:     v213: mem = store.8 v211, v14, v210
// CHECK:     v214: int:i64 = iconst 8
// CHECK:     v215: ptr = ptradd v14, v214
// CHECK:     v216: mem = store.8 v212, v215, v213
// CHECK:     v217: int:i64 = iconst 52
// CHECK:     v218: int:i64 = iconst 8
// CHECK:     v219: ptr = ptradd v14, v218
// CHECK:     v220: mem = store.8 v217, v219, v216
// CHECK:     v221: ptr = load.8 v14, v220
// CHECK:     v222: int:i64 = iconst 8
// CHECK:     v223: ptr = ptradd v14, v222
// CHECK:     v224: int:i64 = load.8 v223, v220
// CHECK:     v225: ptr = stack_slot 16
// CHECK:     v226: mem = store.8 v221, v225, v220
// CHECK:     v227: int:i64 = iconst 8
// CHECK:     v228: ptr = ptradd v225, v227
// CHECK:     v229: mem = store.8 v224, v228, v226
// CHECK:     v230: int:i64 = iconst 8
// CHECK:     v231: ptr = ptradd v14, v230
// CHECK:     v232: int:i64 = load.8 v231, v229
// CHECK:     v233: int:i64 = iconst 8
// CHECK:     v234: ptr = ptradd v225, v233
// CHECK:     v235: mem = store.8 v232, v234, v229
// CHECK:     v236: ptr = load.8 v225, v235
// CHECK:     v237: ptr = symbol_addr @.Lstr.15
// CHECK:     v238: int:i64 = iconst 52
// CHECK:     v239: int:i32 = iconst 1
// CHECK:     v240: int:i64 = iconst 63
// CHECK:     v241: int:i64 = and v239, v240
// CHECK:     v242: int:i64 = shl v238:u64, v241
// CHECK:     v243: int:u64 = zext v242, 64
// CHECK:     v244: int:i64 = iconst 1
// CHECK:     v245: int:i64 = or v243, v244:u64
// CHECK:     v246: int:u64 = zext v245, 64
// CHECK:     v247: mem = store.8 v236, v13, v235
// CHECK:     v248: int:i64 = iconst 8
// CHECK:     v249: ptr = ptradd v13, v248
// CHECK:     v250: mem = store.8 v246, v249, v247
// CHECK:     v251: int:i64 = load.8 v13, v250
// CHECK:     v252: int:i64 = iconst 8
// CHECK:     v253: ptr = ptradd v13, v252
// CHECK:     v254: int:i64 = load.8 v253, v250
// CHECK:     v255: ptr = symbol_addr @.Lloc.17
// CHECK:     v256: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v257: mem = call v256(v251, v254, v255), v250
// CHECK:     v258: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb22(v260: mem):
// CHECK:     v261: mem, v262: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v260
// CHECK:     v263: bool = icmp.eq v262, v2
// CHECK:     v264: mem = store.4 v262, v10, v261
// CHECK:     v265: int:i64 = iconst 4
// CHECK:     v266: ptr = ptradd v10, v265
// CHECK:     v267: mem = store.1 v263, v266, v264
// CHECK:     br bb25(v267)
// CHECK:
// CHECK:   bb23(v269: mem):
// CHECK:     v270: mem, v271: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v269
// CHECK:     v272: bool = icmp.eq v271, v2
// CHECK:     v273: mem = store.4 v271, v10, v270
// CHECK:     v274: int:i64 = iconst 4
// CHECK:     v275: ptr = ptradd v10, v274
// CHECK:     v276: mem = store.1 v272, v275, v273
// CHECK:     br bb25(v276)
// CHECK:
// CHECK:   bb24(v278: mem):
// CHECK:     v279: mem, v280: int:i32 = cmpxchg.seqcst.seqcst v1, v2, v3, v278
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
// CHECK:     brif v326, bb13(v324), bb30(v324)
// CHECK:
// CHECK:   bb30(v328: mem):
// CHECK:     v329: int:i64 = iconst 2
// CHECK:     v330: bool = icmp.eq v16, v329
// CHECK:     brif v330, bb9(v328), bb31(v328)
// CHECK:
// CHECK:   bb31(v332: mem):
// CHECK:     v333: int:i64 = iconst 3
// CHECK:     v334: bool = icmp.eq v16, v333
// CHECK:     brif v334, bb5(v332), bb32(v332)
// CHECK:
// CHECK:   bb32(v336: mem):
// CHECK:     v337: int:i64 = iconst 4
// CHECK:     v338: bool = icmp.eq v16, v337
// CHECK:     brif v338, bb1(v336), bb19(v336)
// CHECK:
// CHECK:   bb33(v340: mem):
// CHECK:     v341: int:i64 = iconst 2
// CHECK:     v342: bool = icmp.eq v21, v341
// CHECK:     brif v342, bb3(v340), bb34(v340)
// CHECK:
// CHECK:   bb34(v344: mem):
// CHECK:     v345: int:i64 = iconst 4
// CHECK:     v346: bool = icmp.eq v21, v345
// CHECK:     brif v346, bb2(v344), bb18(v344)
// CHECK:
// CHECK:   bb35(v348: mem):
// CHECK:     v349: int:i64 = iconst 2
// CHECK:     v350: bool = icmp.eq v53, v349
// CHECK:     brif v350, bb7(v348), bb36(v348)
// CHECK:
// CHECK:   bb36(v352: mem):
// CHECK:     v353: int:i64 = iconst 4
// CHECK:     v354: bool = icmp.eq v53, v353
// CHECK:     brif v354, bb6(v352), bb18(v352)
// CHECK:
// CHECK:   bb37(v356: mem):
// CHECK:     v357: int:i64 = iconst 2
// CHECK:     v358: bool = icmp.eq v85, v357
// CHECK:     brif v358, bb11(v356), bb38(v356)
// CHECK:
// CHECK:   bb38(v360: mem):
// CHECK:     v361: int:i64 = iconst 4
// CHECK:     v362: bool = icmp.eq v85, v361
// CHECK:     brif v362, bb10(v360), bb18(v360)
// CHECK:
// CHECK:   bb39(v364: mem):
// CHECK:     v365: int:i64 = iconst 2
// CHECK:     v366: bool = icmp.eq v117, v365
// CHECK:     brif v366, bb15(v364), bb40(v364)
// CHECK:
// CHECK:   bb40(v368: mem):
// CHECK:     v369: int:i64 = iconst 4
// CHECK:     v370: bool = icmp.eq v117, v369
// CHECK:     brif v370, bb14(v368), bb18(v368)
// CHECK:
// CHECK:   bb41(v372: mem):
// CHECK:     v373: int:i64 = iconst 2
// CHECK:     v374: bool = icmp.eq v149, v373
// CHECK:     brif v374, bb23(v372), bb42(v372)
// CHECK:
// CHECK:   bb42(v376: mem):
// CHECK:     v377: int:i64 = iconst 4
// CHECK:     v378: bool = icmp.eq v149, v377
// CHECK:     brif v378, bb22(v376), bb18(v376)
// CHECK:
// CHECK:   bb43(v380: mem):
// CHECK:     v381: int:i64 = iconst 3
// CHECK:     v382: bool = icmp.eq v154, v381
// CHECK:     brif v382, bb20(v380), bb19(v380)
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
// CHECK:     v4: ptr = stack_slot 8 align 8
// CHECK:     v5: mem = store.8 v1, v4, v0
// CHECK:     v6: ptr = stack_slot 8 align 4
// CHECK:     v7: ptr = load.8 v4, v5
// CHECK:     v8: int:i8 = iconst 4
// CHECK:     v9: int:i8 = iconst 4
// CHECK:     v10: ptr = symbol_addr @_RINvNtNtC$HASH_4core4sync6atomic23atomic_compare_exchangemEC$HASH_10atomic_ops
// CHECK:     v11: mem, v12: int:i32 = call v10(v7, v2, v3, v8, v9), v5 -> int:i32
// CHECK:     v13: mem = store.4 v12, v6, v11
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: int:i64 = iconst 4
// CHECK:     v16: ptr = ptradd v6, v15
// CHECK:     v17: mem = store.4 v14, v16, v13
// CHECK:     br bb1(v17)
// CHECK:
// CHECK:   bb1(v19: mem):
// CHECK:     v20: int:i32 = load.4 v6, v19
// CHECK:     v21: int:i64 = iconst 4
// CHECK:     v22: ptr = ptradd v6, v21
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
// CHECK:     v3: ptr = stack_slot 8 align 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int:i32 = rmw.add.seqcst v5, v2, v4
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
// CHECK:     v2: ptr = stack_slot 8 align 8
// CHECK:     v3: mem = store.8 v1, v2, v0
// CHECK:     v4: ptr = load.8 v2, v3
// CHECK:     v5: int:i8 = iconst 0
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
// CHECK:     v3: ptr = stack_slot 8 align 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: int:i8 = iconst 1
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
// CHECK:     v3: ptr = stack_slot 8 align 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int:i32 = rmw.xchg.seqcst v5, v2, v4
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
