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
// CHECK: data @.Lloc_file.2 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.3 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: data @.Lstr.4 = "there is no such thing as a release load"
// CHECK: data @.Lstr.5 = "there is no such thing as a release load"
// CHECK: data @.Lloc_file.6 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.7 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops(%self: ptr, %order: int) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int = param %order
// CHECK:     v3: ptr = stack_slot 4
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 1
// CHECK:     v9: mem = store.1 v2, v8, v0
// CHECK:     v10: int = load.1 v8, v9
// CHECK:     v11: int = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.0
// CHECK:     v18: int = iconst 49
// CHECK:     v19: int = iconst 49
// CHECK:     v20: mem = store.8 v17, v6, v16
// CHECK:     v21: int = iconst 8
// CHECK:     v22: ptr = ptradd v6, v21
// CHECK:     v23: mem = store.8 v19, v22, v20
// CHECK:     v24: int = iconst 49
// CHECK:     v25: int = iconst 8
// CHECK:     v26: ptr = ptradd v6, v25
// CHECK:     v27: mem = store.8 v24, v26, v23
// CHECK:     v28: ptr = load.8 v6, v27
// CHECK:     v29: int = ptrtoaddr v28
// CHECK:     v30: ptr = symbol_addr @.Lstr.1
// CHECK:     v31: int = iconst 49
// CHECK:     v32: mem = store.8 v29, v5, v27
// CHECK:     v33: int = iconst 0
// CHECK:     v34: int = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: int = load.8 v5, v36
// CHECK:     v38: int = iconst 8
// CHECK:     v39: ptr = ptradd v5, v38
// CHECK:     v40: int = load.8 v39, v36
// CHECK:     v41: ptr = symbol_addr @.Lloc.3
// CHECK:     v42: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v43: mem, v44: int = call v42(v37, v40, v41), v36 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v46: mem):
// CHECK:     v47: ptr = symbol_addr @.Lstr.4
// CHECK:     v48: int = iconst 40
// CHECK:     v49: int = iconst 40
// CHECK:     v50: mem = store.8 v47, v7, v46
// CHECK:     v51: int = iconst 8
// CHECK:     v52: ptr = ptradd v7, v51
// CHECK:     v53: mem = store.8 v49, v52, v50
// CHECK:     v54: int = iconst 40
// CHECK:     v55: int = iconst 8
// CHECK:     v56: ptr = ptradd v7, v55
// CHECK:     v57: mem = store.8 v54, v56, v53
// CHECK:     v58: ptr = load.8 v7, v57
// CHECK:     v59: int = ptrtoaddr v58
// CHECK:     v60: ptr = symbol_addr @.Lstr.5
// CHECK:     v61: int = iconst 40
// CHECK:     v62: mem = store.8 v59, v4, v57
// CHECK:     v63: int = iconst 0
// CHECK:     v64: int = iconst 8
// CHECK:     v65: ptr = ptradd v4, v64
// CHECK:     v66: mem = store.8 v63, v65, v62
// CHECK:     v67: int = load.8 v4, v66
// CHECK:     v68: int = iconst 8
// CHECK:     v69: ptr = ptradd v4, v68
// CHECK:     v70: int = load.8 v69, v66
// CHECK:     v71: ptr = symbol_addr @.Lloc.7
// CHECK:     v72: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v73: mem, v74: int = call v72(v67, v70, v71), v66 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v76: mem):
// CHECK:     v77: mem, v78: int = load.atomic.seqcst v1, v76
// CHECK:     br bb7(v77)
// CHECK:
// CHECK:   bb5(v80: mem):
// CHECK:     v81: mem, v82: int = load.atomic.seqcst v1, v80
// CHECK:     br bb7(v81)
// CHECK:
// CHECK:   bb6(v84: mem):
// CHECK:     v85: mem, v86: int = load.atomic.seqcst v1, v84
// CHECK:     br bb7(v85)
// CHECK:
// CHECK:   bb7(v88: mem):
// CHECK:     ret v86, v88
// CHECK:
// CHECK:   bb8(v90: mem):
// CHECK:     v91: int = iconst 1
// CHECK:     v92: bool = icmp.eq v10, v91
// CHECK:     brif v92, bb3(v90), bb9(v90)
// CHECK:
// CHECK:   bb9(v94: mem):
// CHECK:     v95: int = iconst 2
// CHECK:     v96: bool = icmp.eq v10, v95
// CHECK:     brif v96, bb5(v94), bb10(v94)
// CHECK:
// CHECK:   bb10(v98: mem):
// CHECK:     v99: int = iconst 3
// CHECK:     v100: bool = icmp.eq v10, v99
// CHECK:     brif v100, bb2(v98), bb11(v98)
// CHECK:
// CHECK:   bb11(v102: mem):
// CHECK:     v103: int = iconst 4
// CHECK:     v104: bool = icmp.eq v10, v103
// CHECK:     brif v104, bb4(v102), bb1(v102)
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
// CHECK: data @.Lloc_file.10 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.11 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: data @.Lstr.12 = "there is no such thing as an acquire store"
// CHECK: data @.Lstr.13 = "there is no such thing as an acquire store"
// CHECK: data @.Lloc_file.14 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.15 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %val: int:u32, %order: int) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int:u32 = param %val
// CHECK:     v3: int = param %order
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 1
// CHECK:     v9: mem = store.1 v3, v8, v0
// CHECK:     v10: int = load.1 v8, v9
// CHECK:     v11: int = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.8
// CHECK:     v18: int = iconst 50
// CHECK:     v19: int = iconst 50
// CHECK:     v20: mem = store.8 v17, v6, v16
// CHECK:     v21: int = iconst 8
// CHECK:     v22: ptr = ptradd v6, v21
// CHECK:     v23: mem = store.8 v19, v22, v20
// CHECK:     v24: int = iconst 50
// CHECK:     v25: int = iconst 8
// CHECK:     v26: ptr = ptradd v6, v25
// CHECK:     v27: mem = store.8 v24, v26, v23
// CHECK:     v28: ptr = load.8 v6, v27
// CHECK:     v29: int = ptrtoaddr v28
// CHECK:     v30: ptr = symbol_addr @.Lstr.9
// CHECK:     v31: int = iconst 50
// CHECK:     v32: mem = store.8 v29, v5, v27
// CHECK:     v33: int = iconst 0
// CHECK:     v34: int = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: int = load.8 v5, v36
// CHECK:     v38: int = iconst 8
// CHECK:     v39: ptr = ptradd v5, v38
// CHECK:     v40: int = load.8 v39, v36
// CHECK:     v41: ptr = symbol_addr @.Lloc.11
// CHECK:     v42: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v43: mem, v44: int = call v42(v37, v40, v41), v36 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v46: mem):
// CHECK:     v47: ptr = symbol_addr @.Lstr.12
// CHECK:     v48: int = iconst 42
// CHECK:     v49: int = iconst 42
// CHECK:     v50: mem = store.8 v47, v7, v46
// CHECK:     v51: int = iconst 8
// CHECK:     v52: ptr = ptradd v7, v51
// CHECK:     v53: mem = store.8 v49, v52, v50
// CHECK:     v54: int = iconst 42
// CHECK:     v55: int = iconst 8
// CHECK:     v56: ptr = ptradd v7, v55
// CHECK:     v57: mem = store.8 v54, v56, v53
// CHECK:     v58: ptr = load.8 v7, v57
// CHECK:     v59: int = ptrtoaddr v58
// CHECK:     v60: ptr = symbol_addr @.Lstr.13
// CHECK:     v61: int = iconst 42
// CHECK:     v62: mem = store.8 v59, v4, v57
// CHECK:     v63: int = iconst 0
// CHECK:     v64: int = iconst 8
// CHECK:     v65: ptr = ptradd v4, v64
// CHECK:     v66: mem = store.8 v63, v65, v62
// CHECK:     v67: int = load.8 v4, v66
// CHECK:     v68: int = iconst 8
// CHECK:     v69: ptr = ptradd v4, v68
// CHECK:     v70: int = load.8 v69, v66
// CHECK:     v71: ptr = symbol_addr @.Lloc.15
// CHECK:     v72: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v73: mem, v74: int = call v72(v67, v70, v71), v66 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v76: mem):
// CHECK:     v77: mem = store.atomic.seqcst v2, v1, v76
// CHECK:     br bb7(v77)
// CHECK:
// CHECK:   bb5(v79: mem):
// CHECK:     v80: mem = store.atomic.seqcst v2, v1, v79
// CHECK:     br bb7(v80)
// CHECK:
// CHECK:   bb6(v82: mem):
// CHECK:     v83: mem = store.atomic.seqcst v2, v1, v82
// CHECK:     br bb7(v83)
// CHECK:
// CHECK:   bb7(v85: mem):
// CHECK:     ret v85
// CHECK:
// CHECK:   bb8(v87: mem):
// CHECK:     v88: int = iconst 1
// CHECK:     v89: bool = icmp.eq v10, v88
// CHECK:     brif v89, bb5(v87), bb9(v87)
// CHECK:
// CHECK:   bb9(v91: mem):
// CHECK:     v92: int = iconst 2
// CHECK:     v93: bool = icmp.eq v10, v92
// CHECK:     brif v93, bb3(v91), bb10(v91)
// CHECK:
// CHECK:   bb10(v95: mem):
// CHECK:     v96: int = iconst 3
// CHECK:     v97: bool = icmp.eq v10, v96
// CHECK:     brif v97, bb2(v95), bb11(v95)
// CHECK:
// CHECK:   bb11(v99: mem):
// CHECK:     v100: int = iconst 4
// CHECK:     v101: bool = icmp.eq v10, v100
// CHECK:     brif v101, bb4(v99), bb1(v99)
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
// CHECK: data @.Lloc_file.18 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.19 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: data @.Lstr.20 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lstr.21 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lloc_file.22 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.23 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %old: int:u32, %new: int:u32, %success: int, %failure: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int:u32 = param %old
// CHECK:     v3: int:u32 = param %new
// CHECK:     v4: int = param %success
// CHECK:     v5: int = param %failure
// CHECK:     v6: ptr = stack_slot 8
// CHECK:     v7: ptr = stack_slot 8
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: ptr = stack_slot 16
// CHECK:     v12: ptr = stack_slot 1
// CHECK:     v13: mem = store.1 v4, v12, v0
// CHECK:     v14: int = load.1 v12, v13
// CHECK:     v15: int = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb2(v13), bb29(v13)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: ptr = stack_slot 1
// CHECK:     v20: mem = store.1 v5, v19, v18
// CHECK:     v21: int = load.1 v19, v20
// CHECK:     v22: int = iconst 1
// CHECK:     v23: bool = icmp.eq v21, v22
// CHECK:     brif v23, bb8(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26: ptr = stack_slot 1
// CHECK:     v27: mem = store.1 v5, v26, v25
// CHECK:     v28: int = load.1 v26, v27
// CHECK:     v29: int = iconst 0
// CHECK:     v30: bool = icmp.eq v28, v29
// CHECK:     brif v30, bb24(v27), bb34(v27)
// CHECK:
// CHECK:   bb3(v32: mem):
// CHECK:     v33: ptr = stack_slot 1
// CHECK:     v34: mem = store.1 v5, v33, v32
// CHECK:     v35: int = load.1 v33, v34
// CHECK:     v36: int = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb21(v34), bb36(v34)
// CHECK:
// CHECK:   bb4(v39: mem):
// CHECK:     v40: ptr = stack_slot 1
// CHECK:     v41: mem = store.1 v5, v40, v39
// CHECK:     v42: int = load.1 v40, v41
// CHECK:     v43: int = iconst 0
// CHECK:     v44: bool = icmp.eq v42, v43
// CHECK:     brif v44, bb18(v41), bb38(v41)
// CHECK:
// CHECK:   bb5(v46: mem):
// CHECK:     v47: ptr = stack_slot 1
// CHECK:     v48: mem = store.1 v5, v47, v46
// CHECK:     v49: int = load.1 v47, v48
// CHECK:     v50: int = iconst 0
// CHECK:     v51: bool = icmp.eq v49, v50
// CHECK:     brif v51, bb15(v48), bb40(v48)
// CHECK:
// CHECK:   bb6(v53: mem):
// CHECK:     v54: ptr = stack_slot 1
// CHECK:     v55: mem = store.1 v5, v54, v53
// CHECK:     v56: int = load.1 v54, v55
// CHECK:     v57: int = iconst 0
// CHECK:     v58: bool = icmp.eq v56, v57
// CHECK:     brif v58, bb12(v55), bb42(v55)
// CHECK:
// CHECK:   bb7(v60: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v62: mem):
// CHECK:     v63: ptr = symbol_addr @.Lstr.16
// CHECK:     v64: int = iconst 52
// CHECK:     v65: int = iconst 52
// CHECK:     v66: mem = store.8 v63, v10, v62
// CHECK:     v67: int = iconst 8
// CHECK:     v68: ptr = ptradd v10, v67
// CHECK:     v69: mem = store.8 v65, v68, v66
// CHECK:     v70: int = iconst 52
// CHECK:     v71: int = iconst 8
// CHECK:     v72: ptr = ptradd v10, v71
// CHECK:     v73: mem = store.8 v70, v72, v69
// CHECK:     v74: ptr = load.8 v10, v73
// CHECK:     v75: int = ptrtoaddr v74
// CHECK:     v76: ptr = symbol_addr @.Lstr.17
// CHECK:     v77: int = iconst 52
// CHECK:     v78: mem = store.8 v75, v9, v73
// CHECK:     v79: int = iconst 0
// CHECK:     v80: int = iconst 8
// CHECK:     v81: ptr = ptradd v9, v80
// CHECK:     v82: mem = store.8 v79, v81, v78
// CHECK:     v83: int = load.8 v9, v82
// CHECK:     v84: int = iconst 8
// CHECK:     v85: ptr = ptradd v9, v84
// CHECK:     v86: int = load.8 v85, v82
// CHECK:     v87: ptr = symbol_addr @.Lloc.19
// CHECK:     v88: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v89: mem, v90: int = call v88(v83, v86, v87), v82 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb9(v92: mem):
// CHECK:     v93: ptr = symbol_addr @.Lstr.20
// CHECK:     v94: int = iconst 61
// CHECK:     v95: int = iconst 61
// CHECK:     v96: mem = store.8 v93, v11, v92
// CHECK:     v97: int = iconst 8
// CHECK:     v98: ptr = ptradd v11, v97
// CHECK:     v99: mem = store.8 v95, v98, v96
// CHECK:     v100: int = iconst 61
// CHECK:     v101: int = iconst 8
// CHECK:     v102: ptr = ptradd v11, v101
// CHECK:     v103: mem = store.8 v100, v102, v99
// CHECK:     v104: ptr = load.8 v11, v103
// CHECK:     v105: int = ptrtoaddr v104
// CHECK:     v106: ptr = symbol_addr @.Lstr.21
// CHECK:     v107: int = iconst 61
// CHECK:     v108: mem = store.8 v105, v8, v103
// CHECK:     v109: int = iconst 0
// CHECK:     v110: int = iconst 8
// CHECK:     v111: ptr = ptradd v8, v110
// CHECK:     v112: mem = store.8 v109, v111, v108
// CHECK:     v113: int = load.8 v8, v112
// CHECK:     v114: int = iconst 8
// CHECK:     v115: ptr = ptradd v8, v114
// CHECK:     v116: int = load.8 v115, v112
// CHECK:     v117: ptr = symbol_addr @.Lloc.23
// CHECK:     v118: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v119: mem, v120: int = call v118(v113, v116, v117), v112 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v122: mem):
// CHECK:     v123: mem, v124: int = cmpxchg.seqcst.seqcst v1, v2, v3, v122
// CHECK:     v125: bool = icmp.eq v124, v2
// CHECK:     v126: mem = store.4 v124, v6, v123
// CHECK:     v127: int = iconst 4
// CHECK:     v128: ptr = ptradd v6, v127
// CHECK:     v129: mem = store.1 v125, v128, v126
// CHECK:     br bb25(v129)
// CHECK:
// CHECK:   bb11(v131: mem):
// CHECK:     v132: mem, v133: int = cmpxchg.seqcst.seqcst v1, v2, v3, v131
// CHECK:     v134: bool = icmp.eq v133, v2
// CHECK:     v135: mem = store.4 v133, v6, v132
// CHECK:     v136: int = iconst 4
// CHECK:     v137: ptr = ptradd v6, v136
// CHECK:     v138: mem = store.1 v134, v137, v135
// CHECK:     br bb25(v138)
// CHECK:
// CHECK:   bb12(v140: mem):
// CHECK:     v141: mem, v142: int = cmpxchg.seqcst.seqcst v1, v2, v3, v140
// CHECK:     v143: bool = icmp.eq v142, v2
// CHECK:     v144: mem = store.4 v142, v6, v141
// CHECK:     v145: int = iconst 4
// CHECK:     v146: ptr = ptradd v6, v145
// CHECK:     v147: mem = store.1 v143, v146, v144
// CHECK:     br bb25(v147)
// CHECK:
// CHECK:   bb13(v149: mem):
// CHECK:     v150: mem, v151: int = cmpxchg.seqcst.seqcst v1, v2, v3, v149
// CHECK:     v152: bool = icmp.eq v151, v2
// CHECK:     v153: mem = store.4 v151, v6, v150
// CHECK:     v154: int = iconst 4
// CHECK:     v155: ptr = ptradd v6, v154
// CHECK:     v156: mem = store.1 v152, v155, v153
// CHECK:     br bb25(v156)
// CHECK:
// CHECK:   bb14(v158: mem):
// CHECK:     v159: mem, v160: int = cmpxchg.seqcst.seqcst v1, v2, v3, v158
// CHECK:     v161: bool = icmp.eq v160, v2
// CHECK:     v162: mem = store.4 v160, v6, v159
// CHECK:     v163: int = iconst 4
// CHECK:     v164: ptr = ptradd v6, v163
// CHECK:     v165: mem = store.1 v161, v164, v162
// CHECK:     br bb25(v165)
// CHECK:
// CHECK:   bb15(v167: mem):
// CHECK:     v168: mem, v169: int = cmpxchg.seqcst.seqcst v1, v2, v3, v167
// CHECK:     v170: bool = icmp.eq v169, v2
// CHECK:     v171: mem = store.4 v169, v6, v168
// CHECK:     v172: int = iconst 4
// CHECK:     v173: ptr = ptradd v6, v172
// CHECK:     v174: mem = store.1 v170, v173, v171
// CHECK:     br bb25(v174)
// CHECK:
// CHECK:   bb16(v176: mem):
// CHECK:     v177: mem, v178: int = cmpxchg.seqcst.seqcst v1, v2, v3, v176
// CHECK:     v179: bool = icmp.eq v178, v2
// CHECK:     v180: mem = store.4 v178, v6, v177
// CHECK:     v181: int = iconst 4
// CHECK:     v182: ptr = ptradd v6, v181
// CHECK:     v183: mem = store.1 v179, v182, v180
// CHECK:     br bb25(v183)
// CHECK:
// CHECK:   bb17(v185: mem):
// CHECK:     v186: mem, v187: int = cmpxchg.seqcst.seqcst v1, v2, v3, v185
// CHECK:     v188: bool = icmp.eq v187, v2
// CHECK:     v189: mem = store.4 v187, v6, v186
// CHECK:     v190: int = iconst 4
// CHECK:     v191: ptr = ptradd v6, v190
// CHECK:     v192: mem = store.1 v188, v191, v189
// CHECK:     br bb25(v192)
// CHECK:
// CHECK:   bb18(v194: mem):
// CHECK:     v195: mem, v196: int = cmpxchg.seqcst.seqcst v1, v2, v3, v194
// CHECK:     v197: bool = icmp.eq v196, v2
// CHECK:     v198: mem = store.4 v196, v6, v195
// CHECK:     v199: int = iconst 4
// CHECK:     v200: ptr = ptradd v6, v199
// CHECK:     v201: mem = store.1 v197, v200, v198
// CHECK:     br bb25(v201)
// CHECK:
// CHECK:   bb19(v203: mem):
// CHECK:     v204: mem, v205: int = cmpxchg.seqcst.seqcst v1, v2, v3, v203
// CHECK:     v206: bool = icmp.eq v205, v2
// CHECK:     v207: mem = store.4 v205, v6, v204
// CHECK:     v208: int = iconst 4
// CHECK:     v209: ptr = ptradd v6, v208
// CHECK:     v210: mem = store.1 v206, v209, v207
// CHECK:     br bb25(v210)
// CHECK:
// CHECK:   bb20(v212: mem):
// CHECK:     v213: mem, v214: int = cmpxchg.seqcst.seqcst v1, v2, v3, v212
// CHECK:     v215: bool = icmp.eq v214, v2
// CHECK:     v216: mem = store.4 v214, v6, v213
// CHECK:     v217: int = iconst 4
// CHECK:     v218: ptr = ptradd v6, v217
// CHECK:     v219: mem = store.1 v215, v218, v216
// CHECK:     br bb25(v219)
// CHECK:
// CHECK:   bb21(v221: mem):
// CHECK:     v222: mem, v223: int = cmpxchg.seqcst.seqcst v1, v2, v3, v221
// CHECK:     v224: bool = icmp.eq v223, v2
// CHECK:     v225: mem = store.4 v223, v6, v222
// CHECK:     v226: int = iconst 4
// CHECK:     v227: ptr = ptradd v6, v226
// CHECK:     v228: mem = store.1 v224, v227, v225
// CHECK:     br bb25(v228)
// CHECK:
// CHECK:   bb22(v230: mem):
// CHECK:     v231: mem, v232: int = cmpxchg.seqcst.seqcst v1, v2, v3, v230
// CHECK:     v233: bool = icmp.eq v232, v2
// CHECK:     v234: mem = store.4 v232, v6, v231
// CHECK:     v235: int = iconst 4
// CHECK:     v236: ptr = ptradd v6, v235
// CHECK:     v237: mem = store.1 v233, v236, v234
// CHECK:     br bb25(v237)
// CHECK:
// CHECK:   bb23(v239: mem):
// CHECK:     v240: mem, v241: int = cmpxchg.seqcst.seqcst v1, v2, v3, v239
// CHECK:     v242: bool = icmp.eq v241, v2
// CHECK:     v243: mem = store.4 v241, v6, v240
// CHECK:     v244: int = iconst 4
// CHECK:     v245: ptr = ptradd v6, v244
// CHECK:     v246: mem = store.1 v242, v245, v243
// CHECK:     br bb25(v246)
// CHECK:
// CHECK:   bb24(v248: mem):
// CHECK:     v249: mem, v250: int = cmpxchg.seqcst.seqcst v1, v2, v3, v248
// CHECK:     v251: bool = icmp.eq v250, v2
// CHECK:     v252: mem = store.4 v250, v6, v249
// CHECK:     v253: int = iconst 4
// CHECK:     v254: ptr = ptradd v6, v253
// CHECK:     v255: mem = store.1 v251, v254, v252
// CHECK:     br bb25(v255)
// CHECK:
// CHECK:   bb25(v257: mem):
// CHECK:     v258: int = load.4 v6, v257
// CHECK:     v259: int = iconst 4
// CHECK:     v260: ptr = ptradd v6, v259
// CHECK:     v261: bool = load.1 v260, v257
// CHECK:     v262: int = bool_to_int v261
// CHECK:     v263: int = iconst 255
// CHECK:     v264: int = and v262, v263
// CHECK:     v265: int = iconst 0
// CHECK:     v266: bool = icmp.eq v264, v265
// CHECK:     brif v266, bb27(v257), bb26(v257)
// CHECK:
// CHECK:   bb26(v268: mem):
// CHECK:     v269: int = iconst 0
// CHECK:     v270: mem = store.8 v269, v7, v268
// CHECK:     v271: int = iconst 4
// CHECK:     v272: ptr = ptradd v7, v271
// CHECK:     v273: mem = store.4 v258, v272, v270
// CHECK:     v274: int = iconst 0
// CHECK:     v275: mem = store.4 v274, v7, v273
// CHECK:     br bb28(v275)
// CHECK:
// CHECK:   bb27(v277: mem):
// CHECK:     v278: int = iconst 0
// CHECK:     v279: mem = store.8 v278, v7, v277
// CHECK:     v280: int = iconst 4
// CHECK:     v281: ptr = ptradd v7, v280
// CHECK:     v282: mem = store.4 v258, v281, v279
// CHECK:     v283: int = iconst 1
// CHECK:     v284: mem = store.4 v283, v7, v282
// CHECK:     br bb28(v284)
// CHECK:
// CHECK:   bb28(v286: mem):
// CHECK:     v287: int = load.8 v7, v286
// CHECK:     ret v287, v286
// CHECK:
// CHECK:   bb29(v289: mem):
// CHECK:     v290: int = iconst 1
// CHECK:     v291: bool = icmp.eq v14, v290
// CHECK:     brif v291, bb4(v289), bb30(v289)
// CHECK:
// CHECK:   bb30(v293: mem):
// CHECK:     v294: int = iconst 2
// CHECK:     v295: bool = icmp.eq v14, v294
// CHECK:     brif v295, bb3(v293), bb31(v293)
// CHECK:
// CHECK:   bb31(v297: mem):
// CHECK:     v298: int = iconst 3
// CHECK:     v299: bool = icmp.eq v14, v298
// CHECK:     brif v299, bb5(v297), bb32(v297)
// CHECK:
// CHECK:   bb32(v301: mem):
// CHECK:     v302: int = iconst 4
// CHECK:     v303: bool = icmp.eq v14, v302
// CHECK:     brif v303, bb6(v301), bb7(v301)
// CHECK:
// CHECK:   bb33(v305: mem):
// CHECK:     v306: int = iconst 3
// CHECK:     v307: bool = icmp.eq v21, v306
// CHECK:     brif v307, bb9(v305), bb7(v305)
// CHECK:
// CHECK:   bb34(v309: mem):
// CHECK:     v310: int = iconst 2
// CHECK:     v311: bool = icmp.eq v28, v310
// CHECK:     brif v311, bb23(v309), bb35(v309)
// CHECK:
// CHECK:   bb35(v313: mem):
// CHECK:     v314: int = iconst 4
// CHECK:     v315: bool = icmp.eq v28, v314
// CHECK:     brif v315, bb22(v313), bb1(v313)
// CHECK:
// CHECK:   bb36(v317: mem):
// CHECK:     v318: int = iconst 2
// CHECK:     v319: bool = icmp.eq v35, v318
// CHECK:     brif v319, bb20(v317), bb37(v317)
// CHECK:
// CHECK:   bb37(v321: mem):
// CHECK:     v322: int = iconst 4
// CHECK:     v323: bool = icmp.eq v35, v322
// CHECK:     brif v323, bb19(v321), bb1(v321)
// CHECK:
// CHECK:   bb38(v325: mem):
// CHECK:     v326: int = iconst 2
// CHECK:     v327: bool = icmp.eq v42, v326
// CHECK:     brif v327, bb17(v325), bb39(v325)
// CHECK:
// CHECK:   bb39(v329: mem):
// CHECK:     v330: int = iconst 4
// CHECK:     v331: bool = icmp.eq v42, v330
// CHECK:     brif v331, bb16(v329), bb1(v329)
// CHECK:
// CHECK:   bb40(v333: mem):
// CHECK:     v334: int = iconst 2
// CHECK:     v335: bool = icmp.eq v49, v334
// CHECK:     brif v335, bb14(v333), bb41(v333)
// CHECK:
// CHECK:   bb41(v337: mem):
// CHECK:     v338: int = iconst 4
// CHECK:     v339: bool = icmp.eq v49, v338
// CHECK:     brif v339, bb13(v337), bb1(v337)
// CHECK:
// CHECK:   bb42(v341: mem):
// CHECK:     v342: int = iconst 2
// CHECK:     v343: bool = icmp.eq v56, v342
// CHECK:     brif v343, bb11(v341), bb43(v341)
// CHECK:
// CHECK:   bb43(v345: mem):
// CHECK:     v346: int = iconst 4
// CHECK:     v347: bool = icmp.eq v56, v346
// CHECK:     brif v347, bb10(v345), bb1(v345)
// CHECK: }
// CHECK:
// CHECK: === ISel failure dump for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops ===
// CHECK:   block 0 (inst_start=0, inst_count=17):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=Param(2)
// CHECK:     vref=3 (index=3) op=Param(3)
// CHECK:     vref=4 (index=4) op=Param(4)
// CHECK:     vref=5 (index=5) op=StackSlot(8)
// CHECK:     vref=6 (index=6) op=StackSlot(8)
// CHECK:     vref=7 (index=7) op=StackSlot(16)
// CHECK:     vref=8 (index=8) op=StackSlot(16)
// CHECK:     vref=9 (index=9) op=StackSlot(16)
// CHECK:     vref=10 (index=10) op=StackSlot(16)
// CHECK:     vref=11 (index=11) op=StackSlot(1)
// CHECK:     vref=12 (index=12) op=Store(Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(11), annotation: None }, 1, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     vref=13 (index=13) op=Load(Operand { value: ValueRef(11), annotation: None }, 1, Operand { value: ValueRef(12), annotation: None })
// CHECK:     vref=14 (index=14) op=Const(0)
// CHECK:     vref=15 (index=15) op=ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(14), annotation: None })
// CHECK:     vref=16 (index=16) op=BrIf(Operand { value: ValueRef(15), annotation: None }, BlockRef(2), [Operand { value: ValueRef(12), annotation: None }], BlockRef(29), [Operand { value: ValueRef(12), annotation: None }])
// CHECK:   block 1 (inst_start=29, inst_count=6):
// CHECK:     vref=29 (index=29) op=StackSlot(1)
// CHECK:     vref=30 (index=30) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(29), annotation: None }, 1, Operand { value: ValueRef(2147483649), annotation: None })
// CHECK:     vref=31 (index=31) op=Load(Operand { value: ValueRef(29), annotation: None }, 1, Operand { value: ValueRef(30), annotation: None })
// CHECK:     vref=32 (index=32) op=Const(1)
// CHECK:     vref=33 (index=33) op=ICmp(Eq, Operand { value: ValueRef(31), annotation: None }, Operand { value: ValueRef(32), annotation: None })
// CHECK:     vref=34 (index=34) op=BrIf(Operand { value: ValueRef(33), annotation: None }, BlockRef(8), [Operand { value: ValueRef(30), annotation: None }], BlockRef(33), [Operand { value: ValueRef(30), annotation: None }])
// CHECK:   block 2 (inst_start=38, inst_count=6):
// CHECK:     vref=38 (index=38) op=StackSlot(1)
// CHECK:     vref=39 (index=39) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(38), annotation: None }, 1, Operand { value: ValueRef(2147483650), annotation: None })
// CHECK:     vref=40 (index=40) op=Load(Operand { value: ValueRef(38), annotation: None }, 1, Operand { value: ValueRef(39), annotation: None })
// CHECK:     vref=41 (index=41) op=Const(0)
// CHECK:     vref=42 (index=42) op=ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(41), annotation: None })
// CHECK:     vref=43 (index=43) op=BrIf(Operand { value: ValueRef(42), annotation: None }, BlockRef(24), [Operand { value: ValueRef(39), annotation: None }], BlockRef(34), [Operand { value: ValueRef(39), annotation: None }])
// CHECK:   block 3 (inst_start=50, inst_count=6):
// CHECK:     vref=50 (index=50) op=StackSlot(1)
// CHECK:     vref=51 (index=51) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(50), annotation: None }, 1, Operand { value: ValueRef(2147483651), annotation: None })
// CHECK:     vref=52 (index=52) op=Load(Operand { value: ValueRef(50), annotation: None }, 1, Operand { value: ValueRef(51), annotation: None })
// CHECK:     vref=53 (index=53) op=Const(0)
// CHECK:     vref=54 (index=54) op=ICmp(Eq, Operand { value: ValueRef(52), annotation: None }, Operand { value: ValueRef(53), annotation: None })
// CHECK:     vref=55 (index=55) op=BrIf(Operand { value: ValueRef(54), annotation: None }, BlockRef(21), [Operand { value: ValueRef(51), annotation: None }], BlockRef(36), [Operand { value: ValueRef(51), annotation: None }])
// CHECK:   block 4 (inst_start=62, inst_count=6):
// CHECK:     vref=62 (index=62) op=StackSlot(1)
// CHECK:     vref=63 (index=63) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(62), annotation: None }, 1, Operand { value: ValueRef(2147483652), annotation: None })
// CHECK:     vref=64 (index=64) op=Load(Operand { value: ValueRef(62), annotation: None }, 1, Operand { value: ValueRef(63), annotation: None })
// CHECK:     vref=65 (index=65) op=Const(0)
// CHECK:     vref=66 (index=66) op=ICmp(Eq, Operand { value: ValueRef(64), annotation: None }, Operand { value: ValueRef(65), annotation: None })
// CHECK:     vref=67 (index=67) op=BrIf(Operand { value: ValueRef(66), annotation: None }, BlockRef(18), [Operand { value: ValueRef(63), annotation: None }], BlockRef(38), [Operand { value: ValueRef(63), annotation: None }])
// CHECK:   block 5 (inst_start=74, inst_count=6):
// CHECK:     vref=74 (index=74) op=StackSlot(1)
// CHECK:     vref=75 (index=75) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(74), annotation: None }, 1, Operand { value: ValueRef(2147483653), annotation: None })
// CHECK:     vref=76 (index=76) op=Load(Operand { value: ValueRef(74), annotation: None }, 1, Operand { value: ValueRef(75), annotation: None })
// CHECK:     vref=77 (index=77) op=Const(0)
// CHECK:     vref=78 (index=78) op=ICmp(Eq, Operand { value: ValueRef(76), annotation: None }, Operand { value: ValueRef(77), annotation: None })
// CHECK:     vref=79 (index=79) op=BrIf(Operand { value: ValueRef(78), annotation: None }, BlockRef(15), [Operand { value: ValueRef(75), annotation: None }], BlockRef(40), [Operand { value: ValueRef(75), annotation: None }])
// CHECK:   block 6 (inst_start=86, inst_count=6):
// CHECK:     vref=86 (index=86) op=StackSlot(1)
// CHECK:     vref=87 (index=87) op=Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(86), annotation: None }, 1, Operand { value: ValueRef(2147483654), annotation: None })
// CHECK:     vref=88 (index=88) op=Load(Operand { value: ValueRef(86), annotation: None }, 1, Operand { value: ValueRef(87), annotation: None })
// CHECK:     vref=89 (index=89) op=Const(0)
// CHECK:     vref=90 (index=90) op=ICmp(Eq, Operand { value: ValueRef(88), annotation: None }, Operand { value: ValueRef(89), annotation: None })
// CHECK:     vref=91 (index=91) op=BrIf(Operand { value: ValueRef(90), annotation: None }, BlockRef(12), [Operand { value: ValueRef(87), annotation: None }], BlockRef(42), [Operand { value: ValueRef(87), annotation: None }])
// CHECK:   block 7 (inst_start=98, inst_count=1):
// CHECK:     vref=98 (index=98) op=Unreachable
// CHECK:   block 8 (inst_start=99, inst_count=28):
// CHECK:     vref=99 (index=99) op=SymbolAddr(SymbolId(8))
// CHECK:     vref=100 (index=100) op=Const(52)
// CHECK:     vref=101 (index=101) op=Const(52)
// CHECK:     vref=102 (index=102) op=Store(Operand { value: ValueRef(99), annotation: None }, Operand { value: ValueRef(9), annotation: None }, 8, Operand { value: ValueRef(2147483656), annotation: None })
// CHECK:     vref=103 (index=103) op=Const(8)
// CHECK:     vref=104 (index=104) op=PtrAdd(Operand { value: ValueRef(9), annotation: None }, Operand { value: ValueRef(103), annotation: None })
// CHECK:     vref=105 (index=105) op=Store(Operand { value: ValueRef(101), annotation: None }, Operand { value: ValueRef(104), annotation: None }, 8, Operand { value: ValueRef(102), annotation: None })
// CHECK:     vref=106 (index=106) op=Const(52)
// CHECK:     vref=107 (index=107) op=Const(8)
// CHECK:     vref=108 (index=108) op=PtrAdd(Operand { value: ValueRef(9), annotation: None }, Operand { value: ValueRef(107), annotation: None })
// CHECK:     vref=109 (index=109) op=Store(Operand { value: ValueRef(106), annotation: None }, Operand { value: ValueRef(108), annotation: None }, 8, Operand { value: ValueRef(105), annotation: None })
// CHECK:     vref=110 (index=110) op=Load(Operand { value: ValueRef(9), annotation: None }, 8, Operand { value: ValueRef(109), annotation: None })
// CHECK:     vref=111 (index=111) op=PtrToAddr(Operand { value: ValueRef(110), annotation: None })
// CHECK:     vref=112 (index=112) op=SymbolAddr(SymbolId(9))
// CHECK:     vref=113 (index=113) op=Const(52)
// CHECK:     vref=114 (index=114) op=Store(Operand { value: ValueRef(111), annotation: None }, Operand { value: ValueRef(8), annotation: None }, 8, Operand { value: ValueRef(109), annotation: None })
// CHECK:     vref=115 (index=115) op=Const(0)
// CHECK:     vref=116 (index=116) op=Const(8)
// CHECK:     vref=117 (index=117) op=PtrAdd(Operand { value: ValueRef(8), annotation: None }, Operand { value: ValueRef(116), annotation: None })
// CHECK:     vref=118 (index=118) op=Store(Operand { value: ValueRef(115), annotation: None }, Operand { value: ValueRef(117), annotation: None }, 8, Operand { value: ValueRef(114), annotation: None })
// CHECK:     vref=119 (index=119) op=Load(Operand { value: ValueRef(8), annotation: None }, 8, Operand { value: ValueRef(118), annotation: None })
// CHECK:     vref=120 (index=120) op=Const(8)
// CHECK:     vref=121 (index=121) op=PtrAdd(Operand { value: ValueRef(8), annotation: None }, Operand { value: ValueRef(120), annotation: None })
// CHECK:     vref=122 (index=122) op=Load(Operand { value: ValueRef(121), annotation: None }, 8, Operand { value: ValueRef(118), annotation: None })
// CHECK:     vref=123 (index=123) op=SymbolAddr(SymbolId(11))
// CHECK:     vref=124 (index=124) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=125 (index=125) op=Call(Operand { value: ValueRef(124), annotation: None }, [Operand { value: ValueRef(119), annotation: None }, Operand { value: ValueRef(122), annotation: None }, Operand { value: ValueRef(123), annotation: None }], Operand { value: ValueRef(118), annotation: None })
// CHECK:     vref=126 (index=126) op=Unreachable
// CHECK:   block 9 (inst_start=127, inst_count=28):
// CHECK:     vref=127 (index=127) op=SymbolAddr(SymbolId(13))
// CHECK:     vref=128 (index=128) op=Const(61)
// CHECK:     vref=129 (index=129) op=Const(61)
// CHECK:     vref=130 (index=130) op=Store(Operand { value: ValueRef(127), annotation: None }, Operand { value: ValueRef(10), annotation: None }, 8, Operand { value: ValueRef(2147483657), annotation: None })
// CHECK:     vref=131 (index=131) op=Const(8)
// CHECK:     vref=132 (index=132) op=PtrAdd(Operand { value: ValueRef(10), annotation: None }, Operand { value: ValueRef(131), annotation: None })
// CHECK:     vref=133 (index=133) op=Store(Operand { value: ValueRef(129), annotation: None }, Operand { value: ValueRef(132), annotation: None }, 8, Operand { value: ValueRef(130), annotation: None })
// CHECK:     vref=134 (index=134) op=Const(61)
// CHECK:     vref=135 (index=135) op=Const(8)
// CHECK:     vref=136 (index=136) op=PtrAdd(Operand { value: ValueRef(10), annotation: None }, Operand { value: ValueRef(135), annotation: None })
// CHECK:     vref=137 (index=137) op=Store(Operand { value: ValueRef(134), annotation: None }, Operand { value: ValueRef(136), annotation: None }, 8, Operand { value: ValueRef(133), annotation: None })
// CHECK:     vref=138 (index=138) op=Load(Operand { value: ValueRef(10), annotation: None }, 8, Operand { value: ValueRef(137), annotation: None })
// CHECK:     vref=139 (index=139) op=PtrToAddr(Operand { value: ValueRef(138), annotation: None })
// CHECK:     vref=140 (index=140) op=SymbolAddr(SymbolId(14))
// CHECK:     vref=141 (index=141) op=Const(61)
// CHECK:     vref=142 (index=142) op=Store(Operand { value: ValueRef(139), annotation: None }, Operand { value: ValueRef(7), annotation: None }, 8, Operand { value: ValueRef(137), annotation: None })
// CHECK:     vref=143 (index=143) op=Const(0)
// CHECK:     vref=144 (index=144) op=Const(8)
// CHECK:     vref=145 (index=145) op=PtrAdd(Operand { value: ValueRef(7), annotation: None }, Operand { value: ValueRef(144), annotation: None })
// CHECK:     vref=146 (index=146) op=Store(Operand { value: ValueRef(143), annotation: None }, Operand { value: ValueRef(145), annotation: None }, 8, Operand { value: ValueRef(142), annotation: None })
// CHECK:     vref=147 (index=147) op=Load(Operand { value: ValueRef(7), annotation: None }, 8, Operand { value: ValueRef(146), annotation: None })
// CHECK:     vref=148 (index=148) op=Const(8)
// CHECK:     vref=149 (index=149) op=PtrAdd(Operand { value: ValueRef(7), annotation: None }, Operand { value: ValueRef(148), annotation: None })
// CHECK:     vref=150 (index=150) op=Load(Operand { value: ValueRef(149), annotation: None }, 8, Operand { value: ValueRef(146), annotation: None })
// CHECK:     vref=151 (index=151) op=SymbolAddr(SymbolId(16))
// CHECK:     vref=152 (index=152) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=153 (index=153) op=Call(Operand { value: ValueRef(152), annotation: None }, [Operand { value: ValueRef(147), annotation: None }, Operand { value: ValueRef(150), annotation: None }, Operand { value: ValueRef(151), annotation: None }], Operand { value: ValueRef(146), annotation: None })
// CHECK:     vref=154 (index=154) op=Unreachable
// CHECK:   block 10 (inst_start=155, inst_count=7):
// CHECK:     vref=155 (index=155) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483658), annotation: None })
// CHECK:     vref=156 (index=156) op=ICmp(Eq, Operand { value: ValueRef(1073741979), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=157 (index=157) op=Store(Operand { value: ValueRef(1073741979), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(155), annotation: None })
// CHECK:     vref=158 (index=158) op=Const(4)
// CHECK:     vref=159 (index=159) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(158), annotation: None })
// CHECK:     vref=160 (index=160) op=Store(Operand { value: ValueRef(156), annotation: None }, Operand { value: ValueRef(159), annotation: None }, 1, Operand { value: ValueRef(157), annotation: None })
// CHECK:     vref=161 (index=161) op=Br(BlockRef(25), [Operand { value: ValueRef(160), annotation: None }])
// CHECK:   block 11 (inst_start=162, inst_count=7):
// CHECK:     vref=162 (index=162) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483659), annotation: None })
// CHECK:     vref=163 (index=163) op=ICmp(Eq, Operand { value: ValueRef(1073741986), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=164 (index=164) op=Store(Operand { value: ValueRef(1073741986), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(162), annotation: None })
// CHECK:     vref=165 (index=165) op=Const(4)
// CHECK:     vref=166 (index=166) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(165), annotation: None })
// CHECK:     vref=167 (index=167) op=Store(Operand { value: ValueRef(163), annotation: None }, Operand { value: ValueRef(166), annotation: None }, 1, Operand { value: ValueRef(164), annotation: None })
// CHECK:     vref=168 (index=168) op=Br(BlockRef(25), [Operand { value: ValueRef(167), annotation: None }])
// CHECK:   block 12 (inst_start=169, inst_count=7):
// CHECK:     vref=169 (index=169) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483660), annotation: None })
// CHECK:     vref=170 (index=170) op=ICmp(Eq, Operand { value: ValueRef(1073741993), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=171 (index=171) op=Store(Operand { value: ValueRef(1073741993), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(169), annotation: None })
// CHECK:     vref=172 (index=172) op=Const(4)
// CHECK:     vref=173 (index=173) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(172), annotation: None })
// CHECK:     vref=174 (index=174) op=Store(Operand { value: ValueRef(170), annotation: None }, Operand { value: ValueRef(173), annotation: None }, 1, Operand { value: ValueRef(171), annotation: None })
// CHECK:     vref=175 (index=175) op=Br(BlockRef(25), [Operand { value: ValueRef(174), annotation: None }])
// CHECK:   block 13 (inst_start=176, inst_count=7):
// CHECK:     vref=176 (index=176) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483661), annotation: None })
// CHECK:     vref=177 (index=177) op=ICmp(Eq, Operand { value: ValueRef(1073742000), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=178 (index=178) op=Store(Operand { value: ValueRef(1073742000), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(176), annotation: None })
// CHECK:     vref=179 (index=179) op=Const(4)
// CHECK:     vref=180 (index=180) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(179), annotation: None })
// CHECK:     vref=181 (index=181) op=Store(Operand { value: ValueRef(177), annotation: None }, Operand { value: ValueRef(180), annotation: None }, 1, Operand { value: ValueRef(178), annotation: None })
// CHECK:     vref=182 (index=182) op=Br(BlockRef(25), [Operand { value: ValueRef(181), annotation: None }])
// CHECK:   block 14 (inst_start=183, inst_count=7):
// CHECK:     vref=183 (index=183) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483662), annotation: None })
// CHECK:     vref=184 (index=184) op=ICmp(Eq, Operand { value: ValueRef(1073742007), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=185 (index=185) op=Store(Operand { value: ValueRef(1073742007), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(183), annotation: None })
// CHECK:     vref=186 (index=186) op=Const(4)
// CHECK:     vref=187 (index=187) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(186), annotation: None })
// CHECK:     vref=188 (index=188) op=Store(Operand { value: ValueRef(184), annotation: None }, Operand { value: ValueRef(187), annotation: None }, 1, Operand { value: ValueRef(185), annotation: None })
// CHECK:     vref=189 (index=189) op=Br(BlockRef(25), [Operand { value: ValueRef(188), annotation: None }])
// CHECK:   block 15 (inst_start=190, inst_count=7):
// CHECK:     vref=190 (index=190) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483663), annotation: None })
// CHECK:     vref=191 (index=191) op=ICmp(Eq, Operand { value: ValueRef(1073742014), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=192 (index=192) op=Store(Operand { value: ValueRef(1073742014), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(190), annotation: None })
// CHECK:     vref=193 (index=193) op=Const(4)
// CHECK:     vref=194 (index=194) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(193), annotation: None })
// CHECK:     vref=195 (index=195) op=Store(Operand { value: ValueRef(191), annotation: None }, Operand { value: ValueRef(194), annotation: None }, 1, Operand { value: ValueRef(192), annotation: None })
// CHECK:     vref=196 (index=196) op=Br(BlockRef(25), [Operand { value: ValueRef(195), annotation: None }])
// CHECK:   block 16 (inst_start=197, inst_count=7):
// CHECK:     vref=197 (index=197) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483664), annotation: None })
// CHECK:     vref=198 (index=198) op=ICmp(Eq, Operand { value: ValueRef(1073742021), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=199 (index=199) op=Store(Operand { value: ValueRef(1073742021), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(197), annotation: None })
// CHECK:     vref=200 (index=200) op=Const(4)
// CHECK:     vref=201 (index=201) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(200), annotation: None })
// CHECK:     vref=202 (index=202) op=Store(Operand { value: ValueRef(198), annotation: None }, Operand { value: ValueRef(201), annotation: None }, 1, Operand { value: ValueRef(199), annotation: None })
// CHECK:     vref=203 (index=203) op=Br(BlockRef(25), [Operand { value: ValueRef(202), annotation: None }])
// CHECK:   block 17 (inst_start=204, inst_count=7):
// CHECK:     vref=204 (index=204) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483665), annotation: None })
// CHECK:     vref=205 (index=205) op=ICmp(Eq, Operand { value: ValueRef(1073742028), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=206 (index=206) op=Store(Operand { value: ValueRef(1073742028), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(204), annotation: None })
// CHECK:     vref=207 (index=207) op=Const(4)
// CHECK:     vref=208 (index=208) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(207), annotation: None })
// CHECK:     vref=209 (index=209) op=Store(Operand { value: ValueRef(205), annotation: None }, Operand { value: ValueRef(208), annotation: None }, 1, Operand { value: ValueRef(206), annotation: None })
// CHECK:     vref=210 (index=210) op=Br(BlockRef(25), [Operand { value: ValueRef(209), annotation: None }])
// CHECK:   block 18 (inst_start=211, inst_count=7):
// CHECK:     vref=211 (index=211) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483666), annotation: None })
// CHECK:     vref=212 (index=212) op=ICmp(Eq, Operand { value: ValueRef(1073742035), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=213 (index=213) op=Store(Operand { value: ValueRef(1073742035), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(211), annotation: None })
// CHECK:     vref=214 (index=214) op=Const(4)
// CHECK:     vref=215 (index=215) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(214), annotation: None })
// CHECK:     vref=216 (index=216) op=Store(Operand { value: ValueRef(212), annotation: None }, Operand { value: ValueRef(215), annotation: None }, 1, Operand { value: ValueRef(213), annotation: None })
// CHECK:     vref=217 (index=217) op=Br(BlockRef(25), [Operand { value: ValueRef(216), annotation: None }])
// CHECK:   block 19 (inst_start=218, inst_count=7):
// CHECK:     vref=218 (index=218) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483667), annotation: None })
// CHECK:     vref=219 (index=219) op=ICmp(Eq, Operand { value: ValueRef(1073742042), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=220 (index=220) op=Store(Operand { value: ValueRef(1073742042), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(218), annotation: None })
// CHECK:     vref=221 (index=221) op=Const(4)
// CHECK:     vref=222 (index=222) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(221), annotation: None })
// CHECK:     vref=223 (index=223) op=Store(Operand { value: ValueRef(219), annotation: None }, Operand { value: ValueRef(222), annotation: None }, 1, Operand { value: ValueRef(220), annotation: None })
// CHECK:     vref=224 (index=224) op=Br(BlockRef(25), [Operand { value: ValueRef(223), annotation: None }])
// CHECK:   block 20 (inst_start=225, inst_count=7):
// CHECK:     vref=225 (index=225) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483668), annotation: None })
// CHECK:     vref=226 (index=226) op=ICmp(Eq, Operand { value: ValueRef(1073742049), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=227 (index=227) op=Store(Operand { value: ValueRef(1073742049), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(225), annotation: None })
// CHECK:     vref=228 (index=228) op=Const(4)
// CHECK:     vref=229 (index=229) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(228), annotation: None })
// CHECK:     vref=230 (index=230) op=Store(Operand { value: ValueRef(226), annotation: None }, Operand { value: ValueRef(229), annotation: None }, 1, Operand { value: ValueRef(227), annotation: None })
// CHECK:     vref=231 (index=231) op=Br(BlockRef(25), [Operand { value: ValueRef(230), annotation: None }])
// CHECK:   block 21 (inst_start=232, inst_count=7):
// CHECK:     vref=232 (index=232) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483669), annotation: None })
// CHECK:     vref=233 (index=233) op=ICmp(Eq, Operand { value: ValueRef(1073742056), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=234 (index=234) op=Store(Operand { value: ValueRef(1073742056), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(232), annotation: None })
// CHECK:     vref=235 (index=235) op=Const(4)
// CHECK:     vref=236 (index=236) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(235), annotation: None })
// CHECK:     vref=237 (index=237) op=Store(Operand { value: ValueRef(233), annotation: None }, Operand { value: ValueRef(236), annotation: None }, 1, Operand { value: ValueRef(234), annotation: None })
// CHECK:     vref=238 (index=238) op=Br(BlockRef(25), [Operand { value: ValueRef(237), annotation: None }])
// CHECK:   block 22 (inst_start=239, inst_count=7):
// CHECK:     vref=239 (index=239) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483670), annotation: None })
// CHECK:     vref=240 (index=240) op=ICmp(Eq, Operand { value: ValueRef(1073742063), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=241 (index=241) op=Store(Operand { value: ValueRef(1073742063), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(239), annotation: None })
// CHECK:     vref=242 (index=242) op=Const(4)
// CHECK:     vref=243 (index=243) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(242), annotation: None })
// CHECK:     vref=244 (index=244) op=Store(Operand { value: ValueRef(240), annotation: None }, Operand { value: ValueRef(243), annotation: None }, 1, Operand { value: ValueRef(241), annotation: None })
// CHECK:     vref=245 (index=245) op=Br(BlockRef(25), [Operand { value: ValueRef(244), annotation: None }])
// CHECK:   block 23 (inst_start=246, inst_count=7):
// CHECK:     vref=246 (index=246) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483671), annotation: None })
// CHECK:     vref=247 (index=247) op=ICmp(Eq, Operand { value: ValueRef(1073742070), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=248 (index=248) op=Store(Operand { value: ValueRef(1073742070), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(246), annotation: None })
// CHECK:     vref=249 (index=249) op=Const(4)
// CHECK:     vref=250 (index=250) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(249), annotation: None })
// CHECK:     vref=251 (index=251) op=Store(Operand { value: ValueRef(247), annotation: None }, Operand { value: ValueRef(250), annotation: None }, 1, Operand { value: ValueRef(248), annotation: None })
// CHECK:     vref=252 (index=252) op=Br(BlockRef(25), [Operand { value: ValueRef(251), annotation: None }])
// CHECK:   block 24 (inst_start=253, inst_count=7):
// CHECK:     vref=253 (index=253) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483672), annotation: None })
// CHECK:     vref=254 (index=254) op=ICmp(Eq, Operand { value: ValueRef(1073742077), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=255 (index=255) op=Store(Operand { value: ValueRef(1073742077), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(253), annotation: None })
// CHECK:     vref=256 (index=256) op=Const(4)
// CHECK:     vref=257 (index=257) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(256), annotation: None })
// CHECK:     vref=258 (index=258) op=Store(Operand { value: ValueRef(254), annotation: None }, Operand { value: ValueRef(257), annotation: None }, 1, Operand { value: ValueRef(255), annotation: None })
// CHECK:     vref=259 (index=259) op=Br(BlockRef(25), [Operand { value: ValueRef(258), annotation: None }])
// CHECK:   block 25 (inst_start=260, inst_count=10):
// CHECK:     vref=260 (index=260) op=Load(Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(2147483673), annotation: None })
// CHECK:     vref=261 (index=261) op=Const(4)
// CHECK:     vref=262 (index=262) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(261), annotation: None })
// CHECK:     vref=263 (index=263) op=Load(Operand { value: ValueRef(262), annotation: None }, 1, Operand { value: ValueRef(2147483673), annotation: None })
// CHECK:     vref=264 (index=264) op=BoolToInt(Operand { value: ValueRef(263), annotation: None })
// CHECK:     vref=265 (index=265) op=Const(255)
// CHECK:     vref=266 (index=266) op=And(Operand { value: ValueRef(264), annotation: None }, Operand { value: ValueRef(265), annotation: None })
// CHECK:     vref=267 (index=267) op=Const(0)
// CHECK:     vref=268 (index=268) op=ICmp(Eq, Operand { value: ValueRef(266), annotation: None }, Operand { value: ValueRef(267), annotation: None })
// CHECK:     vref=269 (index=269) op=BrIf(Operand { value: ValueRef(268), annotation: None }, BlockRef(27), [Operand { value: ValueRef(2147483673), annotation: None }], BlockRef(26), [Operand { value: ValueRef(2147483673), annotation: None }])
// CHECK:   block 26 (inst_start=270, inst_count=8):
// CHECK:     vref=270 (index=270) op=Const(0)
// CHECK:     vref=271 (index=271) op=Store(Operand { value: ValueRef(270), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 8, Operand { value: ValueRef(2147483674), annotation: None })
// CHECK:     vref=272 (index=272) op=Const(4)
// CHECK:     vref=273 (index=273) op=PtrAdd(Operand { value: ValueRef(6), annotation: None }, Operand { value: ValueRef(272), annotation: None })
// CHECK:     vref=274 (index=274) op=Store(Operand { value: ValueRef(260), annotation: None }, Operand { value: ValueRef(273), annotation: None }, 4, Operand { value: ValueRef(271), annotation: None })
// CHECK:     vref=275 (index=275) op=Const(0)
// CHECK:     vref=276 (index=276) op=Store(Operand { value: ValueRef(275), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 4, Operand { value: ValueRef(274), annotation: None })
// CHECK:     vref=277 (index=277) op=Br(BlockRef(28), [Operand { value: ValueRef(276), annotation: None }])
// CHECK:   block 27 (inst_start=278, inst_count=8):
// CHECK:     vref=278 (index=278) op=Const(0)
// CHECK:     vref=279 (index=279) op=Store(Operand { value: ValueRef(278), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 8, Operand { value: ValueRef(2147483675), annotation: None })
// CHECK:     vref=280 (index=280) op=Const(4)
// CHECK:     vref=281 (index=281) op=PtrAdd(Operand { value: ValueRef(6), annotation: None }, Operand { value: ValueRef(280), annotation: None })
// CHECK:     vref=282 (index=282) op=Store(Operand { value: ValueRef(260), annotation: None }, Operand { value: ValueRef(281), annotation: None }, 4, Operand { value: ValueRef(279), annotation: None })
// CHECK:     vref=283 (index=283) op=Const(1)
// CHECK:     vref=284 (index=284) op=Store(Operand { value: ValueRef(283), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 4, Operand { value: ValueRef(282), annotation: None })
// CHECK:     vref=285 (index=285) op=Br(BlockRef(28), [Operand { value: ValueRef(284), annotation: None }])
// CHECK:   block 28 (inst_start=286, inst_count=2):
// CHECK:     vref=286 (index=286) op=Load(Operand { value: ValueRef(6), annotation: None }, 8, Operand { value: ValueRef(2147483676), annotation: None })
// CHECK:     vref=287 (index=287) op=Ret(Some(Operand { value: ValueRef(286), annotation: None }), Operand { value: ValueRef(2147483676), annotation: None })
// CHECK:   block 29 (inst_start=17, inst_count=3):
// CHECK:     vref=17 (index=17) op=Const(1)
// CHECK:     vref=18 (index=18) op=ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(17), annotation: None })
// CHECK:     vref=19 (index=19) op=BrIf(Operand { value: ValueRef(18), annotation: None }, BlockRef(4), [Operand { value: ValueRef(2147483677), annotation: None }], BlockRef(30), [Operand { value: ValueRef(2147483677), annotation: None }])
// CHECK:   block 30 (inst_start=20, inst_count=3):
// CHECK:     vref=20 (index=20) op=Const(2)
// CHECK:     vref=21 (index=21) op=ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(20), annotation: None })
// CHECK:     vref=22 (index=22) op=BrIf(Operand { value: ValueRef(21), annotation: None }, BlockRef(3), [Operand { value: ValueRef(2147483678), annotation: None }], BlockRef(31), [Operand { value: ValueRef(2147483678), annotation: None }])
// CHECK:   block 31 (inst_start=23, inst_count=3):
// CHECK:     vref=23 (index=23) op=Const(3)
// CHECK:     vref=24 (index=24) op=ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(23), annotation: None })
// CHECK:     vref=25 (index=25) op=BrIf(Operand { value: ValueRef(24), annotation: None }, BlockRef(5), [Operand { value: ValueRef(2147483679), annotation: None }], BlockRef(32), [Operand { value: ValueRef(2147483679), annotation: None }])
// CHECK:   block 32 (inst_start=26, inst_count=3):
// CHECK:     vref=26 (index=26) op=Const(4)
// CHECK:     vref=27 (index=27) op=ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(26), annotation: None })
// CHECK:     vref=28 (index=28) op=BrIf(Operand { value: ValueRef(27), annotation: None }, BlockRef(6), [Operand { value: ValueRef(2147483680), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483680), annotation: None }])
// CHECK:   block 33 (inst_start=35, inst_count=3):
// CHECK:     vref=35 (index=35) op=Const(3)
// CHECK:     vref=36 (index=36) op=ICmp(Eq, Operand { value: ValueRef(31), annotation: None }, Operand { value: ValueRef(35), annotation: None })
// CHECK:     vref=37 (index=37) op=BrIf(Operand { value: ValueRef(36), annotation: None }, BlockRef(9), [Operand { value: ValueRef(2147483681), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483681), annotation: None }])
// CHECK:   block 34 (inst_start=44, inst_count=3):
// CHECK:     vref=44 (index=44) op=Const(2)
// CHECK:     vref=45 (index=45) op=ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(44), annotation: None })
// CHECK:     vref=46 (index=46) op=BrIf(Operand { value: ValueRef(45), annotation: None }, BlockRef(23), [Operand { value: ValueRef(2147483682), annotation: None }], BlockRef(35), [Operand { value: ValueRef(2147483682), annotation: None }])
// CHECK:   block 35 (inst_start=47, inst_count=3):
// CHECK:     vref=47 (index=47) op=Const(4)
// CHECK:     vref=48 (index=48) op=ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(47), annotation: None })
// CHECK:     vref=49 (index=49) op=BrIf(Operand { value: ValueRef(48), annotation: None }, BlockRef(22), [Operand { value: ValueRef(2147483683), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483683), annotation: None }])
// CHECK:   block 36 (inst_start=56, inst_count=3):
// CHECK:     vref=56 (index=56) op=Const(2)
// CHECK:     vref=57 (index=57) op=ICmp(Eq, Operand { value: ValueRef(52), annotation: None }, Operand { value: ValueRef(56), annotation: None })
// CHECK:     vref=58 (index=58) op=BrIf(Operand { value: ValueRef(57), annotation: None }, BlockRef(20), [Operand { value: ValueRef(2147483684), annotation: None }], BlockRef(37), [Operand { value: ValueRef(2147483684), annotation: None }])
// CHECK:   block 37 (inst_start=59, inst_count=3):
// CHECK:     vref=59 (index=59) op=Const(4)
// CHECK:     vref=60 (index=60) op=ICmp(Eq, Operand { value: ValueRef(52), annotation: None }, Operand { value: ValueRef(59), annotation: None })
// CHECK:     vref=61 (index=61) op=BrIf(Operand { value: ValueRef(60), annotation: None }, BlockRef(19), [Operand { value: ValueRef(2147483685), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483685), annotation: None }])
// CHECK:   block 38 (inst_start=68, inst_count=3):
// CHECK:     vref=68 (index=68) op=Const(2)
// CHECK:     vref=69 (index=69) op=ICmp(Eq, Operand { value: ValueRef(64), annotation: None }, Operand { value: ValueRef(68), annotation: None })
// CHECK:     vref=70 (index=70) op=BrIf(Operand { value: ValueRef(69), annotation: None }, BlockRef(17), [Operand { value: ValueRef(2147483686), annotation: None }], BlockRef(39), [Operand { value: ValueRef(2147483686), annotation: None }])
// CHECK:   block 39 (inst_start=71, inst_count=3):
// CHECK:     vref=71 (index=71) op=Const(4)
// CHECK:     vref=72 (index=72) op=ICmp(Eq, Operand { value: ValueRef(64), annotation: None }, Operand { value: ValueRef(71), annotation: None })
// CHECK:     vref=73 (index=73) op=BrIf(Operand { value: ValueRef(72), annotation: None }, BlockRef(16), [Operand { value: ValueRef(2147483687), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483687), annotation: None }])
// CHECK:   block 40 (inst_start=80, inst_count=3):
// CHECK:     vref=80 (index=80) op=Const(2)
// CHECK:     vref=81 (index=81) op=ICmp(Eq, Operand { value: ValueRef(76), annotation: None }, Operand { value: ValueRef(80), annotation: None })
// CHECK:     vref=82 (index=82) op=BrIf(Operand { value: ValueRef(81), annotation: None }, BlockRef(14), [Operand { value: ValueRef(2147483688), annotation: None }], BlockRef(41), [Operand { value: ValueRef(2147483688), annotation: None }])
// CHECK:   block 41 (inst_start=83, inst_count=3):
// CHECK:     vref=83 (index=83) op=Const(4)
// CHECK:     vref=84 (index=84) op=ICmp(Eq, Operand { value: ValueRef(76), annotation: None }, Operand { value: ValueRef(83), annotation: None })
// CHECK:     vref=85 (index=85) op=BrIf(Operand { value: ValueRef(84), annotation: None }, BlockRef(13), [Operand { value: ValueRef(2147483689), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483689), annotation: None }])
// CHECK:   block 42 (inst_start=92, inst_count=3):
// CHECK:     vref=92 (index=92) op=Const(2)
// CHECK:     vref=93 (index=93) op=ICmp(Eq, Operand { value: ValueRef(88), annotation: None }, Operand { value: ValueRef(92), annotation: None })
// CHECK:     vref=94 (index=94) op=BrIf(Operand { value: ValueRef(93), annotation: None }, BlockRef(11), [Operand { value: ValueRef(2147483690), annotation: None }], BlockRef(43), [Operand { value: ValueRef(2147483690), annotation: None }])
// CHECK:   block 43 (inst_start=95, inst_count=3):
// CHECK:     vref=95 (index=95) op=Const(4)
// CHECK:     vref=96 (index=96) op=ICmp(Eq, Operand { value: ValueRef(88), annotation: None }, Operand { value: ValueRef(95), annotation: None })
// CHECK:     vref=97 (index=97) op=BrIf(Operand { value: ValueRef(96), annotation: None }, BlockRef(10), [Operand { value: ValueRef(2147483691), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483691), annotation: None }])
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] Param(1)
// CHECK:     [2] Param(2)
// CHECK:     [3] Param(3)
// CHECK:     [4] Param(4)
// CHECK:     [5] StackSlot(8)
// CHECK:     [6] StackSlot(8)
// CHECK:     [7] StackSlot(16)
// CHECK:     [8] StackSlot(16)
// CHECK:     [9] StackSlot(16)
// CHECK:     [10] StackSlot(16)
// CHECK:     [11] StackSlot(1)
// CHECK:     [12] Store(Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(11), annotation: None }, 1, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     [13] Load(Operand { value: ValueRef(11), annotation: None }, 1, Operand { value: ValueRef(12), annotation: None })
// CHECK:     [14] Const(0)
// CHECK:     [15] ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(14), annotation: None })
// CHECK:     [16] BrIf(Operand { value: ValueRef(15), annotation: None }, BlockRef(2), [Operand { value: ValueRef(12), annotation: None }], BlockRef(29), [Operand { value: ValueRef(12), annotation: None }])
// CHECK:     [17] Const(1)
// CHECK:     [18] ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(17), annotation: None })
// CHECK:     [19] BrIf(Operand { value: ValueRef(18), annotation: None }, BlockRef(4), [Operand { value: ValueRef(2147483677), annotation: None }], BlockRef(30), [Operand { value: ValueRef(2147483677), annotation: None }])
// CHECK:     [20] Const(2)
// CHECK:     [21] ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(20), annotation: None })
// CHECK:     [22] BrIf(Operand { value: ValueRef(21), annotation: None }, BlockRef(3), [Operand { value: ValueRef(2147483678), annotation: None }], BlockRef(31), [Operand { value: ValueRef(2147483678), annotation: None }])
// CHECK:     [23] Const(3)
// CHECK:     [24] ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(23), annotation: None })
// CHECK:     [25] BrIf(Operand { value: ValueRef(24), annotation: None }, BlockRef(5), [Operand { value: ValueRef(2147483679), annotation: None }], BlockRef(32), [Operand { value: ValueRef(2147483679), annotation: None }])
// CHECK:     [26] Const(4)
// CHECK:     [27] ICmp(Eq, Operand { value: ValueRef(13), annotation: None }, Operand { value: ValueRef(26), annotation: None })
// CHECK:     [28] BrIf(Operand { value: ValueRef(27), annotation: None }, BlockRef(6), [Operand { value: ValueRef(2147483680), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483680), annotation: None }])
// CHECK:     [29] StackSlot(1)
// CHECK:     [30] Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(29), annotation: None }, 1, Operand { value: ValueRef(2147483649), annotation: None })
// CHECK:     [31] Load(Operand { value: ValueRef(29), annotation: None }, 1, Operand { value: ValueRef(30), annotation: None })
// CHECK:     [32] Const(1)
// CHECK:     [33] ICmp(Eq, Operand { value: ValueRef(31), annotation: None }, Operand { value: ValueRef(32), annotation: None })
// CHECK:     [34] BrIf(Operand { value: ValueRef(33), annotation: None }, BlockRef(8), [Operand { value: ValueRef(30), annotation: None }], BlockRef(33), [Operand { value: ValueRef(30), annotation: None }])
// CHECK:     [35] Const(3)
// CHECK:     [36] ICmp(Eq, Operand { value: ValueRef(31), annotation: None }, Operand { value: ValueRef(35), annotation: None })
// CHECK:     [37] BrIf(Operand { value: ValueRef(36), annotation: None }, BlockRef(9), [Operand { value: ValueRef(2147483681), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483681), annotation: None }])
// CHECK:     [38] StackSlot(1)
// CHECK:     [39] Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(38), annotation: None }, 1, Operand { value: ValueRef(2147483650), annotation: None })
// CHECK:     [40] Load(Operand { value: ValueRef(38), annotation: None }, 1, Operand { value: ValueRef(39), annotation: None })
// CHECK:     [41] Const(0)
// CHECK:     [42] ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(41), annotation: None })
// CHECK:     [43] BrIf(Operand { value: ValueRef(42), annotation: None }, BlockRef(24), [Operand { value: ValueRef(39), annotation: None }], BlockRef(34), [Operand { value: ValueRef(39), annotation: None }])
// CHECK:     [44] Const(2)
// CHECK:     [45] ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(44), annotation: None })
// CHECK:     [46] BrIf(Operand { value: ValueRef(45), annotation: None }, BlockRef(23), [Operand { value: ValueRef(2147483682), annotation: None }], BlockRef(35), [Operand { value: ValueRef(2147483682), annotation: None }])
// CHECK:     [47] Const(4)
// CHECK:     [48] ICmp(Eq, Operand { value: ValueRef(40), annotation: None }, Operand { value: ValueRef(47), annotation: None })
// CHECK:     [49] BrIf(Operand { value: ValueRef(48), annotation: None }, BlockRef(22), [Operand { value: ValueRef(2147483683), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483683), annotation: None }])
// CHECK:     [50] StackSlot(1)
// CHECK:     [51] Store(Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(50), annotation: None }, 1, Operand { value: ValueRef(2147483651), annotation: None })
// CHECK:     [52] Load(Operand { value: ValueRef(50), annotation: None }, 1, Operand { value: ValueRef(51), annotation: None })
// CHECK:     [53] Const(0)
// CHECK:     [54] ICmp(Eq, Operand { value: ValueRef(52), annotation: None }, Operand { value: ValueRef(53), annotation: None })
// CHECK:     [55] BrIf(Operand { value: ValueRef(54), annotation: None }, BlockRef(21), [Operand { value: ValueRef(51), annotation: None }], BlockRef(36), [Operand { value: ValueRef(51), annotation: None }])
// CHECK:     [56] Const(2)
// CHECK:     [57] ICmp(Eq, Operand { value: ValueRef(52), annotation: None }, Operand { value: ValueRef(56), annotation: None })
// CHECK:     [58] BrIf(Operand { value: ValueRef(57), annotation: None }, BlockRef(20), [Operand { value: ValueRef(2147483684), annotation: None }], BlockRef(37), [Operand { value: ValueRef(2147483684), annotation: None }])
// CHECK:     [59] Const(4)
// CHECK: warning: isel failed on vref=ValueRef(155) op AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483658), annotation: None })
// CHECK: warning: isel failed for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops, emitting stub
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
// CHECK: func @atomic_compare_exchange(%ptr: ptr, %expected: int:u32, %new: int:u32) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:u32 = param %expected
// CHECK:     v3: int:u32 = param %new
// CHECK:     v4: ptr = stack_slot 8
// CHECK:     v5: mem = store.8 v1, v4, v0
// CHECK:     v6: ptr = load.8 v4, v5
// CHECK:     v7: int = iconst 4
// CHECK:     v8: int = iconst 4
// CHECK:     v9: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v10: mem, v11: int = call v9(v6, v2, v3, v7, v8), v5 -> int
// CHECK:     br bb1(v10)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     ret v11, v13
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
// CHECK: func @atomic_fetch_add(%ptr: ptr, %val: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:u32 = param %val
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int = rmw.add.seqcst v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
// CHECK: }
// CHECK:
// CHECK: === ISel failure dump for atomic_fetch_add ===
// CHECK:   block 0 (inst_start=0, inst_count=7):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=StackSlot(8)
// CHECK:     vref=3 (index=3) op=Store(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     vref=4 (index=4) op=Load(Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(3), annotation: None })
// CHECK:     vref=5 (index=5) op=AtomicRmw(Add, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK:     vref=6 (index=6) op=Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:   block 1 (inst_start=7, inst_count=1):
// CHECK:     vref=7 (index=7) op=Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), Operand { value: ValueRef(2147483649), annotation: None })
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] Param(1)
// CHECK:     [2] StackSlot(8)
// CHECK:     [3] Store(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     [4] Load(Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(3), annotation: None })
// CHECK:     [5] AtomicRmw(Add, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK:     [6] Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:     [7] Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), Operand { value: ValueRef(2147483649), annotation: None })
// CHECK: warning: isel failed on vref=ValueRef(5) op AtomicRmw(Add, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK: warning: isel failed for atomic_fetch_add, emitting stub
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
// CHECK: func @atomic_load_relaxed(%ptr: ptr) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: mem = store.8 v1, v2, v0
// CHECK:     v4: ptr = load.8 v2, v3
// CHECK:     v5: int = iconst 0
// CHECK:     v6: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops
// CHECK:     v7: mem, v8: int = call v6(v4, v5), v3 -> int
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
// CHECK: func @atomic_store_release(%ptr: ptr, %val: int:u32) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:u32 = param %val
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: int = iconst 1
// CHECK:     v7: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v8: mem = call v7(v5, v2, v6), v4
// CHECK:     v9: int = iconst 0
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
// CHECK: func @atomic_swap(%ptr: ptr, %val: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:u32 = param %val
// CHECK:     v3: ptr = stack_slot 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: ptr = load.8 v3, v4
// CHECK:     v6: mem, v7: int = rmw.xchg.seqcst v5, v2, v4
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
// CHECK: }
// CHECK:
// CHECK: === ISel failure dump for atomic_swap ===
// CHECK:   block 0 (inst_start=0, inst_count=7):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=StackSlot(8)
// CHECK:     vref=3 (index=3) op=Store(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     vref=4 (index=4) op=Load(Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(3), annotation: None })
// CHECK:     vref=5 (index=5) op=AtomicRmw(Xchg, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK:     vref=6 (index=6) op=Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:   block 1 (inst_start=7, inst_count=1):
// CHECK:     vref=7 (index=7) op=Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), Operand { value: ValueRef(2147483649), annotation: None })
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] Param(1)
// CHECK:     [2] StackSlot(8)
// CHECK:     [3] Store(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(2147483648), annotation: None })
// CHECK:     [4] Load(Operand { value: ValueRef(2), annotation: None }, 8, Operand { value: ValueRef(3), annotation: None })
// CHECK:     [5] AtomicRmw(Xchg, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK:     [6] Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:     [7] Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), Operand { value: ValueRef(2147483649), annotation: None })
// CHECK: warning: isel failed on vref=ValueRef(5) op AtomicRmw(Xchg, Operand { value: ValueRef(4), annotation: None }, Operand { value: ValueRef(1), annotation: None }, SeqCst, Operand { value: ValueRef(3), annotation: None })
// CHECK: warning: isel failed for atomic_swap, emitting stub

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
