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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops(%self: ptr) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int:i64 = iconst 0
// CHECK:     v3: ptr = stack_slot 4
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 1
// CHECK:     v9: mem = store.1 v2, v8, v0
// CHECK:     v10: int:i8 = load.1 v8, v9
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.0
// CHECK:     v18: int:i64 = iconst 49
// CHECK:     v19: int:i64 = iconst 49
// CHECK:     v20: mem = store.8 v17, v6, v16
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v6, v21
// CHECK:     v23: mem = store.8 v19, v22, v20
// CHECK:     v24: int:i64 = iconst 49
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v6, v25
// CHECK:     v27: mem = store.8 v24, v26, v23
// CHECK:     v28: ptr = load.8 v6, v27
// CHECK:     v29: int:u64 = ptrtoaddr v28
// CHECK:     v30: ptr = symbol_addr @.Lstr.1
// CHECK:     v31: int:i64 = iconst 49
// CHECK:     v32: mem = store.8 v29, v5, v27
// CHECK:     v33: int:i64 = iconst 0
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: ptr = symbol_addr @.Lloc.3
// CHECK:     v38: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v39: mem = call v38(v37), v36
// CHECK:     v40: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v42: mem):
// CHECK:     v43: ptr = symbol_addr @.Lstr.4
// CHECK:     v44: int:i64 = iconst 40
// CHECK:     v45: int:i64 = iconst 40
// CHECK:     v46: mem = store.8 v43, v7, v42
// CHECK:     v47: int:i64 = iconst 8
// CHECK:     v48: ptr = ptradd v7, v47
// CHECK:     v49: mem = store.8 v45, v48, v46
// CHECK:     v50: int:i64 = iconst 40
// CHECK:     v51: int:i64 = iconst 8
// CHECK:     v52: ptr = ptradd v7, v51
// CHECK:     v53: mem = store.8 v50, v52, v49
// CHECK:     v54: ptr = load.8 v7, v53
// CHECK:     v55: int:u64 = ptrtoaddr v54
// CHECK:     v56: ptr = symbol_addr @.Lstr.5
// CHECK:     v57: int:i64 = iconst 40
// CHECK:     v58: mem = store.8 v55, v4, v53
// CHECK:     v59: int:i64 = iconst 0
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v4, v60
// CHECK:     v62: mem = store.8 v59, v61, v58
// CHECK:     v63: ptr = symbol_addr @.Lloc.7
// CHECK:     v64: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v65: mem = call v64(v63), v62
// CHECK:     v66: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v68: mem):
// CHECK:     v69: mem, v70: int:i64 = load.atomic.seqcst v1, v68
// CHECK:     br bb7(v69)
// CHECK:
// CHECK:   bb5(v72: mem):
// CHECK:     v73: mem, v74: int:i64 = load.atomic.seqcst v1, v72
// CHECK:     br bb7(v73)
// CHECK:
// CHECK:   bb6(v76: mem):
// CHECK:     v77: mem, v78: int:i64 = load.atomic.seqcst v1, v76
// CHECK:     br bb7(v77)
// CHECK:
// CHECK:   bb7(v80: mem):
// CHECK:     ret v78, v80
// CHECK:
// CHECK:   bb8(v82: mem):
// CHECK:     v83: int:i64 = iconst 1
// CHECK:     v84: bool = icmp.eq v10, v83
// CHECK:     brif v84, bb3(v82), bb9(v82)
// CHECK:
// CHECK:   bb9(v86: mem):
// CHECK:     v87: int:i64 = iconst 2
// CHECK:     v88: bool = icmp.eq v10, v87
// CHECK:     brif v88, bb5(v86), bb10(v86)
// CHECK:
// CHECK:   bb10(v90: mem):
// CHECK:     v91: int:i64 = iconst 3
// CHECK:     v92: bool = icmp.eq v10, v91
// CHECK:     brif v92, bb2(v90), bb11(v90)
// CHECK:
// CHECK:   bb11(v94: mem):
// CHECK:     v95: int:i64 = iconst 4
// CHECK:     v96: bool = icmp.eq v10, v95
// CHECK:     brif v96, bb4(v94), bb1(v94)
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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %val: int:u32) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int:u32 = param %val
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 1
// CHECK:     v9: mem = store.1 v3, v8, v0
// CHECK:     v10: int:i8 = load.1 v8, v9
// CHECK:     v11: int:i64 = iconst 0
// CHECK:     v12: bool = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: ptr = symbol_addr @.Lstr.8
// CHECK:     v18: int:i64 = iconst 50
// CHECK:     v19: int:i64 = iconst 50
// CHECK:     v20: mem = store.8 v17, v6, v16
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v6, v21
// CHECK:     v23: mem = store.8 v19, v22, v20
// CHECK:     v24: int:i64 = iconst 50
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v6, v25
// CHECK:     v27: mem = store.8 v24, v26, v23
// CHECK:     v28: ptr = load.8 v6, v27
// CHECK:     v29: int:u64 = ptrtoaddr v28
// CHECK:     v30: ptr = symbol_addr @.Lstr.9
// CHECK:     v31: int:i64 = iconst 50
// CHECK:     v32: mem = store.8 v29, v5, v27
// CHECK:     v33: int:i64 = iconst 0
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v5, v34
// CHECK:     v36: mem = store.8 v33, v35, v32
// CHECK:     v37: ptr = symbol_addr @.Lloc.11
// CHECK:     v38: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v39: mem = call v38(v37), v36
// CHECK:     v40: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v42: mem):
// CHECK:     v43: ptr = symbol_addr @.Lstr.12
// CHECK:     v44: int:i64 = iconst 42
// CHECK:     v45: int:i64 = iconst 42
// CHECK:     v46: mem = store.8 v43, v7, v42
// CHECK:     v47: int:i64 = iconst 8
// CHECK:     v48: ptr = ptradd v7, v47
// CHECK:     v49: mem = store.8 v45, v48, v46
// CHECK:     v50: int:i64 = iconst 42
// CHECK:     v51: int:i64 = iconst 8
// CHECK:     v52: ptr = ptradd v7, v51
// CHECK:     v53: mem = store.8 v50, v52, v49
// CHECK:     v54: ptr = load.8 v7, v53
// CHECK:     v55: int:u64 = ptrtoaddr v54
// CHECK:     v56: ptr = symbol_addr @.Lstr.13
// CHECK:     v57: int:i64 = iconst 42
// CHECK:     v58: mem = store.8 v55, v4, v53
// CHECK:     v59: int:i64 = iconst 0
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v4, v60
// CHECK:     v62: mem = store.8 v59, v61, v58
// CHECK:     v63: ptr = symbol_addr @.Lloc.15
// CHECK:     v64: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v65: mem = call v64(v63), v62
// CHECK:     v66: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v68: mem):
// CHECK:     v69: mem = store.atomic.seqcst v2, v1, v68
// CHECK:     br bb7(v69)
// CHECK:
// CHECK:   bb5(v71: mem):
// CHECK:     v72: mem = store.atomic.seqcst v2, v1, v71
// CHECK:     br bb7(v72)
// CHECK:
// CHECK:   bb6(v74: mem):
// CHECK:     v75: mem = store.atomic.seqcst v2, v1, v74
// CHECK:     br bb7(v75)
// CHECK:
// CHECK:   bb7(v77: mem):
// CHECK:     ret v77
// CHECK:
// CHECK:   bb8(v79: mem):
// CHECK:     v80: int:i64 = iconst 1
// CHECK:     v81: bool = icmp.eq v10, v80
// CHECK:     brif v81, bb5(v79), bb9(v79)
// CHECK:
// CHECK:   bb9(v83: mem):
// CHECK:     v84: int:i64 = iconst 2
// CHECK:     v85: bool = icmp.eq v10, v84
// CHECK:     brif v85, bb3(v83), bb10(v83)
// CHECK:
// CHECK:   bb10(v87: mem):
// CHECK:     v88: int:i64 = iconst 3
// CHECK:     v89: bool = icmp.eq v10, v88
// CHECK:     brif v89, bb2(v87), bb11(v87)
// CHECK:
// CHECK:   bb11(v91: mem):
// CHECK:     v92: int:i64 = iconst 4
// CHECK:     v93: bool = icmp.eq v10, v92
// CHECK:     brif v93, bb4(v91), bb1(v91)
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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %old: int:u32, %new: int:u32) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int:u32 = param %old
// CHECK:     v3: int:u32 = param %new
// CHECK:     v4: int:i64 = iconst 0
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: ptr = stack_slot 8
// CHECK:     v7: ptr = stack_slot 8
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: ptr = stack_slot 16
// CHECK:     v11: ptr = stack_slot 16
// CHECK:     v12: ptr = stack_slot 1
// CHECK:     v13: mem = store.1 v4, v12, v0
// CHECK:     v14: int:i8 = load.1 v12, v13
// CHECK:     v15: int:i64 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb2(v13), bb29(v13)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: ptr = stack_slot 1
// CHECK:     v20: mem = store.1 v5, v19, v18
// CHECK:     v21: int:i8 = load.1 v19, v20
// CHECK:     v22: int:i64 = iconst 1
// CHECK:     v23: bool = icmp.eq v21, v22
// CHECK:     brif v23, bb8(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26: ptr = stack_slot 1
// CHECK:     v27: mem = store.1 v5, v26, v25
// CHECK:     v28: int:i8 = load.1 v26, v27
// CHECK:     v29: int:i64 = iconst 0
// CHECK:     v30: bool = icmp.eq v28, v29
// CHECK:     brif v30, bb24(v27), bb34(v27)
// CHECK:
// CHECK:   bb3(v32: mem):
// CHECK:     v33: ptr = stack_slot 1
// CHECK:     v34: mem = store.1 v5, v33, v32
// CHECK:     v35: int:i8 = load.1 v33, v34
// CHECK:     v36: int:i64 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb21(v34), bb36(v34)
// CHECK:
// CHECK:   bb4(v39: mem):
// CHECK:     v40: ptr = stack_slot 1
// CHECK:     v41: mem = store.1 v5, v40, v39
// CHECK:     v42: int:i8 = load.1 v40, v41
// CHECK:     v43: int:i64 = iconst 0
// CHECK:     v44: bool = icmp.eq v42, v43
// CHECK:     brif v44, bb18(v41), bb38(v41)
// CHECK:
// CHECK:   bb5(v46: mem):
// CHECK:     v47: ptr = stack_slot 1
// CHECK:     v48: mem = store.1 v5, v47, v46
// CHECK:     v49: int:i8 = load.1 v47, v48
// CHECK:     v50: int:i64 = iconst 0
// CHECK:     v51: bool = icmp.eq v49, v50
// CHECK:     brif v51, bb15(v48), bb40(v48)
// CHECK:
// CHECK:   bb6(v53: mem):
// CHECK:     v54: ptr = stack_slot 1
// CHECK:     v55: mem = store.1 v5, v54, v53
// CHECK:     v56: int:i8 = load.1 v54, v55
// CHECK:     v57: int:i64 = iconst 0
// CHECK:     v58: bool = icmp.eq v56, v57
// CHECK:     brif v58, bb12(v55), bb42(v55)
// CHECK:
// CHECK:   bb7(v60: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v62: mem):
// CHECK:     v63: ptr = symbol_addr @.Lstr.16
// CHECK:     v64: int:i64 = iconst 52
// CHECK:     v65: int:i64 = iconst 52
// CHECK:     v66: mem = store.8 v63, v10, v62
// CHECK:     v67: int:i64 = iconst 8
// CHECK:     v68: ptr = ptradd v10, v67
// CHECK:     v69: mem = store.8 v65, v68, v66
// CHECK:     v70: int:i64 = iconst 52
// CHECK:     v71: int:i64 = iconst 8
// CHECK:     v72: ptr = ptradd v10, v71
// CHECK:     v73: mem = store.8 v70, v72, v69
// CHECK:     v74: ptr = load.8 v10, v73
// CHECK:     v75: int:u64 = ptrtoaddr v74
// CHECK:     v76: ptr = symbol_addr @.Lstr.17
// CHECK:     v77: int:i64 = iconst 52
// CHECK:     v78: mem = store.8 v75, v9, v73
// CHECK:     v79: int:i64 = iconst 0
// CHECK:     v80: int:i64 = iconst 8
// CHECK:     v81: ptr = ptradd v9, v80
// CHECK:     v82: mem = store.8 v79, v81, v78
// CHECK:     v83: ptr = symbol_addr @.Lloc.19
// CHECK:     v84: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v85: mem = call v84(v83), v82
// CHECK:     v86: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb9(v88: mem):
// CHECK:     v89: ptr = symbol_addr @.Lstr.20
// CHECK:     v90: int:i64 = iconst 61
// CHECK:     v91: int:i64 = iconst 61
// CHECK:     v92: mem = store.8 v89, v11, v88
// CHECK:     v93: int:i64 = iconst 8
// CHECK:     v94: ptr = ptradd v11, v93
// CHECK:     v95: mem = store.8 v91, v94, v92
// CHECK:     v96: int:i64 = iconst 61
// CHECK:     v97: int:i64 = iconst 8
// CHECK:     v98: ptr = ptradd v11, v97
// CHECK:     v99: mem = store.8 v96, v98, v95
// CHECK:     v100: ptr = load.8 v11, v99
// CHECK:     v101: int:u64 = ptrtoaddr v100
// CHECK:     v102: ptr = symbol_addr @.Lstr.21
// CHECK:     v103: int:i64 = iconst 61
// CHECK:     v104: mem = store.8 v101, v8, v99
// CHECK:     v105: int:i64 = iconst 0
// CHECK:     v106: int:i64 = iconst 8
// CHECK:     v107: ptr = ptradd v8, v106
// CHECK:     v108: mem = store.8 v105, v107, v104
// CHECK:     v109: ptr = symbol_addr @.Lloc.23
// CHECK:     v110: ptr = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v111: mem = call v110(v109), v108
// CHECK:     v112: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v114: mem):
// CHECK:     v115: mem, v116: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v114
// CHECK:     v117: bool = icmp.eq v116, v2
// CHECK:     v118: mem = store.4 v116, v6, v115
// CHECK:     v119: int:i64 = iconst 4
// CHECK:     v120: ptr = ptradd v6, v119
// CHECK:     v121: mem = store.1 v117, v120, v118
// CHECK:     br bb25(v121)
// CHECK:
// CHECK:   bb11(v123: mem):
// CHECK:     v124: mem, v125: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v123
// CHECK:     v126: bool = icmp.eq v125, v2
// CHECK:     v127: mem = store.4 v125, v6, v124
// CHECK:     v128: int:i64 = iconst 4
// CHECK:     v129: ptr = ptradd v6, v128
// CHECK:     v130: mem = store.1 v126, v129, v127
// CHECK:     br bb25(v130)
// CHECK:
// CHECK:   bb12(v132: mem):
// CHECK:     v133: mem, v134: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v132
// CHECK:     v135: bool = icmp.eq v134, v2
// CHECK:     v136: mem = store.4 v134, v6, v133
// CHECK:     v137: int:i64 = iconst 4
// CHECK:     v138: ptr = ptradd v6, v137
// CHECK:     v139: mem = store.1 v135, v138, v136
// CHECK:     br bb25(v139)
// CHECK:
// CHECK:   bb13(v141: mem):
// CHECK:     v142: mem, v143: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v141
// CHECK:     v144: bool = icmp.eq v143, v2
// CHECK:     v145: mem = store.4 v143, v6, v142
// CHECK:     v146: int:i64 = iconst 4
// CHECK:     v147: ptr = ptradd v6, v146
// CHECK:     v148: mem = store.1 v144, v147, v145
// CHECK:     br bb25(v148)
// CHECK:
// CHECK:   bb14(v150: mem):
// CHECK:     v151: mem, v152: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v150
// CHECK:     v153: bool = icmp.eq v152, v2
// CHECK:     v154: mem = store.4 v152, v6, v151
// CHECK:     v155: int:i64 = iconst 4
// CHECK:     v156: ptr = ptradd v6, v155
// CHECK:     v157: mem = store.1 v153, v156, v154
// CHECK:     br bb25(v157)
// CHECK:
// CHECK:   bb15(v159: mem):
// CHECK:     v160: mem, v161: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v159
// CHECK:     v162: bool = icmp.eq v161, v2
// CHECK:     v163: mem = store.4 v161, v6, v160
// CHECK:     v164: int:i64 = iconst 4
// CHECK:     v165: ptr = ptradd v6, v164
// CHECK:     v166: mem = store.1 v162, v165, v163
// CHECK:     br bb25(v166)
// CHECK:
// CHECK:   bb16(v168: mem):
// CHECK:     v169: mem, v170: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v168
// CHECK:     v171: bool = icmp.eq v170, v2
// CHECK:     v172: mem = store.4 v170, v6, v169
// CHECK:     v173: int:i64 = iconst 4
// CHECK:     v174: ptr = ptradd v6, v173
// CHECK:     v175: mem = store.1 v171, v174, v172
// CHECK:     br bb25(v175)
// CHECK:
// CHECK:   bb17(v177: mem):
// CHECK:     v178: mem, v179: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v177
// CHECK:     v180: bool = icmp.eq v179, v2
// CHECK:     v181: mem = store.4 v179, v6, v178
// CHECK:     v182: int:i64 = iconst 4
// CHECK:     v183: ptr = ptradd v6, v182
// CHECK:     v184: mem = store.1 v180, v183, v181
// CHECK:     br bb25(v184)
// CHECK:
// CHECK:   bb18(v186: mem):
// CHECK:     v187: mem, v188: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v186
// CHECK:     v189: bool = icmp.eq v188, v2
// CHECK:     v190: mem = store.4 v188, v6, v187
// CHECK:     v191: int:i64 = iconst 4
// CHECK:     v192: ptr = ptradd v6, v191
// CHECK:     v193: mem = store.1 v189, v192, v190
// CHECK:     br bb25(v193)
// CHECK:
// CHECK:   bb19(v195: mem):
// CHECK:     v196: mem, v197: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v195
// CHECK:     v198: bool = icmp.eq v197, v2
// CHECK:     v199: mem = store.4 v197, v6, v196
// CHECK:     v200: int:i64 = iconst 4
// CHECK:     v201: ptr = ptradd v6, v200
// CHECK:     v202: mem = store.1 v198, v201, v199
// CHECK:     br bb25(v202)
// CHECK:
// CHECK:   bb20(v204: mem):
// CHECK:     v205: mem, v206: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v204
// CHECK:     v207: bool = icmp.eq v206, v2
// CHECK:     v208: mem = store.4 v206, v6, v205
// CHECK:     v209: int:i64 = iconst 4
// CHECK:     v210: ptr = ptradd v6, v209
// CHECK:     v211: mem = store.1 v207, v210, v208
// CHECK:     br bb25(v211)
// CHECK:
// CHECK:   bb21(v213: mem):
// CHECK:     v214: mem, v215: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v213
// CHECK:     v216: bool = icmp.eq v215, v2
// CHECK:     v217: mem = store.4 v215, v6, v214
// CHECK:     v218: int:i64 = iconst 4
// CHECK:     v219: ptr = ptradd v6, v218
// CHECK:     v220: mem = store.1 v216, v219, v217
// CHECK:     br bb25(v220)
// CHECK:
// CHECK:   bb22(v222: mem):
// CHECK:     v223: mem, v224: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v222
// CHECK:     v225: bool = icmp.eq v224, v2
// CHECK:     v226: mem = store.4 v224, v6, v223
// CHECK:     v227: int:i64 = iconst 4
// CHECK:     v228: ptr = ptradd v6, v227
// CHECK:     v229: mem = store.1 v225, v228, v226
// CHECK:     br bb25(v229)
// CHECK:
// CHECK:   bb23(v231: mem):
// CHECK:     v232: mem, v233: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v231
// CHECK:     v234: bool = icmp.eq v233, v2
// CHECK:     v235: mem = store.4 v233, v6, v232
// CHECK:     v236: int:i64 = iconst 4
// CHECK:     v237: ptr = ptradd v6, v236
// CHECK:     v238: mem = store.1 v234, v237, v235
// CHECK:     br bb25(v238)
// CHECK:
// CHECK:   bb24(v240: mem):
// CHECK:     v241: mem, v242: int:i64 = cmpxchg.seqcst.seqcst v1, v2, v3, v240
// CHECK:     v243: bool = icmp.eq v242, v2
// CHECK:     v244: mem = store.4 v242, v6, v241
// CHECK:     v245: int:i64 = iconst 4
// CHECK:     v246: ptr = ptradd v6, v245
// CHECK:     v247: mem = store.1 v243, v246, v244
// CHECK:     br bb25(v247)
// CHECK:
// CHECK:   bb25(v249: mem):
// CHECK:     v250: int:i32 = load.4 v6, v249
// CHECK:     v251: int:i64 = iconst 4
// CHECK:     v252: ptr = ptradd v6, v251
// CHECK:     v253: bool = load.1 v252, v249
// CHECK:     v254: int:u64 = iconst 1
// CHECK:     v255: int:u64 = iconst 0
// CHECK:     v256: int:u64 = select v253, v254, v255
// CHECK:     v257: int:i64 = iconst 255
// CHECK:     v258: int:u64 = and v256, v257
// CHECK:     v259: int:i64 = iconst 0
// CHECK:     v260: bool = icmp.eq v258, v259
// CHECK:     brif v260, bb27(v249), bb26(v249)
// CHECK:
// CHECK:   bb26(v262: mem):
// CHECK:     v263: int:i64 = iconst 0
// CHECK:     v264: mem = store.8 v263, v7, v262
// CHECK:     v265: int:i64 = iconst 4
// CHECK:     v266: ptr = ptradd v7, v265
// CHECK:     v267: mem = store.4 v250, v266, v264
// CHECK:     v268: int:i64 = iconst 0
// CHECK:     v269: mem = store.4 v268, v7, v267
// CHECK:     br bb28(v269)
// CHECK:
// CHECK:   bb27(v271: mem):
// CHECK:     v272: int:i64 = iconst 0
// CHECK:     v273: mem = store.8 v272, v7, v271
// CHECK:     v274: int:i64 = iconst 4
// CHECK:     v275: ptr = ptradd v7, v274
// CHECK:     v276: mem = store.4 v250, v275, v273
// CHECK:     v277: int:i64 = iconst 1
// CHECK:     v278: mem = store.4 v277, v7, v276
// CHECK:     br bb28(v278)
// CHECK:
// CHECK:   bb28(v280: mem):
// CHECK:     ret v280
// CHECK:
// CHECK:   bb29(v282: mem):
// CHECK:     v283: int:i64 = iconst 1
// CHECK:     v284: bool = icmp.eq v14, v283
// CHECK:     brif v284, bb4(v282), bb30(v282)
// CHECK:
// CHECK:   bb30(v286: mem):
// CHECK:     v287: int:i64 = iconst 2
// CHECK:     v288: bool = icmp.eq v14, v287
// CHECK:     brif v288, bb3(v286), bb31(v286)
// CHECK:
// CHECK:   bb31(v290: mem):
// CHECK:     v291: int:i64 = iconst 3
// CHECK:     v292: bool = icmp.eq v14, v291
// CHECK:     brif v292, bb5(v290), bb32(v290)
// CHECK:
// CHECK:   bb32(v294: mem):
// CHECK:     v295: int:i64 = iconst 4
// CHECK:     v296: bool = icmp.eq v14, v295
// CHECK:     brif v296, bb6(v294), bb7(v294)
// CHECK:
// CHECK:   bb33(v298: mem):
// CHECK:     v299: int:i64 = iconst 3
// CHECK:     v300: bool = icmp.eq v21, v299
// CHECK:     brif v300, bb9(v298), bb7(v298)
// CHECK:
// CHECK:   bb34(v302: mem):
// CHECK:     v303: int:i64 = iconst 2
// CHECK:     v304: bool = icmp.eq v28, v303
// CHECK:     brif v304, bb23(v302), bb35(v302)
// CHECK:
// CHECK:   bb35(v306: mem):
// CHECK:     v307: int:i64 = iconst 4
// CHECK:     v308: bool = icmp.eq v28, v307
// CHECK:     brif v308, bb22(v306), bb1(v306)
// CHECK:
// CHECK:   bb36(v310: mem):
// CHECK:     v311: int:i64 = iconst 2
// CHECK:     v312: bool = icmp.eq v35, v311
// CHECK:     brif v312, bb20(v310), bb37(v310)
// CHECK:
// CHECK:   bb37(v314: mem):
// CHECK:     v315: int:i64 = iconst 4
// CHECK:     v316: bool = icmp.eq v35, v315
// CHECK:     brif v316, bb19(v314), bb1(v314)
// CHECK:
// CHECK:   bb38(v318: mem):
// CHECK:     v319: int:i64 = iconst 2
// CHECK:     v320: bool = icmp.eq v42, v319
// CHECK:     brif v320, bb17(v318), bb39(v318)
// CHECK:
// CHECK:   bb39(v322: mem):
// CHECK:     v323: int:i64 = iconst 4
// CHECK:     v324: bool = icmp.eq v42, v323
// CHECK:     brif v324, bb16(v322), bb1(v322)
// CHECK:
// CHECK:   bb40(v326: mem):
// CHECK:     v327: int:i64 = iconst 2
// CHECK:     v328: bool = icmp.eq v49, v327
// CHECK:     brif v328, bb14(v326), bb41(v326)
// CHECK:
// CHECK:   bb41(v330: mem):
// CHECK:     v331: int:i64 = iconst 4
// CHECK:     v332: bool = icmp.eq v49, v331
// CHECK:     brif v332, bb13(v330), bb1(v330)
// CHECK:
// CHECK:   bb42(v334: mem):
// CHECK:     v335: int:i64 = iconst 2
// CHECK:     v336: bool = icmp.eq v56, v335
// CHECK:     brif v336, bb11(v334), bb43(v334)
// CHECK:
// CHECK:   bb43(v338: mem):
// CHECK:     v339: int:i64 = iconst 4
// CHECK:     v340: bool = icmp.eq v56, v339
// CHECK:     brif v340, bb10(v338), bb1(v338)
// CHECK: }
// CHECK:
// CHECK: === ISel failure dump for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops ===
// CHECK:   block 0 (inst_start=0, inst_count=17):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=Param(2)
// CHECK:     vref=3 (index=3) op=Const(0)
// CHECK:     vref=4 (index=4) op=Const(0)
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
// CHECK:   block 8 (inst_start=99, inst_count=25):
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
// CHECK:     vref=119 (index=119) op=SymbolAddr(SymbolId(11))
// CHECK:     vref=120 (index=120) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=121 (index=121) op=Call(Operand { value: ValueRef(120), annotation: None }, [Operand { value: ValueRef(119), annotation: None }], Operand { value: ValueRef(118), annotation: None })
// CHECK:     vref=122 (index=122) op=Const(0)
// CHECK:     vref=123 (index=123) op=Unreachable
// CHECK:   block 9 (inst_start=124, inst_count=25):
// CHECK:     vref=124 (index=124) op=SymbolAddr(SymbolId(13))
// CHECK:     vref=125 (index=125) op=Const(61)
// CHECK:     vref=126 (index=126) op=Const(61)
// CHECK:     vref=127 (index=127) op=Store(Operand { value: ValueRef(124), annotation: None }, Operand { value: ValueRef(10), annotation: None }, 8, Operand { value: ValueRef(2147483657), annotation: None })
// CHECK:     vref=128 (index=128) op=Const(8)
// CHECK:     vref=129 (index=129) op=PtrAdd(Operand { value: ValueRef(10), annotation: None }, Operand { value: ValueRef(128), annotation: None })
// CHECK:     vref=130 (index=130) op=Store(Operand { value: ValueRef(126), annotation: None }, Operand { value: ValueRef(129), annotation: None }, 8, Operand { value: ValueRef(127), annotation: None })
// CHECK:     vref=131 (index=131) op=Const(61)
// CHECK:     vref=132 (index=132) op=Const(8)
// CHECK:     vref=133 (index=133) op=PtrAdd(Operand { value: ValueRef(10), annotation: None }, Operand { value: ValueRef(132), annotation: None })
// CHECK:     vref=134 (index=134) op=Store(Operand { value: ValueRef(131), annotation: None }, Operand { value: ValueRef(133), annotation: None }, 8, Operand { value: ValueRef(130), annotation: None })
// CHECK:     vref=135 (index=135) op=Load(Operand { value: ValueRef(10), annotation: None }, 8, Operand { value: ValueRef(134), annotation: None })
// CHECK:     vref=136 (index=136) op=PtrToAddr(Operand { value: ValueRef(135), annotation: None })
// CHECK:     vref=137 (index=137) op=SymbolAddr(SymbolId(14))
// CHECK:     vref=138 (index=138) op=Const(61)
// CHECK:     vref=139 (index=139) op=Store(Operand { value: ValueRef(136), annotation: None }, Operand { value: ValueRef(7), annotation: None }, 8, Operand { value: ValueRef(134), annotation: None })
// CHECK:     vref=140 (index=140) op=Const(0)
// CHECK:     vref=141 (index=141) op=Const(8)
// CHECK:     vref=142 (index=142) op=PtrAdd(Operand { value: ValueRef(7), annotation: None }, Operand { value: ValueRef(141), annotation: None })
// CHECK:     vref=143 (index=143) op=Store(Operand { value: ValueRef(140), annotation: None }, Operand { value: ValueRef(142), annotation: None }, 8, Operand { value: ValueRef(139), annotation: None })
// CHECK:     vref=144 (index=144) op=SymbolAddr(SymbolId(16))
// CHECK:     vref=145 (index=145) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=146 (index=146) op=Call(Operand { value: ValueRef(145), annotation: None }, [Operand { value: ValueRef(144), annotation: None }], Operand { value: ValueRef(143), annotation: None })
// CHECK:     vref=147 (index=147) op=Const(0)
// CHECK:     vref=148 (index=148) op=Unreachable
// CHECK:   block 10 (inst_start=149, inst_count=7):
// CHECK:     vref=149 (index=149) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483658), annotation: None })
// CHECK:     vref=150 (index=150) op=ICmp(Eq, Operand { value: ValueRef(1073741973), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=151 (index=151) op=Store(Operand { value: ValueRef(1073741973), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(149), annotation: None })
// CHECK:     vref=152 (index=152) op=Const(4)
// CHECK:     vref=153 (index=153) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(152), annotation: None })
// CHECK:     vref=154 (index=154) op=Store(Operand { value: ValueRef(150), annotation: None }, Operand { value: ValueRef(153), annotation: None }, 1, Operand { value: ValueRef(151), annotation: None })
// CHECK:     vref=155 (index=155) op=Br(BlockRef(25), [Operand { value: ValueRef(154), annotation: None }])
// CHECK:   block 11 (inst_start=156, inst_count=7):
// CHECK:     vref=156 (index=156) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483659), annotation: None })
// CHECK:     vref=157 (index=157) op=ICmp(Eq, Operand { value: ValueRef(1073741980), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=158 (index=158) op=Store(Operand { value: ValueRef(1073741980), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(156), annotation: None })
// CHECK:     vref=159 (index=159) op=Const(4)
// CHECK:     vref=160 (index=160) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(159), annotation: None })
// CHECK:     vref=161 (index=161) op=Store(Operand { value: ValueRef(157), annotation: None }, Operand { value: ValueRef(160), annotation: None }, 1, Operand { value: ValueRef(158), annotation: None })
// CHECK:     vref=162 (index=162) op=Br(BlockRef(25), [Operand { value: ValueRef(161), annotation: None }])
// CHECK:   block 12 (inst_start=163, inst_count=7):
// CHECK:     vref=163 (index=163) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483660), annotation: None })
// CHECK:     vref=164 (index=164) op=ICmp(Eq, Operand { value: ValueRef(1073741987), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=165 (index=165) op=Store(Operand { value: ValueRef(1073741987), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(163), annotation: None })
// CHECK:     vref=166 (index=166) op=Const(4)
// CHECK:     vref=167 (index=167) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(166), annotation: None })
// CHECK:     vref=168 (index=168) op=Store(Operand { value: ValueRef(164), annotation: None }, Operand { value: ValueRef(167), annotation: None }, 1, Operand { value: ValueRef(165), annotation: None })
// CHECK:     vref=169 (index=169) op=Br(BlockRef(25), [Operand { value: ValueRef(168), annotation: None }])
// CHECK:   block 13 (inst_start=170, inst_count=7):
// CHECK:     vref=170 (index=170) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483661), annotation: None })
// CHECK:     vref=171 (index=171) op=ICmp(Eq, Operand { value: ValueRef(1073741994), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=172 (index=172) op=Store(Operand { value: ValueRef(1073741994), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(170), annotation: None })
// CHECK:     vref=173 (index=173) op=Const(4)
// CHECK:     vref=174 (index=174) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(173), annotation: None })
// CHECK:     vref=175 (index=175) op=Store(Operand { value: ValueRef(171), annotation: None }, Operand { value: ValueRef(174), annotation: None }, 1, Operand { value: ValueRef(172), annotation: None })
// CHECK:     vref=176 (index=176) op=Br(BlockRef(25), [Operand { value: ValueRef(175), annotation: None }])
// CHECK:   block 14 (inst_start=177, inst_count=7):
// CHECK:     vref=177 (index=177) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483662), annotation: None })
// CHECK:     vref=178 (index=178) op=ICmp(Eq, Operand { value: ValueRef(1073742001), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=179 (index=179) op=Store(Operand { value: ValueRef(1073742001), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(177), annotation: None })
// CHECK:     vref=180 (index=180) op=Const(4)
// CHECK:     vref=181 (index=181) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(180), annotation: None })
// CHECK:     vref=182 (index=182) op=Store(Operand { value: ValueRef(178), annotation: None }, Operand { value: ValueRef(181), annotation: None }, 1, Operand { value: ValueRef(179), annotation: None })
// CHECK:     vref=183 (index=183) op=Br(BlockRef(25), [Operand { value: ValueRef(182), annotation: None }])
// CHECK:   block 15 (inst_start=184, inst_count=7):
// CHECK:     vref=184 (index=184) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483663), annotation: None })
// CHECK:     vref=185 (index=185) op=ICmp(Eq, Operand { value: ValueRef(1073742008), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=186 (index=186) op=Store(Operand { value: ValueRef(1073742008), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(184), annotation: None })
// CHECK:     vref=187 (index=187) op=Const(4)
// CHECK:     vref=188 (index=188) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(187), annotation: None })
// CHECK:     vref=189 (index=189) op=Store(Operand { value: ValueRef(185), annotation: None }, Operand { value: ValueRef(188), annotation: None }, 1, Operand { value: ValueRef(186), annotation: None })
// CHECK:     vref=190 (index=190) op=Br(BlockRef(25), [Operand { value: ValueRef(189), annotation: None }])
// CHECK:   block 16 (inst_start=191, inst_count=7):
// CHECK:     vref=191 (index=191) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483664), annotation: None })
// CHECK:     vref=192 (index=192) op=ICmp(Eq, Operand { value: ValueRef(1073742015), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=193 (index=193) op=Store(Operand { value: ValueRef(1073742015), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(191), annotation: None })
// CHECK:     vref=194 (index=194) op=Const(4)
// CHECK:     vref=195 (index=195) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(194), annotation: None })
// CHECK:     vref=196 (index=196) op=Store(Operand { value: ValueRef(192), annotation: None }, Operand { value: ValueRef(195), annotation: None }, 1, Operand { value: ValueRef(193), annotation: None })
// CHECK:     vref=197 (index=197) op=Br(BlockRef(25), [Operand { value: ValueRef(196), annotation: None }])
// CHECK:   block 17 (inst_start=198, inst_count=7):
// CHECK:     vref=198 (index=198) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483665), annotation: None })
// CHECK:     vref=199 (index=199) op=ICmp(Eq, Operand { value: ValueRef(1073742022), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=200 (index=200) op=Store(Operand { value: ValueRef(1073742022), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(198), annotation: None })
// CHECK:     vref=201 (index=201) op=Const(4)
// CHECK:     vref=202 (index=202) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(201), annotation: None })
// CHECK:     vref=203 (index=203) op=Store(Operand { value: ValueRef(199), annotation: None }, Operand { value: ValueRef(202), annotation: None }, 1, Operand { value: ValueRef(200), annotation: None })
// CHECK:     vref=204 (index=204) op=Br(BlockRef(25), [Operand { value: ValueRef(203), annotation: None }])
// CHECK:   block 18 (inst_start=205, inst_count=7):
// CHECK:     vref=205 (index=205) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483666), annotation: None })
// CHECK:     vref=206 (index=206) op=ICmp(Eq, Operand { value: ValueRef(1073742029), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=207 (index=207) op=Store(Operand { value: ValueRef(1073742029), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(205), annotation: None })
// CHECK:     vref=208 (index=208) op=Const(4)
// CHECK:     vref=209 (index=209) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(208), annotation: None })
// CHECK:     vref=210 (index=210) op=Store(Operand { value: ValueRef(206), annotation: None }, Operand { value: ValueRef(209), annotation: None }, 1, Operand { value: ValueRef(207), annotation: None })
// CHECK:     vref=211 (index=211) op=Br(BlockRef(25), [Operand { value: ValueRef(210), annotation: None }])
// CHECK:   block 19 (inst_start=212, inst_count=7):
// CHECK:     vref=212 (index=212) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483667), annotation: None })
// CHECK:     vref=213 (index=213) op=ICmp(Eq, Operand { value: ValueRef(1073742036), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=214 (index=214) op=Store(Operand { value: ValueRef(1073742036), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(212), annotation: None })
// CHECK:     vref=215 (index=215) op=Const(4)
// CHECK:     vref=216 (index=216) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(215), annotation: None })
// CHECK:     vref=217 (index=217) op=Store(Operand { value: ValueRef(213), annotation: None }, Operand { value: ValueRef(216), annotation: None }, 1, Operand { value: ValueRef(214), annotation: None })
// CHECK:     vref=218 (index=218) op=Br(BlockRef(25), [Operand { value: ValueRef(217), annotation: None }])
// CHECK:   block 20 (inst_start=219, inst_count=7):
// CHECK:     vref=219 (index=219) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483668), annotation: None })
// CHECK:     vref=220 (index=220) op=ICmp(Eq, Operand { value: ValueRef(1073742043), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=221 (index=221) op=Store(Operand { value: ValueRef(1073742043), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(219), annotation: None })
// CHECK:     vref=222 (index=222) op=Const(4)
// CHECK:     vref=223 (index=223) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(222), annotation: None })
// CHECK:     vref=224 (index=224) op=Store(Operand { value: ValueRef(220), annotation: None }, Operand { value: ValueRef(223), annotation: None }, 1, Operand { value: ValueRef(221), annotation: None })
// CHECK:     vref=225 (index=225) op=Br(BlockRef(25), [Operand { value: ValueRef(224), annotation: None }])
// CHECK:   block 21 (inst_start=226, inst_count=7):
// CHECK:     vref=226 (index=226) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483669), annotation: None })
// CHECK:     vref=227 (index=227) op=ICmp(Eq, Operand { value: ValueRef(1073742050), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=228 (index=228) op=Store(Operand { value: ValueRef(1073742050), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(226), annotation: None })
// CHECK:     vref=229 (index=229) op=Const(4)
// CHECK:     vref=230 (index=230) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(229), annotation: None })
// CHECK:     vref=231 (index=231) op=Store(Operand { value: ValueRef(227), annotation: None }, Operand { value: ValueRef(230), annotation: None }, 1, Operand { value: ValueRef(228), annotation: None })
// CHECK:     vref=232 (index=232) op=Br(BlockRef(25), [Operand { value: ValueRef(231), annotation: None }])
// CHECK:   block 22 (inst_start=233, inst_count=7):
// CHECK:     vref=233 (index=233) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483670), annotation: None })
// CHECK:     vref=234 (index=234) op=ICmp(Eq, Operand { value: ValueRef(1073742057), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=235 (index=235) op=Store(Operand { value: ValueRef(1073742057), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(233), annotation: None })
// CHECK:     vref=236 (index=236) op=Const(4)
// CHECK:     vref=237 (index=237) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(236), annotation: None })
// CHECK:     vref=238 (index=238) op=Store(Operand { value: ValueRef(234), annotation: None }, Operand { value: ValueRef(237), annotation: None }, 1, Operand { value: ValueRef(235), annotation: None })
// CHECK:     vref=239 (index=239) op=Br(BlockRef(25), [Operand { value: ValueRef(238), annotation: None }])
// CHECK:   block 23 (inst_start=240, inst_count=7):
// CHECK:     vref=240 (index=240) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483671), annotation: None })
// CHECK:     vref=241 (index=241) op=ICmp(Eq, Operand { value: ValueRef(1073742064), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=242 (index=242) op=Store(Operand { value: ValueRef(1073742064), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(240), annotation: None })
// CHECK:     vref=243 (index=243) op=Const(4)
// CHECK:     vref=244 (index=244) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(243), annotation: None })
// CHECK:     vref=245 (index=245) op=Store(Operand { value: ValueRef(241), annotation: None }, Operand { value: ValueRef(244), annotation: None }, 1, Operand { value: ValueRef(242), annotation: None })
// CHECK:     vref=246 (index=246) op=Br(BlockRef(25), [Operand { value: ValueRef(245), annotation: None }])
// CHECK:   block 24 (inst_start=247, inst_count=7):
// CHECK:     vref=247 (index=247) op=AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483672), annotation: None })
// CHECK:     vref=248 (index=248) op=ICmp(Eq, Operand { value: ValueRef(1073742071), annotation: None }, Operand { value: ValueRef(1), annotation: None })
// CHECK:     vref=249 (index=249) op=Store(Operand { value: ValueRef(1073742071), annotation: None }, Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(247), annotation: None })
// CHECK:     vref=250 (index=250) op=Const(4)
// CHECK:     vref=251 (index=251) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(250), annotation: None })
// CHECK:     vref=252 (index=252) op=Store(Operand { value: ValueRef(248), annotation: None }, Operand { value: ValueRef(251), annotation: None }, 1, Operand { value: ValueRef(249), annotation: None })
// CHECK:     vref=253 (index=253) op=Br(BlockRef(25), [Operand { value: ValueRef(252), annotation: None }])
// CHECK:   block 25 (inst_start=254, inst_count=12):
// CHECK:     vref=254 (index=254) op=Load(Operand { value: ValueRef(5), annotation: None }, 4, Operand { value: ValueRef(2147483673), annotation: None })
// CHECK:     vref=255 (index=255) op=Const(4)
// CHECK:     vref=256 (index=256) op=PtrAdd(Operand { value: ValueRef(5), annotation: None }, Operand { value: ValueRef(255), annotation: None })
// CHECK:     vref=257 (index=257) op=Load(Operand { value: ValueRef(256), annotation: None }, 1, Operand { value: ValueRef(2147483673), annotation: None })
// CHECK:     vref=258 (index=258) op=Const(1)
// CHECK:     vref=259 (index=259) op=Const(0)
// CHECK:     vref=260 (index=260) op=Select(Operand { value: ValueRef(257), annotation: None }, Operand { value: ValueRef(258), annotation: None }, Operand { value: ValueRef(259), annotation: None })
// CHECK:     vref=261 (index=261) op=Const(255)
// CHECK:     vref=262 (index=262) op=And(Operand { value: ValueRef(260), annotation: None }, Operand { value: ValueRef(261), annotation: None })
// CHECK:     vref=263 (index=263) op=Const(0)
// CHECK:     vref=264 (index=264) op=ICmp(Eq, Operand { value: ValueRef(262), annotation: None }, Operand { value: ValueRef(263), annotation: None })
// CHECK:     vref=265 (index=265) op=BrIf(Operand { value: ValueRef(264), annotation: None }, BlockRef(27), [Operand { value: ValueRef(2147483673), annotation: None }], BlockRef(26), [Operand { value: ValueRef(2147483673), annotation: None }])
// CHECK:   block 26 (inst_start=266, inst_count=8):
// CHECK:     vref=266 (index=266) op=Const(0)
// CHECK:     vref=267 (index=267) op=Store(Operand { value: ValueRef(266), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 8, Operand { value: ValueRef(2147483674), annotation: None })
// CHECK:     vref=268 (index=268) op=Const(4)
// CHECK:     vref=269 (index=269) op=PtrAdd(Operand { value: ValueRef(6), annotation: None }, Operand { value: ValueRef(268), annotation: None })
// CHECK:     vref=270 (index=270) op=Store(Operand { value: ValueRef(254), annotation: None }, Operand { value: ValueRef(269), annotation: None }, 4, Operand { value: ValueRef(267), annotation: None })
// CHECK:     vref=271 (index=271) op=Const(0)
// CHECK:     vref=272 (index=272) op=Store(Operand { value: ValueRef(271), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 4, Operand { value: ValueRef(270), annotation: None })
// CHECK:     vref=273 (index=273) op=Br(BlockRef(28), [Operand { value: ValueRef(272), annotation: None }])
// CHECK:   block 27 (inst_start=274, inst_count=8):
// CHECK:     vref=274 (index=274) op=Const(0)
// CHECK:     vref=275 (index=275) op=Store(Operand { value: ValueRef(274), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 8, Operand { value: ValueRef(2147483675), annotation: None })
// CHECK:     vref=276 (index=276) op=Const(4)
// CHECK:     vref=277 (index=277) op=PtrAdd(Operand { value: ValueRef(6), annotation: None }, Operand { value: ValueRef(276), annotation: None })
// CHECK:     vref=278 (index=278) op=Store(Operand { value: ValueRef(254), annotation: None }, Operand { value: ValueRef(277), annotation: None }, 4, Operand { value: ValueRef(275), annotation: None })
// CHECK:     vref=279 (index=279) op=Const(1)
// CHECK:     vref=280 (index=280) op=Store(Operand { value: ValueRef(279), annotation: None }, Operand { value: ValueRef(6), annotation: None }, 4, Operand { value: ValueRef(278), annotation: None })
// CHECK:     vref=281 (index=281) op=Br(BlockRef(28), [Operand { value: ValueRef(280), annotation: None }])
// CHECK:   block 28 (inst_start=282, inst_count=1):
// CHECK:     vref=282 (index=282) op=Ret(None, Operand { value: ValueRef(2147483676), annotation: None })
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
// CHECK:     [3] Const(0)
// CHECK:     [4] Const(0)
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
// CHECK: warning: isel failed on vref=ValueRef(149) op AtomicCmpXchg(Operand { value: ValueRef(0), annotation: None }, Operand { value: ValueRef(1), annotation: None }, Operand { value: ValueRef(2), annotation: None }, SeqCst, SeqCst, Operand { value: ValueRef(2147483658), annotation: None })
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
// CHECK: func @atomic_compare_exchange(%ptr: ptr, %expected: int:u32, %new: int:u32) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:u32 = param %expected
// CHECK:     v3: int:u32 = param %new
// CHECK:     v4: ptr = stack_slot 8
// CHECK:     v5: mem = store.8 v1, v4, v0
// CHECK:     v6: ptr = load.8 v4, v5
// CHECK:     v7: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v8: mem = call v7(v6, v2, v3), v5
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     ret v11
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
// CHECK:     v6: mem, v7: int:i64 = rmw.add.seqcst v5, v2, v4
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
// CHECK:     v5: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops
// CHECK:     v6: mem, v7: int:u32 = call v5(v4), v3 -> int
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
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
// CHECK:     v6: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v7: mem = call v6(v5, v2), v4
// CHECK:     v8: int:i64 = iconst 0
// CHECK:     br bb1(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v10
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
// CHECK:     v6: mem, v7: int:i64 = rmw.xchg.seqcst v5, v2, v4
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
