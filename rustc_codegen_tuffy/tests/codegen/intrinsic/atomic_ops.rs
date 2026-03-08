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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops(%self: ptr) -> int {
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
// CHECK:     v10: int = load.1 v8, v9
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
// CHECK: warning: IR verification failed for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops] return type: Int type requires annotation
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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %val: int) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int = param %val
// CHECK:     v3: int:i64 = iconst 0
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 1
// CHECK:     v9: mem = store.1 v3, v8, v0
// CHECK:     v10: int = load.1 v8, v9
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
// CHECK: warning: IR verification failed for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops] param 1: Int type requires annotation
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
// CHECK: func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops(%self: ptr, %old: int, %new: int) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %self
// CHECK:     v2: int = param %old
// CHECK:     v3: int = param %new
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
// CHECK:     v14: int = load.1 v12, v13
// CHECK:     v15: int:i64 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb2(v13), bb29(v13)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: ptr = stack_slot 1
// CHECK:     v20: mem = store.1 v5, v19, v18
// CHECK:     v21: int = load.1 v19, v20
// CHECK:     v22: int:i64 = iconst 1
// CHECK:     v23: bool = icmp.eq v21, v22
// CHECK:     brif v23, bb8(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26: ptr = stack_slot 1
// CHECK:     v27: mem = store.1 v5, v26, v25
// CHECK:     v28: int = load.1 v26, v27
// CHECK:     v29: int:i64 = iconst 0
// CHECK:     v30: bool = icmp.eq v28, v29
// CHECK:     brif v30, bb24(v27), bb34(v27)
// CHECK:
// CHECK:   bb3(v32: mem):
// CHECK:     v33: ptr = stack_slot 1
// CHECK:     v34: mem = store.1 v5, v33, v32
// CHECK:     v35: int = load.1 v33, v34
// CHECK:     v36: int:i64 = iconst 0
// CHECK:     v37: bool = icmp.eq v35, v36
// CHECK:     brif v37, bb21(v34), bb36(v34)
// CHECK:
// CHECK:   bb4(v39: mem):
// CHECK:     v40: ptr = stack_slot 1
// CHECK:     v41: mem = store.1 v5, v40, v39
// CHECK:     v42: int = load.1 v40, v41
// CHECK:     v43: int:i64 = iconst 0
// CHECK:     v44: bool = icmp.eq v42, v43
// CHECK:     brif v44, bb18(v41), bb38(v41)
// CHECK:
// CHECK:   bb5(v46: mem):
// CHECK:     v47: ptr = stack_slot 1
// CHECK:     v48: mem = store.1 v5, v47, v46
// CHECK:     v49: int = load.1 v47, v48
// CHECK:     v50: int:i64 = iconst 0
// CHECK:     v51: bool = icmp.eq v49, v50
// CHECK:     brif v51, bb15(v48), bb40(v48)
// CHECK:
// CHECK:   bb6(v53: mem):
// CHECK:     v54: ptr = stack_slot 1
// CHECK:     v55: mem = store.1 v5, v54, v53
// CHECK:     v56: int = load.1 v54, v55
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
// CHECK:     v250: int = load.4 v6, v249
// CHECK:     v251: int:i64 = iconst 4
// CHECK:     v252: ptr = ptradd v6, v251
// CHECK:     v253: bool = load.1 v252, v249
// CHECK:     v254: int:u64 = bool_to_int v253
// CHECK:     v255: int:i64 = iconst 255
// CHECK:     v256: int:u64 = and v254, v255
// CHECK:     v257: int:i64 = iconst 0
// CHECK:     v258: bool = icmp.eq v256, v257
// CHECK:     brif v258, bb27(v249), bb26(v249)
// CHECK:
// CHECK:   bb26(v260: mem):
// CHECK:     v261: int:i64 = iconst 0
// CHECK:     v262: mem = store.8 v261, v7, v260
// CHECK:     v263: int:i64 = iconst 4
// CHECK:     v264: ptr = ptradd v7, v263
// CHECK:     v265: mem = store.4 v250, v264, v262
// CHECK:     v266: int:i64 = iconst 0
// CHECK:     v267: mem = store.4 v266, v7, v265
// CHECK:     br bb28(v267)
// CHECK:
// CHECK:   bb27(v269: mem):
// CHECK:     v270: int:i64 = iconst 0
// CHECK:     v271: mem = store.8 v270, v7, v269
// CHECK:     v272: int:i64 = iconst 4
// CHECK:     v273: ptr = ptradd v7, v272
// CHECK:     v274: mem = store.4 v250, v273, v271
// CHECK:     v275: int:i64 = iconst 1
// CHECK:     v276: mem = store.4 v275, v7, v274
// CHECK:     br bb28(v276)
// CHECK:
// CHECK:   bb28(v278: mem):
// CHECK:     ret v278
// CHECK:
// CHECK:   bb29(v280: mem):
// CHECK:     v281: int:i64 = iconst 1
// CHECK:     v282: bool = icmp.eq v14, v281
// CHECK:     brif v282, bb4(v280), bb30(v280)
// CHECK:
// CHECK:   bb30(v284: mem):
// CHECK:     v285: int:i64 = iconst 2
// CHECK:     v286: bool = icmp.eq v14, v285
// CHECK:     brif v286, bb3(v284), bb31(v284)
// CHECK:
// CHECK:   bb31(v288: mem):
// CHECK:     v289: int:i64 = iconst 3
// CHECK:     v290: bool = icmp.eq v14, v289
// CHECK:     brif v290, bb5(v288), bb32(v288)
// CHECK:
// CHECK:   bb32(v292: mem):
// CHECK:     v293: int:i64 = iconst 4
// CHECK:     v294: bool = icmp.eq v14, v293
// CHECK:     brif v294, bb6(v292), bb7(v292)
// CHECK:
// CHECK:   bb33(v296: mem):
// CHECK:     v297: int:i64 = iconst 3
// CHECK:     v298: bool = icmp.eq v21, v297
// CHECK:     brif v298, bb9(v296), bb7(v296)
// CHECK:
// CHECK:   bb34(v300: mem):
// CHECK:     v301: int:i64 = iconst 2
// CHECK:     v302: bool = icmp.eq v28, v301
// CHECK:     brif v302, bb23(v300), bb35(v300)
// CHECK:
// CHECK:   bb35(v304: mem):
// CHECK:     v305: int:i64 = iconst 4
// CHECK:     v306: bool = icmp.eq v28, v305
// CHECK:     brif v306, bb22(v304), bb1(v304)
// CHECK:
// CHECK:   bb36(v308: mem):
// CHECK:     v309: int:i64 = iconst 2
// CHECK:     v310: bool = icmp.eq v35, v309
// CHECK:     brif v310, bb20(v308), bb37(v308)
// CHECK:
// CHECK:   bb37(v312: mem):
// CHECK:     v313: int:i64 = iconst 4
// CHECK:     v314: bool = icmp.eq v35, v313
// CHECK:     brif v314, bb19(v312), bb1(v312)
// CHECK:
// CHECK:   bb38(v316: mem):
// CHECK:     v317: int:i64 = iconst 2
// CHECK:     v318: bool = icmp.eq v42, v317
// CHECK:     brif v318, bb17(v316), bb39(v316)
// CHECK:
// CHECK:   bb39(v320: mem):
// CHECK:     v321: int:i64 = iconst 4
// CHECK:     v322: bool = icmp.eq v42, v321
// CHECK:     brif v322, bb16(v320), bb1(v320)
// CHECK:
// CHECK:   bb40(v324: mem):
// CHECK:     v325: int:i64 = iconst 2
// CHECK:     v326: bool = icmp.eq v49, v325
// CHECK:     brif v326, bb14(v324), bb41(v324)
// CHECK:
// CHECK:   bb41(v328: mem):
// CHECK:     v329: int:i64 = iconst 4
// CHECK:     v330: bool = icmp.eq v49, v329
// CHECK:     brif v330, bb13(v328), bb1(v328)
// CHECK:
// CHECK:   bb42(v332: mem):
// CHECK:     v333: int:i64 = iconst 2
// CHECK:     v334: bool = icmp.eq v56, v333
// CHECK:     brif v334, bb11(v332), bb43(v332)
// CHECK:
// CHECK:   bb43(v336: mem):
// CHECK:     v337: int:i64 = iconst 4
// CHECK:     v338: bool = icmp.eq v56, v337
// CHECK:     brif v338, bb10(v336), bb1(v336)
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for _RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops] param 1: Int type requires annotation
// CHECK:   [func @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops] param 2: Int type requires annotation
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
// CHECK: func @atomic_compare_exchange(%ptr: ptr, %expected: int, %new: int) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int = param %expected
// CHECK:     v3: int = param %new
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
// CHECK: warning: IR verification failed for atomic_compare_exchange, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @atomic_compare_exchange] param 1: Int type requires annotation
// CHECK:   [func @atomic_compare_exchange] param 2: Int type requires annotation
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
// CHECK: func @atomic_fetch_add(%ptr: ptr, %val: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int = param %val
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
// CHECK: warning: IR verification failed for atomic_fetch_add, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @atomic_fetch_add] param 1: Int type requires annotation
// CHECK:   [func @atomic_fetch_add] return type: Int type requires annotation
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
// CHECK: func @atomic_load_relaxed(%ptr: ptr) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: mem = store.8 v1, v2, v0
// CHECK:     v4: ptr = load.8 v2, v3
// CHECK:     v5: ptr = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops
// CHECK:     v6: mem, v7: int = call v5(v4), v3 -> int
// CHECK:     br bb1(v6)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v7, v9
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for atomic_load_relaxed, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @atomic_load_relaxed] return type: Int type requires annotation
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
// CHECK: func @atomic_store_release(%ptr: ptr, %val: int) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int = param %val
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
// CHECK: warning: IR verification failed for atomic_store_release, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @atomic_store_release] param 1: Int type requires annotation
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
// CHECK: func @atomic_swap(%ptr: ptr, %val: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int = param %val
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
// CHECK: warning: IR verification failed for atomic_swap, emitting stub
// CHECK:   verification failed with 2 error(s):
// CHECK:   [func @atomic_swap] param 1: Int type requires annotation
// CHECK:   [func @atomic_swap] return type: Int type requires annotation
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
