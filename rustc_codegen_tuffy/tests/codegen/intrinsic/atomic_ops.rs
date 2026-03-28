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
// CHECK: data @.Lloc.3 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.2]
// CHECK: data @.Lstr.4 = "there is no such thing as a release load"
// CHECK: data @.Lstr.5 = "there is no such thing as a release load"
// CHECK: data @.Lloc_file.6 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.7 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.6]
// CHECK: func @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic11atomic_loadmECsh6zX7Z7540N_10atomic_ops(ptr, int:i8) -> int:u32 {
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
// CHECK:     v28: int:u64 = ptrtoaddr v27
// CHECK:     v29: ptr = symbol_addr @.Lstr.1
// CHECK:     v30: mem = store.8 v28, v7, v26
// CHECK:     v31: int:i64 = iconst 0
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v7, v32
// CHECK:     v34: mem = store.8 v31, v33, v30
// CHECK:     v35: int:i64 = load.8 v7, v34
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v7, v36
// CHECK:     v38: int:i64 = load.8 v37, v34
// CHECK:     v39: ptr = symbol_addr @.Lloc.3
// CHECK:     v40: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v41: mem = call v40(v35, v38, v39), v34
// CHECK:     v42: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v44: mem):
// CHECK:     v45: ptr = symbol_addr @.Lstr.4
// CHECK:     v46: int:i64 = iconst 40
// CHECK:     v47: mem = store.8 v45, v9, v44
// CHECK:     v48: int:i64 = iconst 8
// CHECK:     v49: ptr = ptradd v9, v48
// CHECK:     v50: mem = store.8 v46, v49, v47
// CHECK:     v51: int:i64 = iconst 40
// CHECK:     v52: int:i64 = iconst 8
// CHECK:     v53: ptr = ptradd v9, v52
// CHECK:     v54: mem = store.8 v51, v53, v50
// CHECK:     v55: ptr = load.8 v9, v54
// CHECK:     v56: int:u64 = ptrtoaddr v55
// CHECK:     v57: ptr = symbol_addr @.Lstr.5
// CHECK:     v58: mem = store.8 v56, v6, v54
// CHECK:     v59: int:i64 = iconst 0
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v6, v60
// CHECK:     v62: mem = store.8 v59, v61, v58
// CHECK:     v63: int:i64 = load.8 v6, v62
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v6, v64
// CHECK:     v66: int:i64 = load.8 v65, v62
// CHECK:     v67: ptr = symbol_addr @.Lloc.7
// CHECK:     v68: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v69: mem = call v68(v63, v66, v67), v62
// CHECK:     v70: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v72: mem):
// CHECK:     v73: mem, v74: int:i64 = load.atomic.seqcst v1, v72
// CHECK:     v75: mem = store.4 v74, v5, v73
// CHECK:     br bb7(v75)
// CHECK:
// CHECK:   bb5(v77: mem):
// CHECK:     v78: mem, v79: int:i64 = load.atomic.seqcst v1, v77
// CHECK:     v80: mem = store.4 v79, v5, v78
// CHECK:     br bb7(v80)
// CHECK:
// CHECK:   bb6(v82: mem):
// CHECK:     v83: mem, v84: int:i64 = load.atomic.seqcst v1, v82
// CHECK:     v85: mem = store.4 v84, v5, v83
// CHECK:     br bb7(v85)
// CHECK:
// CHECK:   bb7(v87: mem):
// CHECK:     v88: int:u32 = load.4 v5, v87
// CHECK:     ret v88, v87
// CHECK:
// CHECK:   bb8(v90: mem):
// CHECK:     v91: int:i64 = iconst 1
// CHECK:     v92: bool = icmp.eq v10, v91
// CHECK:     brif v92, bb3(v90), bb9(v90)
// CHECK:
// CHECK:   bb9(v94: mem):
// CHECK:     v95: int:i64 = iconst 2
// CHECK:     v96: bool = icmp.eq v10, v95
// CHECK:     brif v96, bb5(v94), bb10(v94)
// CHECK:
// CHECK:   bb10(v98: mem):
// CHECK:     v99: int:i64 = iconst 3
// CHECK:     v100: bool = icmp.eq v10, v99
// CHECK:     brif v100, bb2(v98), bb11(v98)
// CHECK:
// CHECK:   bb11(v102: mem):
// CHECK:     v103: int:i64 = iconst 4
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
// CHECK: data @.Lloc.11 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.10]
// CHECK: data @.Lstr.12 = "there is no such thing as an acquire store"
// CHECK: data @.Lstr.13 = "there is no such thing as an acquire store"
// CHECK: data @.Lloc_file.14 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.15 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.14]
// CHECK: func @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic12atomic_storemECsh6zX7Z7540N_10atomic_ops(ptr, int:u32, int:i8) {
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
// CHECK:     v28: int:u64 = ptrtoaddr v27
// CHECK:     v29: ptr = symbol_addr @.Lstr.9
// CHECK:     v30: mem = store.8 v28, v7, v26
// CHECK:     v31: int:i64 = iconst 0
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v7, v32
// CHECK:     v34: mem = store.8 v31, v33, v30
// CHECK:     v35: int:i64 = load.8 v7, v34
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v7, v36
// CHECK:     v38: int:i64 = load.8 v37, v34
// CHECK:     v39: ptr = symbol_addr @.Lloc.11
// CHECK:     v40: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v41: mem = call v40(v35, v38, v39), v34
// CHECK:     v42: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v44: mem):
// CHECK:     v45: ptr = symbol_addr @.Lstr.12
// CHECK:     v46: int:i64 = iconst 42
// CHECK:     v47: mem = store.8 v45, v9, v44
// CHECK:     v48: int:i64 = iconst 8
// CHECK:     v49: ptr = ptradd v9, v48
// CHECK:     v50: mem = store.8 v46, v49, v47
// CHECK:     v51: int:i64 = iconst 42
// CHECK:     v52: int:i64 = iconst 8
// CHECK:     v53: ptr = ptradd v9, v52
// CHECK:     v54: mem = store.8 v51, v53, v50
// CHECK:     v55: ptr = load.8 v9, v54
// CHECK:     v56: int:u64 = ptrtoaddr v55
// CHECK:     v57: ptr = symbol_addr @.Lstr.13
// CHECK:     v58: mem = store.8 v56, v6, v54
// CHECK:     v59: int:i64 = iconst 0
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v6, v60
// CHECK:     v62: mem = store.8 v59, v61, v58
// CHECK:     v63: int:i64 = load.8 v6, v62
// CHECK:     v64: int:i64 = iconst 8
// CHECK:     v65: ptr = ptradd v6, v64
// CHECK:     v66: int:i64 = load.8 v65, v62
// CHECK:     v67: ptr = symbol_addr @.Lloc.15
// CHECK:     v68: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v69: mem = call v68(v63, v66, v67), v62
// CHECK:     v70: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v72: mem):
// CHECK:     v73: mem = store.atomic.seqcst v2, v1, v72
// CHECK:     br bb7(v73)
// CHECK:
// CHECK:   bb5(v75: mem):
// CHECK:     v76: mem = store.atomic.seqcst v2, v1, v75
// CHECK:     br bb7(v76)
// CHECK:
// CHECK:   bb6(v78: mem):
// CHECK:     v79: mem = store.atomic.seqcst v2, v1, v78
// CHECK:     br bb7(v79)
// CHECK:
// CHECK:   bb7(v81: mem):
// CHECK:     ret v81
// CHECK:
// CHECK:   bb8(v83: mem):
// CHECK:     v84: int:i64 = iconst 1
// CHECK:     v85: bool = icmp.eq v10, v84
// CHECK:     brif v85, bb5(v83), bb9(v83)
// CHECK:
// CHECK:   bb9(v87: mem):
// CHECK:     v88: int:i64 = iconst 2
// CHECK:     v89: bool = icmp.eq v10, v88
// CHECK:     brif v89, bb3(v87), bb10(v87)
// CHECK:
// CHECK:   bb10(v91: mem):
// CHECK:     v92: int:i64 = iconst 3
// CHECK:     v93: bool = icmp.eq v10, v92
// CHECK:     brif v93, bb2(v91), bb11(v91)
// CHECK:
// CHECK:   bb11(v95: mem):
// CHECK:     v96: int:i64 = iconst 4
// CHECK:     v97: bool = icmp.eq v10, v96
// CHECK:     brif v97, bb4(v95), bb1(v95)
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
// CHECK: data @.Lloc.19 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.18]
// CHECK: data @.Lstr.20 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lstr.21 = "there is no such thing as an acquire-release failure ordering"
// CHECK: data @.Lloc_file.22 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.23 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0" relocs [0: @.Lloc_file.22]
// CHECK: func @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic23atomic_compare_exchangemECsh6zX7Z7540N_10atomic_ops(ptr, ptr, int:u32, int:u32, int:i8, int:i8) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: ptr = param 1
// CHECK:     v4: int:u32 = param 2
// CHECK:     v5: int:u32 = param 3
// CHECK:     v6: int:i8 = param 4
// CHECK:     v7: ptr = stack_slot 1
// CHECK:     v8: int:i8 = param 5
// CHECK:     v9: ptr = stack_slot 1
// CHECK:     v10: mem = store.1 v6, v7, v0
// CHECK:     v11: mem = store.1 v8, v9, v10
// CHECK:     v12: ptr = stack_slot 8
// CHECK:     v13: ptr = stack_slot 16
// CHECK:     v14: ptr = stack_slot 16
// CHECK:     v15: ptr = stack_slot 16
// CHECK:     v16: ptr = stack_slot 16
// CHECK:     v17: int:i8 = load.1 v7, v11
// CHECK:     v18: int:i64 = iconst 0
// CHECK:     v19: bool = icmp.eq v17, v18
// CHECK:     brif v19, bb2(v11), bb29(v11)
// CHECK:
// CHECK:   bb1(v21: mem):
// CHECK:     v22: int:i8 = load.1 v9, v21
// CHECK:     v23: int:i64 = iconst 1
// CHECK:     v24: bool = icmp.eq v22, v23
// CHECK:     brif v24, bb8(v21), bb33(v21)
// CHECK:
// CHECK:   bb2(v26: mem):
// CHECK:     v27: int:i8 = load.1 v9, v26
// CHECK:     v28: int:i64 = iconst 0
// CHECK:     v29: bool = icmp.eq v27, v28
// CHECK:     brif v29, bb24(v26), bb34(v26)
// CHECK:
// CHECK:   bb3(v31: mem):
// CHECK:     v32: int:i8 = load.1 v9, v31
// CHECK:     v33: int:i64 = iconst 0
// CHECK:     v34: bool = icmp.eq v32, v33
// CHECK:     brif v34, bb21(v31), bb36(v31)
// CHECK:
// CHECK:   bb4(v36: mem):
// CHECK:     v37: int:i8 = load.1 v9, v36
// CHECK:     v38: int:i64 = iconst 0
// CHECK:     v39: bool = icmp.eq v37, v38
// CHECK:     brif v39, bb18(v36), bb38(v36)
// CHECK:
// CHECK:   bb5(v41: mem):
// CHECK:     v42: int:i8 = load.1 v9, v41
// CHECK:     v43: int:i64 = iconst 0
// CHECK:     v44: bool = icmp.eq v42, v43
// CHECK:     brif v44, bb15(v41), bb40(v41)
// CHECK:
// CHECK:   bb6(v46: mem):
// CHECK:     v47: int:i8 = load.1 v9, v46
// CHECK:     v48: int:i64 = iconst 0
// CHECK:     v49: bool = icmp.eq v47, v48
// CHECK:     brif v49, bb12(v46), bb42(v46)
// CHECK:
// CHECK:   bb7(v51: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v53: mem):
// CHECK:     v54: ptr = symbol_addr @.Lstr.16
// CHECK:     v55: int:i64 = iconst 52
// CHECK:     v56: mem = store.8 v54, v15, v53
// CHECK:     v57: int:i64 = iconst 8
// CHECK:     v58: ptr = ptradd v15, v57
// CHECK:     v59: mem = store.8 v55, v58, v56
// CHECK:     v60: int:i64 = iconst 52
// CHECK:     v61: int:i64 = iconst 8
// CHECK:     v62: ptr = ptradd v15, v61
// CHECK:     v63: mem = store.8 v60, v62, v59
// CHECK:     v64: ptr = load.8 v15, v63
// CHECK:     v65: int:u64 = ptrtoaddr v64
// CHECK:     v66: ptr = symbol_addr @.Lstr.17
// CHECK:     v67: mem = store.8 v65, v14, v63
// CHECK:     v68: int:i64 = iconst 0
// CHECK:     v69: int:i64 = iconst 8
// CHECK:     v70: ptr = ptradd v14, v69
// CHECK:     v71: mem = store.8 v68, v70, v67
// CHECK:     v72: int:i64 = load.8 v14, v71
// CHECK:     v73: int:i64 = iconst 8
// CHECK:     v74: ptr = ptradd v14, v73
// CHECK:     v75: int:i64 = load.8 v74, v71
// CHECK:     v76: ptr = symbol_addr @.Lloc.19
// CHECK:     v77: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v78: mem = call v77(v72, v75, v76), v71
// CHECK:     v79: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb9(v81: mem):
// CHECK:     v82: ptr = symbol_addr @.Lstr.20
// CHECK:     v83: int:i64 = iconst 61
// CHECK:     v84: mem = store.8 v82, v16, v81
// CHECK:     v85: int:i64 = iconst 8
// CHECK:     v86: ptr = ptradd v16, v85
// CHECK:     v87: mem = store.8 v83, v86, v84
// CHECK:     v88: int:i64 = iconst 61
// CHECK:     v89: int:i64 = iconst 8
// CHECK:     v90: ptr = ptradd v16, v89
// CHECK:     v91: mem = store.8 v88, v90, v87
// CHECK:     v92: ptr = load.8 v16, v91
// CHECK:     v93: int:u64 = ptrtoaddr v92
// CHECK:     v94: ptr = symbol_addr @.Lstr.21
// CHECK:     v95: mem = store.8 v93, v13, v91
// CHECK:     v96: int:i64 = iconst 0
// CHECK:     v97: int:i64 = iconst 8
// CHECK:     v98: ptr = ptradd v13, v97
// CHECK:     v99: mem = store.8 v96, v98, v95
// CHECK:     v100: int:i64 = load.8 v13, v99
// CHECK:     v101: int:i64 = iconst 8
// CHECK:     v102: ptr = ptradd v13, v101
// CHECK:     v103: int:i64 = load.8 v102, v99
// CHECK:     v104: ptr = symbol_addr @.Lloc.23
// CHECK:     v105: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v106: mem = call v105(v100, v103, v104), v99
// CHECK:     v107: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v109: mem):
// CHECK:     v110: mem, v111: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v109
// CHECK:     v112: bool = icmp.eq v111, v4
// CHECK:     v113: mem = store.4 v111, v12, v110
// CHECK:     v114: int:i64 = iconst 4
// CHECK:     v115: ptr = ptradd v12, v114
// CHECK:     v116: mem = store.1 v112, v115, v113
// CHECK:     br bb25(v116)
// CHECK:
// CHECK:   bb11(v118: mem):
// CHECK:     v119: mem, v120: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v118
// CHECK:     v121: bool = icmp.eq v120, v4
// CHECK:     v122: mem = store.4 v120, v12, v119
// CHECK:     v123: int:i64 = iconst 4
// CHECK:     v124: ptr = ptradd v12, v123
// CHECK:     v125: mem = store.1 v121, v124, v122
// CHECK:     br bb25(v125)
// CHECK:
// CHECK:   bb12(v127: mem):
// CHECK:     v128: mem, v129: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v127
// CHECK:     v130: bool = icmp.eq v129, v4
// CHECK:     v131: mem = store.4 v129, v12, v128
// CHECK:     v132: int:i64 = iconst 4
// CHECK:     v133: ptr = ptradd v12, v132
// CHECK:     v134: mem = store.1 v130, v133, v131
// CHECK:     br bb25(v134)
// CHECK:
// CHECK:   bb13(v136: mem):
// CHECK:     v137: mem, v138: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v136
// CHECK:     v139: bool = icmp.eq v138, v4
// CHECK:     v140: mem = store.4 v138, v12, v137
// CHECK:     v141: int:i64 = iconst 4
// CHECK:     v142: ptr = ptradd v12, v141
// CHECK:     v143: mem = store.1 v139, v142, v140
// CHECK:     br bb25(v143)
// CHECK:
// CHECK:   bb14(v145: mem):
// CHECK:     v146: mem, v147: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v145
// CHECK:     v148: bool = icmp.eq v147, v4
// CHECK:     v149: mem = store.4 v147, v12, v146
// CHECK:     v150: int:i64 = iconst 4
// CHECK:     v151: ptr = ptradd v12, v150
// CHECK:     v152: mem = store.1 v148, v151, v149
// CHECK:     br bb25(v152)
// CHECK:
// CHECK:   bb15(v154: mem):
// CHECK:     v155: mem, v156: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v154
// CHECK:     v157: bool = icmp.eq v156, v4
// CHECK:     v158: mem = store.4 v156, v12, v155
// CHECK:     v159: int:i64 = iconst 4
// CHECK:     v160: ptr = ptradd v12, v159
// CHECK:     v161: mem = store.1 v157, v160, v158
// CHECK:     br bb25(v161)
// CHECK:
// CHECK:   bb16(v163: mem):
// CHECK:     v164: mem, v165: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v163
// CHECK:     v166: bool = icmp.eq v165, v4
// CHECK:     v167: mem = store.4 v165, v12, v164
// CHECK:     v168: int:i64 = iconst 4
// CHECK:     v169: ptr = ptradd v12, v168
// CHECK:     v170: mem = store.1 v166, v169, v167
// CHECK:     br bb25(v170)
// CHECK:
// CHECK:   bb17(v172: mem):
// CHECK:     v173: mem, v174: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v172
// CHECK:     v175: bool = icmp.eq v174, v4
// CHECK:     v176: mem = store.4 v174, v12, v173
// CHECK:     v177: int:i64 = iconst 4
// CHECK:     v178: ptr = ptradd v12, v177
// CHECK:     v179: mem = store.1 v175, v178, v176
// CHECK:     br bb25(v179)
// CHECK:
// CHECK:   bb18(v181: mem):
// CHECK:     v182: mem, v183: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v181
// CHECK:     v184: bool = icmp.eq v183, v4
// CHECK:     v185: mem = store.4 v183, v12, v182
// CHECK:     v186: int:i64 = iconst 4
// CHECK:     v187: ptr = ptradd v12, v186
// CHECK:     v188: mem = store.1 v184, v187, v185
// CHECK:     br bb25(v188)
// CHECK:
// CHECK:   bb19(v190: mem):
// CHECK:     v191: mem, v192: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v190
// CHECK:     v193: bool = icmp.eq v192, v4
// CHECK:     v194: mem = store.4 v192, v12, v191
// CHECK:     v195: int:i64 = iconst 4
// CHECK:     v196: ptr = ptradd v12, v195
// CHECK:     v197: mem = store.1 v193, v196, v194
// CHECK:     br bb25(v197)
// CHECK:
// CHECK:   bb20(v199: mem):
// CHECK:     v200: mem, v201: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v199
// CHECK:     v202: bool = icmp.eq v201, v4
// CHECK:     v203: mem = store.4 v201, v12, v200
// CHECK:     v204: int:i64 = iconst 4
// CHECK:     v205: ptr = ptradd v12, v204
// CHECK:     v206: mem = store.1 v202, v205, v203
// CHECK:     br bb25(v206)
// CHECK:
// CHECK:   bb21(v208: mem):
// CHECK:     v209: mem, v210: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v208
// CHECK:     v211: bool = icmp.eq v210, v4
// CHECK:     v212: mem = store.4 v210, v12, v209
// CHECK:     v213: int:i64 = iconst 4
// CHECK:     v214: ptr = ptradd v12, v213
// CHECK:     v215: mem = store.1 v211, v214, v212
// CHECK:     br bb25(v215)
// CHECK:
// CHECK:   bb22(v217: mem):
// CHECK:     v218: mem, v219: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v217
// CHECK:     v220: bool = icmp.eq v219, v4
// CHECK:     v221: mem = store.4 v219, v12, v218
// CHECK:     v222: int:i64 = iconst 4
// CHECK:     v223: ptr = ptradd v12, v222
// CHECK:     v224: mem = store.1 v220, v223, v221
// CHECK:     br bb25(v224)
// CHECK:
// CHECK:   bb23(v226: mem):
// CHECK:     v227: mem, v228: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v226
// CHECK:     v229: bool = icmp.eq v228, v4
// CHECK:     v230: mem = store.4 v228, v12, v227
// CHECK:     v231: int:i64 = iconst 4
// CHECK:     v232: ptr = ptradd v12, v231
// CHECK:     v233: mem = store.1 v229, v232, v230
// CHECK:     br bb25(v233)
// CHECK:
// CHECK:   bb24(v235: mem):
// CHECK:     v236: mem, v237: int:i64 = cmpxchg.seqcst.seqcst v3, v4, v5, v235
// CHECK:     v238: bool = icmp.eq v237, v4
// CHECK:     v239: mem = store.4 v237, v12, v236
// CHECK:     v240: int:i64 = iconst 4
// CHECK:     v241: ptr = ptradd v12, v240
// CHECK:     v242: mem = store.1 v238, v241, v239
// CHECK:     br bb25(v242)
// CHECK:
// CHECK:   bb25(v244: mem):
// CHECK:     v245: int:i32 = load.4 v12, v244
// CHECK:     v246: int:i64 = iconst 4
// CHECK:     v247: ptr = ptradd v12, v246
// CHECK:     v248: bool = load.1 v247, v244
// CHECK:     v249: int:u64 = iconst 1
// CHECK:     v250: int:u64 = iconst 0
// CHECK:     v251: int:u64 = select v248, v249, v250
// CHECK:     v252: int:i64 = iconst 255
// CHECK:     v253: int:u64 = and v251, v252
// CHECK:     v254: int:i8 = iconst 0
// CHECK:     v255: bool = icmp.eq v253, v254
// CHECK:     brif v255, bb27(v244), bb26(v244)
// CHECK:
// CHECK:   bb26(v257: mem):
// CHECK:     v258: int:i64 = iconst 0
// CHECK:     v259: mem = store.8 v258, v2, v257
// CHECK:     v260: int:i64 = iconst 4
// CHECK:     v261: ptr = ptradd v2, v260
// CHECK:     v262: mem = store.4 v245, v261, v259
// CHECK:     v263: int:i64 = iconst 0
// CHECK:     v264: mem = store.4 v263, v2, v262
// CHECK:     br bb28(v264)
// CHECK:
// CHECK:   bb27(v266: mem):
// CHECK:     v267: int:i64 = iconst 0
// CHECK:     v268: mem = store.8 v267, v2, v266
// CHECK:     v269: int:i64 = iconst 4
// CHECK:     v270: ptr = ptradd v2, v269
// CHECK:     v271: mem = store.4 v245, v270, v268
// CHECK:     v272: int:i64 = iconst 1
// CHECK:     v273: mem = store.4 v272, v2, v271
// CHECK:     br bb28(v273)
// CHECK:
// CHECK:   bb28(v275: mem):
// CHECK:     v276: int:i64 = iconst 8
// CHECK:     v277: mem = memcopy v1:align8, v2:align8, v276, v275
// CHECK:     ret v1, v277
// CHECK:
// CHECK:   bb29(v279: mem):
// CHECK:     v280: int:i64 = iconst 1
// CHECK:     v281: bool = icmp.eq v17, v280
// CHECK:     brif v281, bb4(v279), bb30(v279)
// CHECK:
// CHECK:   bb30(v283: mem):
// CHECK:     v284: int:i64 = iconst 2
// CHECK:     v285: bool = icmp.eq v17, v284
// CHECK:     brif v285, bb3(v283), bb31(v283)
// CHECK:
// CHECK:   bb31(v287: mem):
// CHECK:     v288: int:i64 = iconst 3
// CHECK:     v289: bool = icmp.eq v17, v288
// CHECK:     brif v289, bb5(v287), bb32(v287)
// CHECK:
// CHECK:   bb32(v291: mem):
// CHECK:     v292: int:i64 = iconst 4
// CHECK:     v293: bool = icmp.eq v17, v292
// CHECK:     brif v293, bb6(v291), bb7(v291)
// CHECK:
// CHECK:   bb33(v295: mem):
// CHECK:     v296: int:i64 = iconst 3
// CHECK:     v297: bool = icmp.eq v22, v296
// CHECK:     brif v297, bb9(v295), bb7(v295)
// CHECK:
// CHECK:   bb34(v299: mem):
// CHECK:     v300: int:i64 = iconst 2
// CHECK:     v301: bool = icmp.eq v27, v300
// CHECK:     brif v301, bb23(v299), bb35(v299)
// CHECK:
// CHECK:   bb35(v303: mem):
// CHECK:     v304: int:i64 = iconst 4
// CHECK:     v305: bool = icmp.eq v27, v304
// CHECK:     brif v305, bb22(v303), bb1(v303)
// CHECK:
// CHECK:   bb36(v307: mem):
// CHECK:     v308: int:i64 = iconst 2
// CHECK:     v309: bool = icmp.eq v32, v308
// CHECK:     brif v309, bb20(v307), bb37(v307)
// CHECK:
// CHECK:   bb37(v311: mem):
// CHECK:     v312: int:i64 = iconst 4
// CHECK:     v313: bool = icmp.eq v32, v312
// CHECK:     brif v313, bb19(v311), bb1(v311)
// CHECK:
// CHECK:   bb38(v315: mem):
// CHECK:     v316: int:i64 = iconst 2
// CHECK:     v317: bool = icmp.eq v37, v316
// CHECK:     brif v317, bb17(v315), bb39(v315)
// CHECK:
// CHECK:   bb39(v319: mem):
// CHECK:     v320: int:i64 = iconst 4
// CHECK:     v321: bool = icmp.eq v37, v320
// CHECK:     brif v321, bb16(v319), bb1(v319)
// CHECK:
// CHECK:   bb40(v323: mem):
// CHECK:     v324: int:i64 = iconst 2
// CHECK:     v325: bool = icmp.eq v42, v324
// CHECK:     brif v325, bb14(v323), bb41(v323)
// CHECK:
// CHECK:   bb41(v327: mem):
// CHECK:     v328: int:i64 = iconst 4
// CHECK:     v329: bool = icmp.eq v42, v328
// CHECK:     brif v329, bb13(v327), bb1(v327)
// CHECK:
// CHECK:   bb42(v331: mem):
// CHECK:     v332: int:i64 = iconst 2
// CHECK:     v333: bool = icmp.eq v47, v332
// CHECK:     brif v333, bb11(v331), bb43(v331)
// CHECK:
// CHECK:   bb43(v335: mem):
// CHECK:     v336: int:i64 = iconst 4
// CHECK:     v337: bool = icmp.eq v47, v336
// CHECK:     brif v337, bb10(v335), bb1(v335)
// CHECK: }
// CHECK:
// CHECK: === ISel failure dump for _RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic23atomic_compare_exchangemECsh6zX7Z7540N_10atomic_ops ===
// CHECK:   block 0 (inst_start=0, inst_count=20):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=StackSlot(8)
// CHECK:     vref=2 (index=2) op=Param(1)
// CHECK:     vref=3 (index=3) op=Param(2)
// CHECK:     vref=4 (index=4) op=Param(3)
// CHECK:     vref=5 (index=5) op=Param(4)
// CHECK:     vref=6 (index=6) op=StackSlot(1)
// CHECK:     vref=7 (index=7) op=Param(5)
// CHECK:     vref=8 (index=8) op=StackSlot(1)
// CHECK:     vref=9 (index=9) op=Store(Operand { value: ValueRef(5), annotation: None }, PtrOperand(Operand { value: ValueRef(6), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     vref=10 (index=10) op=Store(Operand { value: ValueRef(7), annotation: None }, PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(9), annotation: None }))
// CHECK:     vref=11 (index=11) op=StackSlot(8)
// CHECK:     vref=12 (index=12) op=StackSlot(16)
// CHECK:     vref=13 (index=13) op=StackSlot(16)
// CHECK:     vref=14 (index=14) op=StackSlot(16)
// CHECK:     vref=15 (index=15) op=StackSlot(16)
// CHECK:     vref=16 (index=16) op=Load(PtrOperand(Operand { value: ValueRef(6), annotation: None }), 1, MemOperand(Operand { value: ValueRef(10), annotation: None }))
// CHECK:     vref=17 (index=17) op=Const(0)
// CHECK:     vref=18 (index=18) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(17), annotation: None }))
// CHECK:     vref=19 (index=19) op=BrIf(BoolOperand(Operand { value: ValueRef(18), annotation: None }), BlockRef(2), [Operand { value: ValueRef(10), annotation: None }], BlockRef(29), [Operand { value: ValueRef(10), annotation: None }])
// CHECK:   block 1 (inst_start=32, inst_count=4):
// CHECK:     vref=32 (index=32) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK:     vref=33 (index=33) op=Const(1)
// CHECK:     vref=34 (index=34) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(32), annotation: None }), IntOperand(Operand { value: ValueRef(33), annotation: None }))
// CHECK:     vref=35 (index=35) op=BrIf(BoolOperand(Operand { value: ValueRef(34), annotation: None }), BlockRef(8), [Operand { value: ValueRef(2147483649), annotation: None }], BlockRef(33), [Operand { value: ValueRef(2147483649), annotation: None }])
// CHECK:   block 2 (inst_start=39, inst_count=4):
// CHECK:     vref=39 (index=39) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483650), annotation: None }))
// CHECK:     vref=40 (index=40) op=Const(0)
// CHECK:     vref=41 (index=41) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(40), annotation: None }))
// CHECK:     vref=42 (index=42) op=BrIf(BoolOperand(Operand { value: ValueRef(41), annotation: None }), BlockRef(24), [Operand { value: ValueRef(2147483650), annotation: None }], BlockRef(34), [Operand { value: ValueRef(2147483650), annotation: None }])
// CHECK:   block 3 (inst_start=49, inst_count=4):
// CHECK:     vref=49 (index=49) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483651), annotation: None }))
// CHECK:     vref=50 (index=50) op=Const(0)
// CHECK:     vref=51 (index=51) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(50), annotation: None }))
// CHECK:     vref=52 (index=52) op=BrIf(BoolOperand(Operand { value: ValueRef(51), annotation: None }), BlockRef(21), [Operand { value: ValueRef(2147483651), annotation: None }], BlockRef(36), [Operand { value: ValueRef(2147483651), annotation: None }])
// CHECK:   block 4 (inst_start=59, inst_count=4):
// CHECK:     vref=59 (index=59) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483652), annotation: None }))
// CHECK:     vref=60 (index=60) op=Const(0)
// CHECK:     vref=61 (index=61) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(59), annotation: None }), IntOperand(Operand { value: ValueRef(60), annotation: None }))
// CHECK:     vref=62 (index=62) op=BrIf(BoolOperand(Operand { value: ValueRef(61), annotation: None }), BlockRef(18), [Operand { value: ValueRef(2147483652), annotation: None }], BlockRef(38), [Operand { value: ValueRef(2147483652), annotation: None }])
// CHECK:   block 5 (inst_start=69, inst_count=4):
// CHECK:     vref=69 (index=69) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483653), annotation: None }))
// CHECK:     vref=70 (index=70) op=Const(0)
// CHECK:     vref=71 (index=71) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(69), annotation: None }), IntOperand(Operand { value: ValueRef(70), annotation: None }))
// CHECK:     vref=72 (index=72) op=BrIf(BoolOperand(Operand { value: ValueRef(71), annotation: None }), BlockRef(15), [Operand { value: ValueRef(2147483653), annotation: None }], BlockRef(40), [Operand { value: ValueRef(2147483653), annotation: None }])
// CHECK:   block 6 (inst_start=79, inst_count=4):
// CHECK:     vref=79 (index=79) op=Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483654), annotation: None }))
// CHECK:     vref=80 (index=80) op=Const(0)
// CHECK:     vref=81 (index=81) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(79), annotation: None }), IntOperand(Operand { value: ValueRef(80), annotation: None }))
// CHECK:     vref=82 (index=82) op=BrIf(BoolOperand(Operand { value: ValueRef(81), annotation: None }), BlockRef(12), [Operand { value: ValueRef(2147483654), annotation: None }], BlockRef(42), [Operand { value: ValueRef(2147483654), annotation: None }])
// CHECK:   block 7 (inst_start=89, inst_count=1):
// CHECK:     vref=89 (index=89) op=Unreachable
// CHECK:   block 8 (inst_start=90, inst_count=27):
// CHECK:     vref=90 (index=90) op=SymbolAddr(SymbolId(8))
// CHECK:     vref=91 (index=91) op=Const(52)
// CHECK:     vref=92 (index=92) op=Store(Operand { value: ValueRef(90), annotation: None }, PtrOperand(Operand { value: ValueRef(14), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483656), annotation: None }))
// CHECK:     vref=93 (index=93) op=Const(8)
// CHECK:     vref=94 (index=94) op=PtrAdd(PtrOperand(Operand { value: ValueRef(14), annotation: None }), IntOperand(Operand { value: ValueRef(93), annotation: None }))
// CHECK:     vref=95 (index=95) op=Store(Operand { value: ValueRef(91), annotation: None }, PtrOperand(Operand { value: ValueRef(94), annotation: None }), 8, MemOperand(Operand { value: ValueRef(92), annotation: None }))
// CHECK:     vref=96 (index=96) op=Const(52)
// CHECK:     vref=97 (index=97) op=Const(8)
// CHECK:     vref=98 (index=98) op=PtrAdd(PtrOperand(Operand { value: ValueRef(14), annotation: None }), IntOperand(Operand { value: ValueRef(97), annotation: None }))
// CHECK:     vref=99 (index=99) op=Store(Operand { value: ValueRef(96), annotation: None }, PtrOperand(Operand { value: ValueRef(98), annotation: None }), 8, MemOperand(Operand { value: ValueRef(95), annotation: None }))
// CHECK:     vref=100 (index=100) op=Load(PtrOperand(Operand { value: ValueRef(14), annotation: None }), 8, MemOperand(Operand { value: ValueRef(99), annotation: None }))
// CHECK:     vref=101 (index=101) op=PtrToAddr(PtrOperand(Operand { value: ValueRef(100), annotation: None }))
// CHECK:     vref=102 (index=102) op=SymbolAddr(SymbolId(9))
// CHECK:     vref=103 (index=103) op=Store(Operand { value: ValueRef(101), annotation: None }, PtrOperand(Operand { value: ValueRef(13), annotation: None }), 8, MemOperand(Operand { value: ValueRef(99), annotation: None }))
// CHECK:     vref=104 (index=104) op=Const(0)
// CHECK:     vref=105 (index=105) op=Const(8)
// CHECK:     vref=106 (index=106) op=PtrAdd(PtrOperand(Operand { value: ValueRef(13), annotation: None }), IntOperand(Operand { value: ValueRef(105), annotation: None }))
// CHECK:     vref=107 (index=107) op=Store(Operand { value: ValueRef(104), annotation: None }, PtrOperand(Operand { value: ValueRef(106), annotation: None }), 8, MemOperand(Operand { value: ValueRef(103), annotation: None }))
// CHECK:     vref=108 (index=108) op=Load(PtrOperand(Operand { value: ValueRef(13), annotation: None }), 8, MemOperand(Operand { value: ValueRef(107), annotation: None }))
// CHECK:     vref=109 (index=109) op=Const(8)
// CHECK:     vref=110 (index=110) op=PtrAdd(PtrOperand(Operand { value: ValueRef(13), annotation: None }), IntOperand(Operand { value: ValueRef(109), annotation: None }))
// CHECK:     vref=111 (index=111) op=Load(PtrOperand(Operand { value: ValueRef(110), annotation: None }), 8, MemOperand(Operand { value: ValueRef(107), annotation: None }))
// CHECK:     vref=112 (index=112) op=SymbolAddr(SymbolId(11))
// CHECK:     vref=113 (index=113) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=114 (index=114) op=Call(PtrOperand(Operand { value: ValueRef(113), annotation: None }), [Operand { value: ValueRef(108), annotation: None }, Operand { value: ValueRef(111), annotation: None }, Operand { value: ValueRef(112), annotation: None }], MemOperand(Operand { value: ValueRef(107), annotation: None }))
// CHECK:     vref=115 (index=115) op=Const(0)
// CHECK:     vref=116 (index=116) op=Unreachable
// CHECK:   block 9 (inst_start=117, inst_count=27):
// CHECK:     vref=117 (index=117) op=SymbolAddr(SymbolId(13))
// CHECK:     vref=118 (index=118) op=Const(61)
// CHECK:     vref=119 (index=119) op=Store(Operand { value: ValueRef(117), annotation: None }, PtrOperand(Operand { value: ValueRef(15), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483657), annotation: None }))
// CHECK:     vref=120 (index=120) op=Const(8)
// CHECK:     vref=121 (index=121) op=PtrAdd(PtrOperand(Operand { value: ValueRef(15), annotation: None }), IntOperand(Operand { value: ValueRef(120), annotation: None }))
// CHECK:     vref=122 (index=122) op=Store(Operand { value: ValueRef(118), annotation: None }, PtrOperand(Operand { value: ValueRef(121), annotation: None }), 8, MemOperand(Operand { value: ValueRef(119), annotation: None }))
// CHECK:     vref=123 (index=123) op=Const(61)
// CHECK:     vref=124 (index=124) op=Const(8)
// CHECK:     vref=125 (index=125) op=PtrAdd(PtrOperand(Operand { value: ValueRef(15), annotation: None }), IntOperand(Operand { value: ValueRef(124), annotation: None }))
// CHECK:     vref=126 (index=126) op=Store(Operand { value: ValueRef(123), annotation: None }, PtrOperand(Operand { value: ValueRef(125), annotation: None }), 8, MemOperand(Operand { value: ValueRef(122), annotation: None }))
// CHECK:     vref=127 (index=127) op=Load(PtrOperand(Operand { value: ValueRef(15), annotation: None }), 8, MemOperand(Operand { value: ValueRef(126), annotation: None }))
// CHECK:     vref=128 (index=128) op=PtrToAddr(PtrOperand(Operand { value: ValueRef(127), annotation: None }))
// CHECK:     vref=129 (index=129) op=SymbolAddr(SymbolId(14))
// CHECK:     vref=130 (index=130) op=Store(Operand { value: ValueRef(128), annotation: None }, PtrOperand(Operand { value: ValueRef(12), annotation: None }), 8, MemOperand(Operand { value: ValueRef(126), annotation: None }))
// CHECK:     vref=131 (index=131) op=Const(0)
// CHECK:     vref=132 (index=132) op=Const(8)
// CHECK:     vref=133 (index=133) op=PtrAdd(PtrOperand(Operand { value: ValueRef(12), annotation: None }), IntOperand(Operand { value: ValueRef(132), annotation: None }))
// CHECK:     vref=134 (index=134) op=Store(Operand { value: ValueRef(131), annotation: None }, PtrOperand(Operand { value: ValueRef(133), annotation: None }), 8, MemOperand(Operand { value: ValueRef(130), annotation: None }))
// CHECK:     vref=135 (index=135) op=Load(PtrOperand(Operand { value: ValueRef(12), annotation: None }), 8, MemOperand(Operand { value: ValueRef(134), annotation: None }))
// CHECK:     vref=136 (index=136) op=Const(8)
// CHECK:     vref=137 (index=137) op=PtrAdd(PtrOperand(Operand { value: ValueRef(12), annotation: None }), IntOperand(Operand { value: ValueRef(136), annotation: None }))
// CHECK:     vref=138 (index=138) op=Load(PtrOperand(Operand { value: ValueRef(137), annotation: None }), 8, MemOperand(Operand { value: ValueRef(134), annotation: None }))
// CHECK:     vref=139 (index=139) op=SymbolAddr(SymbolId(16))
// CHECK:     vref=140 (index=140) op=SymbolAddr(SymbolId(12))
// CHECK:     vref=141 (index=141) op=Call(PtrOperand(Operand { value: ValueRef(140), annotation: None }), [Operand { value: ValueRef(135), annotation: None }, Operand { value: ValueRef(138), annotation: None }, Operand { value: ValueRef(139), annotation: None }], MemOperand(Operand { value: ValueRef(134), annotation: None }))
// CHECK:     vref=142 (index=142) op=Const(0)
// CHECK:     vref=143 (index=143) op=Unreachable
// CHECK:   block 10 (inst_start=144, inst_count=7):
// CHECK:     vref=144 (index=144) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483658), annotation: None }))
// CHECK:     vref=145 (index=145) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073741968), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=146 (index=146) op=Store(Operand { value: ValueRef(1073741968), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(144), annotation: None }))
// CHECK:     vref=147 (index=147) op=Const(4)
// CHECK:     vref=148 (index=148) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(147), annotation: None }))
// CHECK:     vref=149 (index=149) op=Store(Operand { value: ValueRef(145), annotation: None }, PtrOperand(Operand { value: ValueRef(148), annotation: None }), 1, MemOperand(Operand { value: ValueRef(146), annotation: None }))
// CHECK:     vref=150 (index=150) op=Br(BlockRef(25), [Operand { value: ValueRef(149), annotation: None }])
// CHECK:   block 11 (inst_start=151, inst_count=7):
// CHECK:     vref=151 (index=151) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483659), annotation: None }))
// CHECK:     vref=152 (index=152) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073741975), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=153 (index=153) op=Store(Operand { value: ValueRef(1073741975), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(151), annotation: None }))
// CHECK:     vref=154 (index=154) op=Const(4)
// CHECK:     vref=155 (index=155) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(154), annotation: None }))
// CHECK:     vref=156 (index=156) op=Store(Operand { value: ValueRef(152), annotation: None }, PtrOperand(Operand { value: ValueRef(155), annotation: None }), 1, MemOperand(Operand { value: ValueRef(153), annotation: None }))
// CHECK:     vref=157 (index=157) op=Br(BlockRef(25), [Operand { value: ValueRef(156), annotation: None }])
// CHECK:   block 12 (inst_start=158, inst_count=7):
// CHECK:     vref=158 (index=158) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483660), annotation: None }))
// CHECK:     vref=159 (index=159) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073741982), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=160 (index=160) op=Store(Operand { value: ValueRef(1073741982), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(158), annotation: None }))
// CHECK:     vref=161 (index=161) op=Const(4)
// CHECK:     vref=162 (index=162) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(161), annotation: None }))
// CHECK:     vref=163 (index=163) op=Store(Operand { value: ValueRef(159), annotation: None }, PtrOperand(Operand { value: ValueRef(162), annotation: None }), 1, MemOperand(Operand { value: ValueRef(160), annotation: None }))
// CHECK:     vref=164 (index=164) op=Br(BlockRef(25), [Operand { value: ValueRef(163), annotation: None }])
// CHECK:   block 13 (inst_start=165, inst_count=7):
// CHECK:     vref=165 (index=165) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483661), annotation: None }))
// CHECK:     vref=166 (index=166) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073741989), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=167 (index=167) op=Store(Operand { value: ValueRef(1073741989), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(165), annotation: None }))
// CHECK:     vref=168 (index=168) op=Const(4)
// CHECK:     vref=169 (index=169) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(168), annotation: None }))
// CHECK:     vref=170 (index=170) op=Store(Operand { value: ValueRef(166), annotation: None }, PtrOperand(Operand { value: ValueRef(169), annotation: None }), 1, MemOperand(Operand { value: ValueRef(167), annotation: None }))
// CHECK:     vref=171 (index=171) op=Br(BlockRef(25), [Operand { value: ValueRef(170), annotation: None }])
// CHECK:   block 14 (inst_start=172, inst_count=7):
// CHECK:     vref=172 (index=172) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483662), annotation: None }))
// CHECK:     vref=173 (index=173) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073741996), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=174 (index=174) op=Store(Operand { value: ValueRef(1073741996), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(172), annotation: None }))
// CHECK:     vref=175 (index=175) op=Const(4)
// CHECK:     vref=176 (index=176) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(175), annotation: None }))
// CHECK:     vref=177 (index=177) op=Store(Operand { value: ValueRef(173), annotation: None }, PtrOperand(Operand { value: ValueRef(176), annotation: None }), 1, MemOperand(Operand { value: ValueRef(174), annotation: None }))
// CHECK:     vref=178 (index=178) op=Br(BlockRef(25), [Operand { value: ValueRef(177), annotation: None }])
// CHECK:   block 15 (inst_start=179, inst_count=7):
// CHECK:     vref=179 (index=179) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483663), annotation: None }))
// CHECK:     vref=180 (index=180) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742003), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=181 (index=181) op=Store(Operand { value: ValueRef(1073742003), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(179), annotation: None }))
// CHECK:     vref=182 (index=182) op=Const(4)
// CHECK:     vref=183 (index=183) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(182), annotation: None }))
// CHECK:     vref=184 (index=184) op=Store(Operand { value: ValueRef(180), annotation: None }, PtrOperand(Operand { value: ValueRef(183), annotation: None }), 1, MemOperand(Operand { value: ValueRef(181), annotation: None }))
// CHECK:     vref=185 (index=185) op=Br(BlockRef(25), [Operand { value: ValueRef(184), annotation: None }])
// CHECK:   block 16 (inst_start=186, inst_count=7):
// CHECK:     vref=186 (index=186) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483664), annotation: None }))
// CHECK:     vref=187 (index=187) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742010), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=188 (index=188) op=Store(Operand { value: ValueRef(1073742010), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(186), annotation: None }))
// CHECK:     vref=189 (index=189) op=Const(4)
// CHECK:     vref=190 (index=190) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(189), annotation: None }))
// CHECK:     vref=191 (index=191) op=Store(Operand { value: ValueRef(187), annotation: None }, PtrOperand(Operand { value: ValueRef(190), annotation: None }), 1, MemOperand(Operand { value: ValueRef(188), annotation: None }))
// CHECK:     vref=192 (index=192) op=Br(BlockRef(25), [Operand { value: ValueRef(191), annotation: None }])
// CHECK:   block 17 (inst_start=193, inst_count=7):
// CHECK:     vref=193 (index=193) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483665), annotation: None }))
// CHECK:     vref=194 (index=194) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742017), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=195 (index=195) op=Store(Operand { value: ValueRef(1073742017), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(193), annotation: None }))
// CHECK:     vref=196 (index=196) op=Const(4)
// CHECK:     vref=197 (index=197) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(196), annotation: None }))
// CHECK:     vref=198 (index=198) op=Store(Operand { value: ValueRef(194), annotation: None }, PtrOperand(Operand { value: ValueRef(197), annotation: None }), 1, MemOperand(Operand { value: ValueRef(195), annotation: None }))
// CHECK:     vref=199 (index=199) op=Br(BlockRef(25), [Operand { value: ValueRef(198), annotation: None }])
// CHECK:   block 18 (inst_start=200, inst_count=7):
// CHECK:     vref=200 (index=200) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483666), annotation: None }))
// CHECK:     vref=201 (index=201) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742024), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=202 (index=202) op=Store(Operand { value: ValueRef(1073742024), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(200), annotation: None }))
// CHECK:     vref=203 (index=203) op=Const(4)
// CHECK:     vref=204 (index=204) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(203), annotation: None }))
// CHECK:     vref=205 (index=205) op=Store(Operand { value: ValueRef(201), annotation: None }, PtrOperand(Operand { value: ValueRef(204), annotation: None }), 1, MemOperand(Operand { value: ValueRef(202), annotation: None }))
// CHECK:     vref=206 (index=206) op=Br(BlockRef(25), [Operand { value: ValueRef(205), annotation: None }])
// CHECK:   block 19 (inst_start=207, inst_count=7):
// CHECK:     vref=207 (index=207) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483667), annotation: None }))
// CHECK:     vref=208 (index=208) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742031), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=209 (index=209) op=Store(Operand { value: ValueRef(1073742031), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(207), annotation: None }))
// CHECK:     vref=210 (index=210) op=Const(4)
// CHECK:     vref=211 (index=211) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(210), annotation: None }))
// CHECK:     vref=212 (index=212) op=Store(Operand { value: ValueRef(208), annotation: None }, PtrOperand(Operand { value: ValueRef(211), annotation: None }), 1, MemOperand(Operand { value: ValueRef(209), annotation: None }))
// CHECK:     vref=213 (index=213) op=Br(BlockRef(25), [Operand { value: ValueRef(212), annotation: None }])
// CHECK:   block 20 (inst_start=214, inst_count=7):
// CHECK:     vref=214 (index=214) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483668), annotation: None }))
// CHECK:     vref=215 (index=215) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742038), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=216 (index=216) op=Store(Operand { value: ValueRef(1073742038), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(214), annotation: None }))
// CHECK:     vref=217 (index=217) op=Const(4)
// CHECK:     vref=218 (index=218) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(217), annotation: None }))
// CHECK:     vref=219 (index=219) op=Store(Operand { value: ValueRef(215), annotation: None }, PtrOperand(Operand { value: ValueRef(218), annotation: None }), 1, MemOperand(Operand { value: ValueRef(216), annotation: None }))
// CHECK:     vref=220 (index=220) op=Br(BlockRef(25), [Operand { value: ValueRef(219), annotation: None }])
// CHECK:   block 21 (inst_start=221, inst_count=7):
// CHECK:     vref=221 (index=221) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483669), annotation: None }))
// CHECK:     vref=222 (index=222) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742045), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=223 (index=223) op=Store(Operand { value: ValueRef(1073742045), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(221), annotation: None }))
// CHECK:     vref=224 (index=224) op=Const(4)
// CHECK:     vref=225 (index=225) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(224), annotation: None }))
// CHECK:     vref=226 (index=226) op=Store(Operand { value: ValueRef(222), annotation: None }, PtrOperand(Operand { value: ValueRef(225), annotation: None }), 1, MemOperand(Operand { value: ValueRef(223), annotation: None }))
// CHECK:     vref=227 (index=227) op=Br(BlockRef(25), [Operand { value: ValueRef(226), annotation: None }])
// CHECK:   block 22 (inst_start=228, inst_count=7):
// CHECK:     vref=228 (index=228) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483670), annotation: None }))
// CHECK:     vref=229 (index=229) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742052), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=230 (index=230) op=Store(Operand { value: ValueRef(1073742052), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(228), annotation: None }))
// CHECK:     vref=231 (index=231) op=Const(4)
// CHECK:     vref=232 (index=232) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(231), annotation: None }))
// CHECK:     vref=233 (index=233) op=Store(Operand { value: ValueRef(229), annotation: None }, PtrOperand(Operand { value: ValueRef(232), annotation: None }), 1, MemOperand(Operand { value: ValueRef(230), annotation: None }))
// CHECK:     vref=234 (index=234) op=Br(BlockRef(25), [Operand { value: ValueRef(233), annotation: None }])
// CHECK:   block 23 (inst_start=235, inst_count=7):
// CHECK:     vref=235 (index=235) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483671), annotation: None }))
// CHECK:     vref=236 (index=236) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742059), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=237 (index=237) op=Store(Operand { value: ValueRef(1073742059), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(235), annotation: None }))
// CHECK:     vref=238 (index=238) op=Const(4)
// CHECK:     vref=239 (index=239) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(238), annotation: None }))
// CHECK:     vref=240 (index=240) op=Store(Operand { value: ValueRef(236), annotation: None }, PtrOperand(Operand { value: ValueRef(239), annotation: None }), 1, MemOperand(Operand { value: ValueRef(237), annotation: None }))
// CHECK:     vref=241 (index=241) op=Br(BlockRef(25), [Operand { value: ValueRef(240), annotation: None }])
// CHECK:   block 24 (inst_start=242, inst_count=7):
// CHECK:     vref=242 (index=242) op=AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483672), annotation: None }))
// CHECK:     vref=243 (index=243) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(1073742066), annotation: None }), IntOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=244 (index=244) op=Store(Operand { value: ValueRef(1073742066), annotation: None }, PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(242), annotation: None }))
// CHECK:     vref=245 (index=245) op=Const(4)
// CHECK:     vref=246 (index=246) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(245), annotation: None }))
// CHECK:     vref=247 (index=247) op=Store(Operand { value: ValueRef(243), annotation: None }, PtrOperand(Operand { value: ValueRef(246), annotation: None }), 1, MemOperand(Operand { value: ValueRef(244), annotation: None }))
// CHECK:     vref=248 (index=248) op=Br(BlockRef(25), [Operand { value: ValueRef(247), annotation: None }])
// CHECK:   block 25 (inst_start=249, inst_count=12):
// CHECK:     vref=249 (index=249) op=Load(PtrOperand(Operand { value: ValueRef(11), annotation: None }), 4, MemOperand(Operand { value: ValueRef(2147483673), annotation: None }))
// CHECK:     vref=250 (index=250) op=Const(4)
// CHECK:     vref=251 (index=251) op=PtrAdd(PtrOperand(Operand { value: ValueRef(11), annotation: None }), IntOperand(Operand { value: ValueRef(250), annotation: None }))
// CHECK:     vref=252 (index=252) op=Load(PtrOperand(Operand { value: ValueRef(251), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483673), annotation: None }))
// CHECK:     vref=253 (index=253) op=Const(1)
// CHECK:     vref=254 (index=254) op=Const(0)
// CHECK:     vref=255 (index=255) op=Select(BoolOperand(Operand { value: ValueRef(252), annotation: None }), Operand { value: ValueRef(253), annotation: None }, Operand { value: ValueRef(254), annotation: None })
// CHECK:     vref=256 (index=256) op=Const(255)
// CHECK:     vref=257 (index=257) op=And(IntOperand(Operand { value: ValueRef(255), annotation: None }), IntOperand(Operand { value: ValueRef(256), annotation: None }))
// CHECK:     vref=258 (index=258) op=Const(0)
// CHECK:     vref=259 (index=259) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(257), annotation: None }), IntOperand(Operand { value: ValueRef(258), annotation: None }))
// CHECK:     vref=260 (index=260) op=BrIf(BoolOperand(Operand { value: ValueRef(259), annotation: None }), BlockRef(27), [Operand { value: ValueRef(2147483673), annotation: None }], BlockRef(26), [Operand { value: ValueRef(2147483673), annotation: None }])
// CHECK:   block 26 (inst_start=261, inst_count=8):
// CHECK:     vref=261 (index=261) op=Const(0)
// CHECK:     vref=262 (index=262) op=Store(Operand { value: ValueRef(261), annotation: None }, PtrOperand(Operand { value: ValueRef(1), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483674), annotation: None }))
// CHECK:     vref=263 (index=263) op=Const(4)
// CHECK:     vref=264 (index=264) op=PtrAdd(PtrOperand(Operand { value: ValueRef(1), annotation: None }), IntOperand(Operand { value: ValueRef(263), annotation: None }))
// CHECK:     vref=265 (index=265) op=Store(Operand { value: ValueRef(249), annotation: None }, PtrOperand(Operand { value: ValueRef(264), annotation: None }), 4, MemOperand(Operand { value: ValueRef(262), annotation: None }))
// CHECK:     vref=266 (index=266) op=Const(0)
// CHECK:     vref=267 (index=267) op=Store(Operand { value: ValueRef(266), annotation: None }, PtrOperand(Operand { value: ValueRef(1), annotation: None }), 4, MemOperand(Operand { value: ValueRef(265), annotation: None }))
// CHECK:     vref=268 (index=268) op=Br(BlockRef(28), [Operand { value: ValueRef(267), annotation: None }])
// CHECK:   block 27 (inst_start=269, inst_count=8):
// CHECK:     vref=269 (index=269) op=Const(0)
// CHECK:     vref=270 (index=270) op=Store(Operand { value: ValueRef(269), annotation: None }, PtrOperand(Operand { value: ValueRef(1), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483675), annotation: None }))
// CHECK:     vref=271 (index=271) op=Const(4)
// CHECK:     vref=272 (index=272) op=PtrAdd(PtrOperand(Operand { value: ValueRef(1), annotation: None }), IntOperand(Operand { value: ValueRef(271), annotation: None }))
// CHECK:     vref=273 (index=273) op=Store(Operand { value: ValueRef(249), annotation: None }, PtrOperand(Operand { value: ValueRef(272), annotation: None }), 4, MemOperand(Operand { value: ValueRef(270), annotation: None }))
// CHECK:     vref=274 (index=274) op=Const(1)
// CHECK:     vref=275 (index=275) op=Store(Operand { value: ValueRef(274), annotation: None }, PtrOperand(Operand { value: ValueRef(1), annotation: None }), 4, MemOperand(Operand { value: ValueRef(273), annotation: None }))
// CHECK:     vref=276 (index=276) op=Br(BlockRef(28), [Operand { value: ValueRef(275), annotation: None }])
// CHECK:   block 28 (inst_start=277, inst_count=3):
// CHECK:     vref=277 (index=277) op=Const(8)
// CHECK:     vref=278 (index=278) op=MemCopy(PtrOperand(Operand { value: ValueRef(0), annotation: Some(Align(8)) }), PtrOperand(Operand { value: ValueRef(1), annotation: Some(Align(8)) }), IntOperand(Operand { value: ValueRef(277), annotation: None }), MemOperand(Operand { value: ValueRef(2147483676), annotation: None }))
// CHECK:     vref=279 (index=279) op=Ret(Some(Operand { value: ValueRef(0), annotation: None }), MemOperand(Operand { value: ValueRef(278), annotation: None }))
// CHECK:   block 29 (inst_start=20, inst_count=3):
// CHECK:     vref=20 (index=20) op=Const(1)
// CHECK:     vref=21 (index=21) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(20), annotation: None }))
// CHECK:     vref=22 (index=22) op=BrIf(BoolOperand(Operand { value: ValueRef(21), annotation: None }), BlockRef(4), [Operand { value: ValueRef(2147483677), annotation: None }], BlockRef(30), [Operand { value: ValueRef(2147483677), annotation: None }])
// CHECK:   block 30 (inst_start=23, inst_count=3):
// CHECK:     vref=23 (index=23) op=Const(2)
// CHECK:     vref=24 (index=24) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(23), annotation: None }))
// CHECK:     vref=25 (index=25) op=BrIf(BoolOperand(Operand { value: ValueRef(24), annotation: None }), BlockRef(3), [Operand { value: ValueRef(2147483678), annotation: None }], BlockRef(31), [Operand { value: ValueRef(2147483678), annotation: None }])
// CHECK:   block 31 (inst_start=26, inst_count=3):
// CHECK:     vref=26 (index=26) op=Const(3)
// CHECK:     vref=27 (index=27) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(26), annotation: None }))
// CHECK:     vref=28 (index=28) op=BrIf(BoolOperand(Operand { value: ValueRef(27), annotation: None }), BlockRef(5), [Operand { value: ValueRef(2147483679), annotation: None }], BlockRef(32), [Operand { value: ValueRef(2147483679), annotation: None }])
// CHECK:   block 32 (inst_start=29, inst_count=3):
// CHECK:     vref=29 (index=29) op=Const(4)
// CHECK:     vref=30 (index=30) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(29), annotation: None }))
// CHECK:     vref=31 (index=31) op=BrIf(BoolOperand(Operand { value: ValueRef(30), annotation: None }), BlockRef(6), [Operand { value: ValueRef(2147483680), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483680), annotation: None }])
// CHECK:   block 33 (inst_start=36, inst_count=3):
// CHECK:     vref=36 (index=36) op=Const(3)
// CHECK:     vref=37 (index=37) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(32), annotation: None }), IntOperand(Operand { value: ValueRef(36), annotation: None }))
// CHECK:     vref=38 (index=38) op=BrIf(BoolOperand(Operand { value: ValueRef(37), annotation: None }), BlockRef(9), [Operand { value: ValueRef(2147483681), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483681), annotation: None }])
// CHECK:   block 34 (inst_start=43, inst_count=3):
// CHECK:     vref=43 (index=43) op=Const(2)
// CHECK:     vref=44 (index=44) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(43), annotation: None }))
// CHECK:     vref=45 (index=45) op=BrIf(BoolOperand(Operand { value: ValueRef(44), annotation: None }), BlockRef(23), [Operand { value: ValueRef(2147483682), annotation: None }], BlockRef(35), [Operand { value: ValueRef(2147483682), annotation: None }])
// CHECK:   block 35 (inst_start=46, inst_count=3):
// CHECK:     vref=46 (index=46) op=Const(4)
// CHECK:     vref=47 (index=47) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(46), annotation: None }))
// CHECK:     vref=48 (index=48) op=BrIf(BoolOperand(Operand { value: ValueRef(47), annotation: None }), BlockRef(22), [Operand { value: ValueRef(2147483683), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483683), annotation: None }])
// CHECK:   block 36 (inst_start=53, inst_count=3):
// CHECK:     vref=53 (index=53) op=Const(2)
// CHECK:     vref=54 (index=54) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(53), annotation: None }))
// CHECK:     vref=55 (index=55) op=BrIf(BoolOperand(Operand { value: ValueRef(54), annotation: None }), BlockRef(20), [Operand { value: ValueRef(2147483684), annotation: None }], BlockRef(37), [Operand { value: ValueRef(2147483684), annotation: None }])
// CHECK:   block 37 (inst_start=56, inst_count=3):
// CHECK:     vref=56 (index=56) op=Const(4)
// CHECK:     vref=57 (index=57) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(56), annotation: None }))
// CHECK:     vref=58 (index=58) op=BrIf(BoolOperand(Operand { value: ValueRef(57), annotation: None }), BlockRef(19), [Operand { value: ValueRef(2147483685), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483685), annotation: None }])
// CHECK:   block 38 (inst_start=63, inst_count=3):
// CHECK:     vref=63 (index=63) op=Const(2)
// CHECK:     vref=64 (index=64) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(59), annotation: None }), IntOperand(Operand { value: ValueRef(63), annotation: None }))
// CHECK:     vref=65 (index=65) op=BrIf(BoolOperand(Operand { value: ValueRef(64), annotation: None }), BlockRef(17), [Operand { value: ValueRef(2147483686), annotation: None }], BlockRef(39), [Operand { value: ValueRef(2147483686), annotation: None }])
// CHECK:   block 39 (inst_start=66, inst_count=3):
// CHECK:     vref=66 (index=66) op=Const(4)
// CHECK:     vref=67 (index=67) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(59), annotation: None }), IntOperand(Operand { value: ValueRef(66), annotation: None }))
// CHECK:     vref=68 (index=68) op=BrIf(BoolOperand(Operand { value: ValueRef(67), annotation: None }), BlockRef(16), [Operand { value: ValueRef(2147483687), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483687), annotation: None }])
// CHECK:   block 40 (inst_start=73, inst_count=3):
// CHECK:     vref=73 (index=73) op=Const(2)
// CHECK:     vref=74 (index=74) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(69), annotation: None }), IntOperand(Operand { value: ValueRef(73), annotation: None }))
// CHECK:     vref=75 (index=75) op=BrIf(BoolOperand(Operand { value: ValueRef(74), annotation: None }), BlockRef(14), [Operand { value: ValueRef(2147483688), annotation: None }], BlockRef(41), [Operand { value: ValueRef(2147483688), annotation: None }])
// CHECK:   block 41 (inst_start=76, inst_count=3):
// CHECK:     vref=76 (index=76) op=Const(4)
// CHECK:     vref=77 (index=77) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(69), annotation: None }), IntOperand(Operand { value: ValueRef(76), annotation: None }))
// CHECK:     vref=78 (index=78) op=BrIf(BoolOperand(Operand { value: ValueRef(77), annotation: None }), BlockRef(13), [Operand { value: ValueRef(2147483689), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483689), annotation: None }])
// CHECK:   block 42 (inst_start=83, inst_count=3):
// CHECK:     vref=83 (index=83) op=Const(2)
// CHECK:     vref=84 (index=84) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(79), annotation: None }), IntOperand(Operand { value: ValueRef(83), annotation: None }))
// CHECK:     vref=85 (index=85) op=BrIf(BoolOperand(Operand { value: ValueRef(84), annotation: None }), BlockRef(11), [Operand { value: ValueRef(2147483690), annotation: None }], BlockRef(43), [Operand { value: ValueRef(2147483690), annotation: None }])
// CHECK:   block 43 (inst_start=86, inst_count=3):
// CHECK:     vref=86 (index=86) op=Const(4)
// CHECK:     vref=87 (index=87) op=ICmp(Eq, IntOperand(Operand { value: ValueRef(79), annotation: None }), IntOperand(Operand { value: ValueRef(86), annotation: None }))
// CHECK:     vref=88 (index=88) op=BrIf(BoolOperand(Operand { value: ValueRef(87), annotation: None }), BlockRef(10), [Operand { value: ValueRef(2147483691), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483691), annotation: None }])
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] StackSlot(8)
// CHECK:     [2] Param(1)
// CHECK:     [3] Param(2)
// CHECK:     [4] Param(3)
// CHECK:     [5] Param(4)
// CHECK:     [6] StackSlot(1)
// CHECK:     [7] Param(5)
// CHECK:     [8] StackSlot(1)
// CHECK:     [9] Store(Operand { value: ValueRef(5), annotation: None }, PtrOperand(Operand { value: ValueRef(6), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     [10] Store(Operand { value: ValueRef(7), annotation: None }, PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(9), annotation: None }))
// CHECK:     [11] StackSlot(8)
// CHECK:     [12] StackSlot(16)
// CHECK:     [13] StackSlot(16)
// CHECK:     [14] StackSlot(16)
// CHECK:     [15] StackSlot(16)
// CHECK:     [16] Load(PtrOperand(Operand { value: ValueRef(6), annotation: None }), 1, MemOperand(Operand { value: ValueRef(10), annotation: None }))
// CHECK:     [17] Const(0)
// CHECK:     [18] ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(17), annotation: None }))
// CHECK:     [19] BrIf(BoolOperand(Operand { value: ValueRef(18), annotation: None }), BlockRef(2), [Operand { value: ValueRef(10), annotation: None }], BlockRef(29), [Operand { value: ValueRef(10), annotation: None }])
// CHECK:     [20] Const(1)
// CHECK:     [21] ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(20), annotation: None }))
// CHECK:     [22] BrIf(BoolOperand(Operand { value: ValueRef(21), annotation: None }), BlockRef(4), [Operand { value: ValueRef(2147483677), annotation: None }], BlockRef(30), [Operand { value: ValueRef(2147483677), annotation: None }])
// CHECK:     [23] Const(2)
// CHECK:     [24] ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(23), annotation: None }))
// CHECK:     [25] BrIf(BoolOperand(Operand { value: ValueRef(24), annotation: None }), BlockRef(3), [Operand { value: ValueRef(2147483678), annotation: None }], BlockRef(31), [Operand { value: ValueRef(2147483678), annotation: None }])
// CHECK:     [26] Const(3)
// CHECK:     [27] ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(26), annotation: None }))
// CHECK:     [28] BrIf(BoolOperand(Operand { value: ValueRef(27), annotation: None }), BlockRef(5), [Operand { value: ValueRef(2147483679), annotation: None }], BlockRef(32), [Operand { value: ValueRef(2147483679), annotation: None }])
// CHECK:     [29] Const(4)
// CHECK:     [30] ICmp(Eq, IntOperand(Operand { value: ValueRef(16), annotation: None }), IntOperand(Operand { value: ValueRef(29), annotation: None }))
// CHECK:     [31] BrIf(BoolOperand(Operand { value: ValueRef(30), annotation: None }), BlockRef(6), [Operand { value: ValueRef(2147483680), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483680), annotation: None }])
// CHECK:     [32] Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK:     [33] Const(1)
// CHECK:     [34] ICmp(Eq, IntOperand(Operand { value: ValueRef(32), annotation: None }), IntOperand(Operand { value: ValueRef(33), annotation: None }))
// CHECK:     [35] BrIf(BoolOperand(Operand { value: ValueRef(34), annotation: None }), BlockRef(8), [Operand { value: ValueRef(2147483649), annotation: None }], BlockRef(33), [Operand { value: ValueRef(2147483649), annotation: None }])
// CHECK:     [36] Const(3)
// CHECK:     [37] ICmp(Eq, IntOperand(Operand { value: ValueRef(32), annotation: None }), IntOperand(Operand { value: ValueRef(36), annotation: None }))
// CHECK:     [38] BrIf(BoolOperand(Operand { value: ValueRef(37), annotation: None }), BlockRef(9), [Operand { value: ValueRef(2147483681), annotation: None }], BlockRef(7), [Operand { value: ValueRef(2147483681), annotation: None }])
// CHECK:     [39] Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483650), annotation: None }))
// CHECK:     [40] Const(0)
// CHECK:     [41] ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(40), annotation: None }))
// CHECK:     [42] BrIf(BoolOperand(Operand { value: ValueRef(41), annotation: None }), BlockRef(24), [Operand { value: ValueRef(2147483650), annotation: None }], BlockRef(34), [Operand { value: ValueRef(2147483650), annotation: None }])
// CHECK:     [43] Const(2)
// CHECK:     [44] ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(43), annotation: None }))
// CHECK:     [45] BrIf(BoolOperand(Operand { value: ValueRef(44), annotation: None }), BlockRef(23), [Operand { value: ValueRef(2147483682), annotation: None }], BlockRef(35), [Operand { value: ValueRef(2147483682), annotation: None }])
// CHECK:     [46] Const(4)
// CHECK:     [47] ICmp(Eq, IntOperand(Operand { value: ValueRef(39), annotation: None }), IntOperand(Operand { value: ValueRef(46), annotation: None }))
// CHECK:     [48] BrIf(BoolOperand(Operand { value: ValueRef(47), annotation: None }), BlockRef(22), [Operand { value: ValueRef(2147483683), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483683), annotation: None }])
// CHECK:     [49] Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483651), annotation: None }))
// CHECK:     [50] Const(0)
// CHECK:     [51] ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(50), annotation: None }))
// CHECK:     [52] BrIf(BoolOperand(Operand { value: ValueRef(51), annotation: None }), BlockRef(21), [Operand { value: ValueRef(2147483651), annotation: None }], BlockRef(36), [Operand { value: ValueRef(2147483651), annotation: None }])
// CHECK:     [53] Const(2)
// CHECK:     [54] ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(53), annotation: None }))
// CHECK:     [55] BrIf(BoolOperand(Operand { value: ValueRef(54), annotation: None }), BlockRef(20), [Operand { value: ValueRef(2147483684), annotation: None }], BlockRef(37), [Operand { value: ValueRef(2147483684), annotation: None }])
// CHECK:     [56] Const(4)
// CHECK:     [57] ICmp(Eq, IntOperand(Operand { value: ValueRef(49), annotation: None }), IntOperand(Operand { value: ValueRef(56), annotation: None }))
// CHECK:     [58] BrIf(BoolOperand(Operand { value: ValueRef(57), annotation: None }), BlockRef(19), [Operand { value: ValueRef(2147483685), annotation: None }], BlockRef(1), [Operand { value: ValueRef(2147483685), annotation: None }])
// CHECK:     [59] Load(PtrOperand(Operand { value: ValueRef(8), annotation: None }), 1, MemOperand(Operand { value: ValueRef(2147483652), annotation: None }))
// CHECK: warning: isel failed on vref=ValueRef(144) op AtomicCmpXchg(PtrOperand(Operand { value: ValueRef(2), annotation: None }), Operand { value: ValueRef(3), annotation: None }, Operand { value: ValueRef(4), annotation: None }, SeqCst, SeqCst, MemOperand(Operand { value: ValueRef(2147483658), annotation: None }))
// CHECK: warning: isel failed for _RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic23atomic_compare_exchangemECsh6zX7Z7540N_10atomic_ops, emitting stub
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
// CHECK: func @atomic_compare_exchange(ptr, ptr, int:u32, int:u32) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: ptr = param 1
// CHECK:     v4: int:u32 = param 2
// CHECK:     v5: int:u32 = param 3
// CHECK:     v6: ptr = stack_slot 8
// CHECK:     v7: mem = store.8 v3, v6, v0
// CHECK:     v8: ptr = load.8 v6, v7
// CHECK:     v9: int:i64 = iconst 4
// CHECK:     v10: int:i64 = iconst 4
// CHECK:     v11: ptr = symbol_addr @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic23atomic_compare_exchangemECsh6zX7Z7540N_10atomic_ops
// CHECK:     v12: mem, v13: int:i64 = call v11(v1, v8, v4, v5, v9, v10), v7 -> int:i64
// CHECK:     br bb1(v12)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     ret v1, v15
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
// CHECK: === ISel failure dump for atomic_fetch_add ===
// CHECK:   block 0 (inst_start=0, inst_count=7):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=StackSlot(8)
// CHECK:     vref=3 (index=3) op=Store(Operand { value: ValueRef(0), annotation: None }, PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     vref=4 (index=4) op=Load(PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=5 (index=5) op=AtomicRmw(Add, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=6 (index=6) op=Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:   block 1 (inst_start=7, inst_count=1):
// CHECK:     vref=7 (index=7) op=Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] Param(1)
// CHECK:     [2] StackSlot(8)
// CHECK:     [3] Store(Operand { value: ValueRef(0), annotation: None }, PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     [4] Load(PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     [5] AtomicRmw(Add, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     [6] Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:     [7] Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK: warning: isel failed on vref=ValueRef(5) op AtomicRmw(Add, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
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
// CHECK: func @atomic_load_relaxed(ptr) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 8
// CHECK:     v3: mem = store.8 v1, v2, v0
// CHECK:     v4: ptr = load.8 v2, v3
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: ptr = symbol_addr @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic11atomic_loadmECsh6zX7Z7540N_10atomic_ops
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
// CHECK:     v7: ptr = symbol_addr @_RINvNtNtCsa3SJzwB9S2T_4core4sync6atomic12atomic_storemECsh6zX7Z7540N_10atomic_ops
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
// CHECK: === ISel failure dump for atomic_swap ===
// CHECK:   block 0 (inst_start=0, inst_count=7):
// CHECK:     vref=0 (index=0) op=Param(0)
// CHECK:     vref=1 (index=1) op=Param(1)
// CHECK:     vref=2 (index=2) op=StackSlot(8)
// CHECK:     vref=3 (index=3) op=Store(Operand { value: ValueRef(0), annotation: None }, PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     vref=4 (index=4) op=Load(PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=5 (index=5) op=AtomicRmw(Xchg, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     vref=6 (index=6) op=Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:   block 1 (inst_start=7, inst_count=1):
// CHECK:     vref=7 (index=7) op=Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK:   Raw instruction array (first 60):
// CHECK:     [0] Param(0)
// CHECK:     [1] Param(1)
// CHECK:     [2] StackSlot(8)
// CHECK:     [3] Store(Operand { value: ValueRef(0), annotation: None }, PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(2147483648), annotation: None }))
// CHECK:     [4] Load(PtrOperand(Operand { value: ValueRef(2), annotation: None }), 8, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     [5] AtomicRmw(Xchg, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
// CHECK:     [6] Br(BlockRef(1), [Operand { value: ValueRef(5), annotation: None }])
// CHECK:     [7] Ret(Some(Operand { value: ValueRef(1073741829), annotation: None }), MemOperand(Operand { value: ValueRef(2147483649), annotation: None }))
// CHECK: warning: isel failed on vref=ValueRef(5) op AtomicRmw(Xchg, PtrOperand(Operand { value: ValueRef(4), annotation: None }), Operand { value: ValueRef(1), annotation: None }, SeqCst, MemOperand(Operand { value: ValueRef(3), annotation: None }))
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
