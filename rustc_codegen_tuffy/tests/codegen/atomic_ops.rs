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
// CHECK:     v1 = param %self
// CHECK:     v2 = param %order
// CHECK:     v3 = stack_slot 4
// CHECK:     v4 = stack_slot 16
// CHECK:     v5 = stack_slot 16
// CHECK:     v6 = stack_slot 16
// CHECK:     v7 = stack_slot 16
// CHECK:     v8 = stack_slot 1
// CHECK:     v9 = store.1 v2, v8, v0
// CHECK:     v10 = load.1 v8, v9
// CHECK:     v11 = iconst 0
// CHECK:     v12 = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17 = symbol_addr @.Lstr.0
// CHECK:     v18 = iconst 49
// CHECK:     v19 = iconst 49
// CHECK:     v20 = store.8 v17, v6, v16
// CHECK:     v21 = iconst 8
// CHECK:     v22 = ptradd v6, v21
// CHECK:     v23 = store.8 v19, v22, v20
// CHECK:     v24 = iconst 49
// CHECK:     v25 = iconst 8
// CHECK:     v26 = ptradd v6, v25
// CHECK:     v27 = store.8 v24, v26, v23
// CHECK:     v28 = load.8 v6, v27
// CHECK:     v29 = ptrtoaddr v28
// CHECK:     v30 = symbol_addr @.Lstr.1
// CHECK:     v31 = iconst 49
// CHECK:     v32 = store.8 v29, v5, v27
// CHECK:     v33 = iconst 0
// CHECK:     v34 = iconst 8
// CHECK:     v35 = ptradd v5, v34
// CHECK:     v36 = store.8 v33, v35, v32
// CHECK:     v37 = load.8 v5, v36
// CHECK:     v38 = iconst 8
// CHECK:     v39 = ptradd v5, v38
// CHECK:     v40 = load.8 v39, v36
// CHECK:     v41 = symbol_addr @.Lloc.3
// CHECK:     v42 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v43, v44 = call v42(v37, v40, v41), v36 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v46: mem):
// CHECK:     v47 = symbol_addr @.Lstr.4
// CHECK:     v48 = iconst 40
// CHECK:     v49 = iconst 40
// CHECK:     v50 = store.8 v47, v7, v46
// CHECK:     v51 = iconst 8
// CHECK:     v52 = ptradd v7, v51
// CHECK:     v53 = store.8 v49, v52, v50
// CHECK:     v54 = iconst 40
// CHECK:     v55 = iconst 8
// CHECK:     v56 = ptradd v7, v55
// CHECK:     v57 = store.8 v54, v56, v53
// CHECK:     v58 = load.8 v7, v57
// CHECK:     v59 = ptrtoaddr v58
// CHECK:     v60 = symbol_addr @.Lstr.5
// CHECK:     v61 = iconst 40
// CHECK:     v62 = store.8 v59, v4, v57
// CHECK:     v63 = iconst 0
// CHECK:     v64 = iconst 8
// CHECK:     v65 = ptradd v4, v64
// CHECK:     v66 = store.8 v63, v65, v62
// CHECK:     v67 = load.8 v4, v66
// CHECK:     v68 = iconst 8
// CHECK:     v69 = ptradd v4, v68
// CHECK:     v70 = load.8 v69, v66
// CHECK:     v71 = symbol_addr @.Lloc.7
// CHECK:     v72 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v73, v74 = call v72(v67, v70, v71), v66 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v76: mem):
// CHECK:     v77 = load.4 v1, v76
// CHECK:     br bb7(v76)
// CHECK:
// CHECK:   bb5(v79: mem):
// CHECK:     v80 = load.4 v1, v79
// CHECK:     br bb7(v79)
// CHECK:
// CHECK:   bb6(v82: mem):
// CHECK:     v83 = load.4 v1, v82
// CHECK:     br bb7(v82)
// CHECK:
// CHECK:   bb7(v85: mem):
// CHECK:     ret v83, v85
// CHECK:
// CHECK:   bb8(v87: mem):
// CHECK:     v88 = iconst 1
// CHECK:     v89 = icmp.eq v10, v88
// CHECK:     brif v89, bb3(v87), bb9(v87)
// CHECK:
// CHECK:   bb9(v91: mem):
// CHECK:     v92 = iconst 2
// CHECK:     v93 = icmp.eq v10, v92
// CHECK:     brif v93, bb5(v91), bb10(v91)
// CHECK:
// CHECK:   bb10(v95: mem):
// CHECK:     v96 = iconst 3
// CHECK:     v97 = icmp.eq v10, v96
// CHECK:     brif v97, bb2(v95), bb11(v95)
// CHECK:
// CHECK:   bb11(v99: mem):
// CHECK:     v100 = iconst 4
// CHECK:     v101 = icmp.eq v10, v100
// CHECK:     brif v101, bb4(v99), bb1(v99)
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
// CHECK:     v1 = param %self
// CHECK:     v2:u32 = param %val
// CHECK:     v3 = param %order
// CHECK:     v4 = stack_slot 16
// CHECK:     v5 = stack_slot 16
// CHECK:     v6 = stack_slot 16
// CHECK:     v7 = stack_slot 16
// CHECK:     v8 = stack_slot 1
// CHECK:     v9 = store.1 v3, v8, v0
// CHECK:     v10 = load.1 v8, v9
// CHECK:     v11 = iconst 0
// CHECK:     v12 = icmp.eq v10, v11
// CHECK:     brif v12, bb6(v9), bb8(v9)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17 = symbol_addr @.Lstr.8
// CHECK:     v18 = iconst 50
// CHECK:     v19 = iconst 50
// CHECK:     v20 = store.8 v17, v6, v16
// CHECK:     v21 = iconst 8
// CHECK:     v22 = ptradd v6, v21
// CHECK:     v23 = store.8 v19, v22, v20
// CHECK:     v24 = iconst 50
// CHECK:     v25 = iconst 8
// CHECK:     v26 = ptradd v6, v25
// CHECK:     v27 = store.8 v24, v26, v23
// CHECK:     v28 = load.8 v6, v27
// CHECK:     v29 = ptrtoaddr v28
// CHECK:     v30 = symbol_addr @.Lstr.9
// CHECK:     v31 = iconst 50
// CHECK:     v32 = store.8 v29, v5, v27
// CHECK:     v33 = iconst 0
// CHECK:     v34 = iconst 8
// CHECK:     v35 = ptradd v5, v34
// CHECK:     v36 = store.8 v33, v35, v32
// CHECK:     v37 = load.8 v5, v36
// CHECK:     v38 = iconst 8
// CHECK:     v39 = ptradd v5, v38
// CHECK:     v40 = load.8 v39, v36
// CHECK:     v41 = symbol_addr @.Lloc.11
// CHECK:     v42 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v43, v44 = call v42(v37, v40, v41), v36 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v46: mem):
// CHECK:     v47 = symbol_addr @.Lstr.12
// CHECK:     v48 = iconst 42
// CHECK:     v49 = iconst 42
// CHECK:     v50 = store.8 v47, v7, v46
// CHECK:     v51 = iconst 8
// CHECK:     v52 = ptradd v7, v51
// CHECK:     v53 = store.8 v49, v52, v50
// CHECK:     v54 = iconst 42
// CHECK:     v55 = iconst 8
// CHECK:     v56 = ptradd v7, v55
// CHECK:     v57 = store.8 v54, v56, v53
// CHECK:     v58 = load.8 v7, v57
// CHECK:     v59 = ptrtoaddr v58
// CHECK:     v60 = symbol_addr @.Lstr.13
// CHECK:     v61 = iconst 42
// CHECK:     v62 = store.8 v59, v4, v57
// CHECK:     v63 = iconst 0
// CHECK:     v64 = iconst 8
// CHECK:     v65 = ptradd v4, v64
// CHECK:     v66 = store.8 v63, v65, v62
// CHECK:     v67 = load.8 v4, v66
// CHECK:     v68 = iconst 8
// CHECK:     v69 = ptradd v4, v68
// CHECK:     v70 = load.8 v69, v66
// CHECK:     v71 = symbol_addr @.Lloc.15
// CHECK:     v72 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v73, v74 = call v72(v67, v70, v71), v66 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb4(v76: mem):
// CHECK:     v77 = store.4 v2, v1, v76
// CHECK:     br bb7(v77)
// CHECK:
// CHECK:   bb5(v79: mem):
// CHECK:     v80 = store.4 v2, v1, v79
// CHECK:     br bb7(v80)
// CHECK:
// CHECK:   bb6(v82: mem):
// CHECK:     v83 = store.4 v2, v1, v82
// CHECK:     br bb7(v83)
// CHECK:
// CHECK:   bb7(v85: mem):
// CHECK:     ret v85
// CHECK:
// CHECK:   bb8(v87: mem):
// CHECK:     v88 = iconst 1
// CHECK:     v89 = icmp.eq v10, v88
// CHECK:     brif v89, bb5(v87), bb9(v87)
// CHECK:
// CHECK:   bb9(v91: mem):
// CHECK:     v92 = iconst 2
// CHECK:     v93 = icmp.eq v10, v92
// CHECK:     brif v93, bb3(v91), bb10(v91)
// CHECK:
// CHECK:   bb10(v95: mem):
// CHECK:     v96 = iconst 3
// CHECK:     v97 = icmp.eq v10, v96
// CHECK:     brif v97, bb2(v95), bb11(v95)
// CHECK:
// CHECK:   bb11(v99: mem):
// CHECK:     v100 = iconst 4
// CHECK:     v101 = icmp.eq v10, v100
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
// CHECK:     v1 = param %self
// CHECK:     v2:u32 = param %old
// CHECK:     v3:u32 = param %new
// CHECK:     v4 = param %success
// CHECK:     v5 = param %failure
// CHECK:     v6 = stack_slot 8
// CHECK:     v7 = stack_slot 8
// CHECK:     v8 = stack_slot 16
// CHECK:     v9 = stack_slot 16
// CHECK:     v10 = stack_slot 16
// CHECK:     v11 = stack_slot 16
// CHECK:     v12 = stack_slot 1
// CHECK:     v13 = store.1 v4, v12, v0
// CHECK:     v14 = load.1 v12, v13
// CHECK:     v15 = iconst 0
// CHECK:     v16 = icmp.eq v14, v15
// CHECK:     brif v16, bb2(v13), bb29(v13)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19 = stack_slot 1
// CHECK:     v20 = store.1 v5, v19, v18
// CHECK:     v21 = load.1 v19, v20
// CHECK:     v22 = iconst 1
// CHECK:     v23 = icmp.eq v21, v22
// CHECK:     brif v23, bb8(v20), bb33(v20)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     v26 = stack_slot 1
// CHECK:     v27 = store.1 v5, v26, v25
// CHECK:     v28 = load.1 v26, v27
// CHECK:     v29 = iconst 0
// CHECK:     v30 = icmp.eq v28, v29
// CHECK:     brif v30, bb24(v27), bb34(v27)
// CHECK:
// CHECK:   bb3(v32: mem):
// CHECK:     v33 = stack_slot 1
// CHECK:     v34 = store.1 v5, v33, v32
// CHECK:     v35 = load.1 v33, v34
// CHECK:     v36 = iconst 0
// CHECK:     v37 = icmp.eq v35, v36
// CHECK:     brif v37, bb21(v34), bb36(v34)
// CHECK:
// CHECK:   bb4(v39: mem):
// CHECK:     v40 = stack_slot 1
// CHECK:     v41 = store.1 v5, v40, v39
// CHECK:     v42 = load.1 v40, v41
// CHECK:     v43 = iconst 0
// CHECK:     v44 = icmp.eq v42, v43
// CHECK:     brif v44, bb18(v41), bb38(v41)
// CHECK:
// CHECK:   bb5(v46: mem):
// CHECK:     v47 = stack_slot 1
// CHECK:     v48 = store.1 v5, v47, v46
// CHECK:     v49 = load.1 v47, v48
// CHECK:     v50 = iconst 0
// CHECK:     v51 = icmp.eq v49, v50
// CHECK:     brif v51, bb15(v48), bb40(v48)
// CHECK:
// CHECK:   bb6(v53: mem):
// CHECK:     v54 = stack_slot 1
// CHECK:     v55 = store.1 v5, v54, v53
// CHECK:     v56 = load.1 v54, v55
// CHECK:     v57 = iconst 0
// CHECK:     v58 = icmp.eq v56, v57
// CHECK:     brif v58, bb12(v55), bb42(v55)
// CHECK:
// CHECK:   bb7(v60: mem):
// CHECK:     unreachable
// CHECK:
// CHECK:   bb8(v62: mem):
// CHECK:     v63 = symbol_addr @.Lstr.16
// CHECK:     v64 = iconst 52
// CHECK:     v65 = iconst 52
// CHECK:     v66 = store.8 v63, v10, v62
// CHECK:     v67 = iconst 8
// CHECK:     v68 = ptradd v10, v67
// CHECK:     v69 = store.8 v65, v68, v66
// CHECK:     v70 = iconst 52
// CHECK:     v71 = iconst 8
// CHECK:     v72 = ptradd v10, v71
// CHECK:     v73 = store.8 v70, v72, v69
// CHECK:     v74 = load.8 v10, v73
// CHECK:     v75 = ptrtoaddr v74
// CHECK:     v76 = symbol_addr @.Lstr.17
// CHECK:     v77 = iconst 52
// CHECK:     v78 = store.8 v75, v9, v73
// CHECK:     v79 = iconst 0
// CHECK:     v80 = iconst 8
// CHECK:     v81 = ptradd v9, v80
// CHECK:     v82 = store.8 v79, v81, v78
// CHECK:     v83 = load.8 v9, v82
// CHECK:     v84 = iconst 8
// CHECK:     v85 = ptradd v9, v84
// CHECK:     v86 = load.8 v85, v82
// CHECK:     v87 = symbol_addr @.Lloc.19
// CHECK:     v88 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v89, v90 = call v88(v83, v86, v87), v82 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb9(v92: mem):
// CHECK:     v93 = symbol_addr @.Lstr.20
// CHECK:     v94 = iconst 61
// CHECK:     v95 = iconst 61
// CHECK:     v96 = store.8 v93, v11, v92
// CHECK:     v97 = iconst 8
// CHECK:     v98 = ptradd v11, v97
// CHECK:     v99 = store.8 v95, v98, v96
// CHECK:     v100 = iconst 61
// CHECK:     v101 = iconst 8
// CHECK:     v102 = ptradd v11, v101
// CHECK:     v103 = store.8 v100, v102, v99
// CHECK:     v104 = load.8 v11, v103
// CHECK:     v105 = ptrtoaddr v104
// CHECK:     v106 = symbol_addr @.Lstr.21
// CHECK:     v107 = iconst 61
// CHECK:     v108 = store.8 v105, v8, v103
// CHECK:     v109 = iconst 0
// CHECK:     v110 = iconst 8
// CHECK:     v111 = ptradd v8, v110
// CHECK:     v112 = store.8 v109, v111, v108
// CHECK:     v113 = load.8 v8, v112
// CHECK:     v114 = iconst 8
// CHECK:     v115 = ptradd v8, v114
// CHECK:     v116 = load.8 v115, v112
// CHECK:     v117 = symbol_addr @.Lloc.23
// CHECK:     v118 = symbol_addr @_RNvNtCsiYoX4ApF2vj_4core9panicking9panic_fmt
// CHECK:     v119, v120 = call v118(v113, v116, v117), v112 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v122: mem):
// CHECK:     v123 = load.4 v1, v122
// CHECK:     v124 = icmp.eq v123, v2
// CHECK:     v125 = select v124, v3, v123
// CHECK:     v126 = store.4 v125, v1, v122
// CHECK:     v127 = store.4 v123, v6, v126
// CHECK:     v128 = iconst 4
// CHECK:     v129 = ptradd v6, v128
// CHECK:     v130 = store.1 v124, v129, v127
// CHECK:     br bb25(v130)
// CHECK:
// CHECK:   bb11(v132: mem):
// CHECK:     v133 = load.4 v1, v132
// CHECK:     v134 = icmp.eq v133, v2
// CHECK:     v135 = select v134, v3, v133
// CHECK:     v136 = store.4 v135, v1, v132
// CHECK:     v137 = store.4 v133, v6, v136
// CHECK:     v138 = iconst 4
// CHECK:     v139 = ptradd v6, v138
// CHECK:     v140 = store.1 v134, v139, v137
// CHECK:     br bb25(v140)
// CHECK:
// CHECK:   bb12(v142: mem):
// CHECK:     v143 = load.4 v1, v142
// CHECK:     v144 = icmp.eq v143, v2
// CHECK:     v145 = select v144, v3, v143
// CHECK:     v146 = store.4 v145, v1, v142
// CHECK:     v147 = store.4 v143, v6, v146
// CHECK:     v148 = iconst 4
// CHECK:     v149 = ptradd v6, v148
// CHECK:     v150 = store.1 v144, v149, v147
// CHECK:     br bb25(v150)
// CHECK:
// CHECK:   bb13(v152: mem):
// CHECK:     v153 = load.4 v1, v152
// CHECK:     v154 = icmp.eq v153, v2
// CHECK:     v155 = select v154, v3, v153
// CHECK:     v156 = store.4 v155, v1, v152
// CHECK:     v157 = store.4 v153, v6, v156
// CHECK:     v158 = iconst 4
// CHECK:     v159 = ptradd v6, v158
// CHECK:     v160 = store.1 v154, v159, v157
// CHECK:     br bb25(v160)
// CHECK:
// CHECK:   bb14(v162: mem):
// CHECK:     v163 = load.4 v1, v162
// CHECK:     v164 = icmp.eq v163, v2
// CHECK:     v165 = select v164, v3, v163
// CHECK:     v166 = store.4 v165, v1, v162
// CHECK:     v167 = store.4 v163, v6, v166
// CHECK:     v168 = iconst 4
// CHECK:     v169 = ptradd v6, v168
// CHECK:     v170 = store.1 v164, v169, v167
// CHECK:     br bb25(v170)
// CHECK:
// CHECK:   bb15(v172: mem):
// CHECK:     v173 = load.4 v1, v172
// CHECK:     v174 = icmp.eq v173, v2
// CHECK:     v175 = select v174, v3, v173
// CHECK:     v176 = store.4 v175, v1, v172
// CHECK:     v177 = store.4 v173, v6, v176
// CHECK:     v178 = iconst 4
// CHECK:     v179 = ptradd v6, v178
// CHECK:     v180 = store.1 v174, v179, v177
// CHECK:     br bb25(v180)
// CHECK:
// CHECK:   bb16(v182: mem):
// CHECK:     v183 = load.4 v1, v182
// CHECK:     v184 = icmp.eq v183, v2
// CHECK:     v185 = select v184, v3, v183
// CHECK:     v186 = store.4 v185, v1, v182
// CHECK:     v187 = store.4 v183, v6, v186
// CHECK:     v188 = iconst 4
// CHECK:     v189 = ptradd v6, v188
// CHECK:     v190 = store.1 v184, v189, v187
// CHECK:     br bb25(v190)
// CHECK:
// CHECK:   bb17(v192: mem):
// CHECK:     v193 = load.4 v1, v192
// CHECK:     v194 = icmp.eq v193, v2
// CHECK:     v195 = select v194, v3, v193
// CHECK:     v196 = store.4 v195, v1, v192
// CHECK:     v197 = store.4 v193, v6, v196
// CHECK:     v198 = iconst 4
// CHECK:     v199 = ptradd v6, v198
// CHECK:     v200 = store.1 v194, v199, v197
// CHECK:     br bb25(v200)
// CHECK:
// CHECK:   bb18(v202: mem):
// CHECK:     v203 = load.4 v1, v202
// CHECK:     v204 = icmp.eq v203, v2
// CHECK:     v205 = select v204, v3, v203
// CHECK:     v206 = store.4 v205, v1, v202
// CHECK:     v207 = store.4 v203, v6, v206
// CHECK:     v208 = iconst 4
// CHECK:     v209 = ptradd v6, v208
// CHECK:     v210 = store.1 v204, v209, v207
// CHECK:     br bb25(v210)
// CHECK:
// CHECK:   bb19(v212: mem):
// CHECK:     v213 = load.4 v1, v212
// CHECK:     v214 = icmp.eq v213, v2
// CHECK:     v215 = select v214, v3, v213
// CHECK:     v216 = store.4 v215, v1, v212
// CHECK:     v217 = store.4 v213, v6, v216
// CHECK:     v218 = iconst 4
// CHECK:     v219 = ptradd v6, v218
// CHECK:     v220 = store.1 v214, v219, v217
// CHECK:     br bb25(v220)
// CHECK:
// CHECK:   bb20(v222: mem):
// CHECK:     v223 = load.4 v1, v222
// CHECK:     v224 = icmp.eq v223, v2
// CHECK:     v225 = select v224, v3, v223
// CHECK:     v226 = store.4 v225, v1, v222
// CHECK:     v227 = store.4 v223, v6, v226
// CHECK:     v228 = iconst 4
// CHECK:     v229 = ptradd v6, v228
// CHECK:     v230 = store.1 v224, v229, v227
// CHECK:     br bb25(v230)
// CHECK:
// CHECK:   bb21(v232: mem):
// CHECK:     v233 = load.4 v1, v232
// CHECK:     v234 = icmp.eq v233, v2
// CHECK:     v235 = select v234, v3, v233
// CHECK:     v236 = store.4 v235, v1, v232
// CHECK:     v237 = store.4 v233, v6, v236
// CHECK:     v238 = iconst 4
// CHECK:     v239 = ptradd v6, v238
// CHECK:     v240 = store.1 v234, v239, v237
// CHECK:     br bb25(v240)
// CHECK:
// CHECK:   bb22(v242: mem):
// CHECK:     v243 = load.4 v1, v242
// CHECK:     v244 = icmp.eq v243, v2
// CHECK:     v245 = select v244, v3, v243
// CHECK:     v246 = store.4 v245, v1, v242
// CHECK:     v247 = store.4 v243, v6, v246
// CHECK:     v248 = iconst 4
// CHECK:     v249 = ptradd v6, v248
// CHECK:     v250 = store.1 v244, v249, v247
// CHECK:     br bb25(v250)
// CHECK:
// CHECK:   bb23(v252: mem):
// CHECK:     v253 = load.4 v1, v252
// CHECK:     v254 = icmp.eq v253, v2
// CHECK:     v255 = select v254, v3, v253
// CHECK:     v256 = store.4 v255, v1, v252
// CHECK:     v257 = store.4 v253, v6, v256
// CHECK:     v258 = iconst 4
// CHECK:     v259 = ptradd v6, v258
// CHECK:     v260 = store.1 v254, v259, v257
// CHECK:     br bb25(v260)
// CHECK:
// CHECK:   bb24(v262: mem):
// CHECK:     v263 = load.4 v1, v262
// CHECK:     v264 = icmp.eq v263, v2
// CHECK:     v265 = select v264, v3, v263
// CHECK:     v266 = store.4 v265, v1, v262
// CHECK:     v267 = store.4 v263, v6, v266
// CHECK:     v268 = iconst 4
// CHECK:     v269 = ptradd v6, v268
// CHECK:     v270 = store.1 v264, v269, v267
// CHECK:     br bb25(v270)
// CHECK:
// CHECK:   bb25(v272: mem):
// CHECK:     v273 = load.4 v6, v272
// CHECK:     v274 = iconst 4
// CHECK:     v275 = ptradd v6, v274
// CHECK:     v276 = load.1 v275, v272
// CHECK:     v277 = bool_to_int v276
// CHECK:     v278 = iconst 255
// CHECK:     v279 = and v277, v278
// CHECK:     v280 = iconst 0
// CHECK:     v281 = icmp.eq v279, v280
// CHECK:     brif v281, bb27(v272), bb26(v272)
// CHECK:
// CHECK:   bb26(v283: mem):
// CHECK:     v284 = iconst 0
// CHECK:     v285 = store.8 v284, v7, v283
// CHECK:     v286 = iconst 4
// CHECK:     v287 = ptradd v7, v286
// CHECK:     v288 = store.4 v273, v287, v285
// CHECK:     v289 = iconst 0
// CHECK:     v290 = store.4 v289, v7, v288
// CHECK:     br bb28(v290)
// CHECK:
// CHECK:   bb27(v292: mem):
// CHECK:     v293 = iconst 0
// CHECK:     v294 = store.8 v293, v7, v292
// CHECK:     v295 = iconst 4
// CHECK:     v296 = ptradd v7, v295
// CHECK:     v297 = store.4 v273, v296, v294
// CHECK:     v298 = iconst 1
// CHECK:     v299 = store.4 v298, v7, v297
// CHECK:     br bb28(v299)
// CHECK:
// CHECK:   bb28(v301: mem):
// CHECK:     v302 = load.8 v7, v301
// CHECK:     ret v302, v301
// CHECK:
// CHECK:   bb29(v304: mem):
// CHECK:     v305 = iconst 1
// CHECK:     v306 = icmp.eq v14, v305
// CHECK:     brif v306, bb4(v304), bb30(v304)
// CHECK:
// CHECK:   bb30(v308: mem):
// CHECK:     v309 = iconst 2
// CHECK:     v310 = icmp.eq v14, v309
// CHECK:     brif v310, bb3(v308), bb31(v308)
// CHECK:
// CHECK:   bb31(v312: mem):
// CHECK:     v313 = iconst 3
// CHECK:     v314 = icmp.eq v14, v313
// CHECK:     brif v314, bb5(v312), bb32(v312)
// CHECK:
// CHECK:   bb32(v316: mem):
// CHECK:     v317 = iconst 4
// CHECK:     v318 = icmp.eq v14, v317
// CHECK:     brif v318, bb6(v316), bb7(v316)
// CHECK:
// CHECK:   bb33(v320: mem):
// CHECK:     v321 = iconst 3
// CHECK:     v322 = icmp.eq v21, v321
// CHECK:     brif v322, bb9(v320), bb7(v320)
// CHECK:
// CHECK:   bb34(v324: mem):
// CHECK:     v325 = iconst 2
// CHECK:     v326 = icmp.eq v28, v325
// CHECK:     brif v326, bb23(v324), bb35(v324)
// CHECK:
// CHECK:   bb35(v328: mem):
// CHECK:     v329 = iconst 4
// CHECK:     v330 = icmp.eq v28, v329
// CHECK:     brif v330, bb22(v328), bb1(v328)
// CHECK:
// CHECK:   bb36(v332: mem):
// CHECK:     v333 = iconst 2
// CHECK:     v334 = icmp.eq v35, v333
// CHECK:     brif v334, bb20(v332), bb37(v332)
// CHECK:
// CHECK:   bb37(v336: mem):
// CHECK:     v337 = iconst 4
// CHECK:     v338 = icmp.eq v35, v337
// CHECK:     brif v338, bb19(v336), bb1(v336)
// CHECK:
// CHECK:   bb38(v340: mem):
// CHECK:     v341 = iconst 2
// CHECK:     v342 = icmp.eq v42, v341
// CHECK:     brif v342, bb17(v340), bb39(v340)
// CHECK:
// CHECK:   bb39(v344: mem):
// CHECK:     v345 = iconst 4
// CHECK:     v346 = icmp.eq v42, v345
// CHECK:     brif v346, bb16(v344), bb1(v344)
// CHECK:
// CHECK:   bb40(v348: mem):
// CHECK:     v349 = iconst 2
// CHECK:     v350 = icmp.eq v49, v349
// CHECK:     brif v350, bb14(v348), bb41(v348)
// CHECK:
// CHECK:   bb41(v352: mem):
// CHECK:     v353 = iconst 4
// CHECK:     v354 = icmp.eq v49, v353
// CHECK:     brif v354, bb13(v352), bb1(v352)
// CHECK:
// CHECK:   bb42(v356: mem):
// CHECK:     v357 = iconst 2
// CHECK:     v358 = icmp.eq v56, v357
// CHECK:     brif v358, bb11(v356), bb43(v356)
// CHECK:
// CHECK:   bb43(v360: mem):
// CHECK:     v361 = iconst 4
// CHECK:     v362 = icmp.eq v56, v361
// CHECK:     brif v362, bb10(v360), bb1(v360)
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
// CHECK: func @atomic_compare_exchange(%ptr: ptr, %expected: int:u32, %new: int:u32) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %ptr
// CHECK:     v2:u32 = param %expected
// CHECK:     v3:u32 = param %new
// CHECK:     v4 = stack_slot 8
// CHECK:     v5 = store.8 v1, v4, v0
// CHECK:     v6 = load.8 v4, v5
// CHECK:     v7 = iconst 4
// CHECK:     v8 = iconst 4
// CHECK:     v9 = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic23atomic_compare_exchangemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v10, v11 = call v9(v6, v2, v3, v7, v8), v5 -> int
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
// CHECK:     v1 = param %ptr
// CHECK:     v2:u32 = param %val
// CHECK:     v3 = stack_slot 8
// CHECK:     v4 = store.8 v1, v3, v0
// CHECK:     v5 = load.8 v3, v4
// CHECK:     v6 = load.4 v5, v4
// CHECK:     v7 = add v6, v2
// CHECK:     v8 = store.4 v7, v5, v4
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v6, v10
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
// CHECK: func @atomic_load_relaxed(%ptr: ptr) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %ptr
// CHECK:     v2 = stack_slot 8
// CHECK:     v3 = store.8 v1, v2, v0
// CHECK:     v4 = load.8 v2, v3
// CHECK:     v5 = iconst 0
// CHECK:     v6 = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic11atomic_loadmECseYAj3kFwz5z_10atomic_ops
// CHECK:     v7, v8 = call v6(v4, v5), v3 -> int
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
// CHECK:     v1 = param %ptr
// CHECK:     v2:u32 = param %val
// CHECK:     v3 = stack_slot 8
// CHECK:     v4 = store.8 v1, v3, v0
// CHECK:     v5 = load.8 v3, v4
// CHECK:     v6 = iconst 1
// CHECK:     v7 = symbol_addr @_RINvNtNtCsiYoX4ApF2vj_4core4sync6atomic12atomic_storemECseYAj3kFwz5z_10atomic_ops
// CHECK:     v8 = call v7(v5, v2, v6), v4
// CHECK:     v9 = iconst 0
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
// CHECK:     v1 = param %ptr
// CHECK:     v2:u32 = param %val
// CHECK:     v3 = stack_slot 8
// CHECK:     v4 = store.8 v1, v3, v0
// CHECK:     v5 = load.8 v3, v4
// CHECK:     v6 = load.4 v5, v4
// CHECK:     v7 = store.4 v2, v5, v4
// CHECK:     br bb1(v7)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     ret v6, v9
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
