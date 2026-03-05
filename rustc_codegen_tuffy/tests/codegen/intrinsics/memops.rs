//@ compile-flags: -C opt-level=0
// CHECK: fn std::ptr::write_bytes(_1: *mut T, _2: u8, _3: usize) -> () {
// CHECK:     debug dst => _1;
// CHECK:     debug val => _2;
// CHECK:     debug count => _3;
// CHECK:     let mut _0: ();
// CHECK:     let _4: ();
// CHECK:     let mut _5: *const ();
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::ub_checks::check_language_ub) {
// CHECK:         scope 2 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined std::mem::align_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(UbChecks) -> [0: bb6, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = copy _1 as *const () (PtrToPtr);
// CHECK:         StorageLive(_6);
// CHECK:         switchInt(const <T as std::mem::SizedTypeProperties>::IS_ZST) -> [0: bb3, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _6 = const true;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _6 = Eq(copy _3, const 0_usize);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _4 = std::ptr::write_bytes::precondition_check(move _5, const <T as std::mem::SizedTypeProperties>::ALIGN, move _6) -> [return: bb5, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb6;
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = std::intrinsics::write_bytes::<T>(move _1, move _2, move _3) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core3ptr11write_byteshECs7z8KAC7jnax_6memops(%dst: ptr, %val: int:u8, %count: int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %dst
// CHECK:     v2:u8 = param %val
// CHECK:     v3:u64 = param %count
// CHECK:     v4 = stack_slot 1
// CHECK:     v5 = iconst 0
// CHECK:     v6 = iconst 0
// CHECK:     v7 = icmp.eq v5, v6
// CHECK:     brif v7, bb6(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10 = bconst false
// CHECK:     v11 = bool_to_int v10
// CHECK:     v12 = iconst 255
// CHECK:     v13 = and v11, v12
// CHECK:     v14 = iconst 0
// CHECK:     v15 = icmp.eq v13, v14
// CHECK:     brif v15, bb3(v9), bb2(v9)
// CHECK:
// CHECK:   bb2(v17: mem):
// CHECK:     v18 = bconst true
// CHECK:     v19 = store.1 v18, v4, v17
// CHECK:     br bb4(v19)
// CHECK:
// CHECK:   bb3(v21: mem):
// CHECK:     v22 = iconst 0
// CHECK:     v23 = icmp.eq v3:u64, v22:u64
// CHECK:     v24 = bool_to_int v23
// CHECK:     v25 = store.1 v24, v4, v21
// CHECK:     br bb4(v25)
// CHECK:
// CHECK:   bb4(v27: mem):
// CHECK:     br bb5(v27)
// CHECK:
// CHECK:   bb5(v29: mem):
// CHECK:     br bb6(v29)
// CHECK:
// CHECK:   bb6(v31: mem):
// CHECK:     v32 = memset v1, v2, v3, align=1, v31
// CHECK:     br bb7(v32)
// CHECK:
// CHECK:   bb7(v34: mem):
// CHECK:     ret v34
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::copy_nonoverlapping(_1: *const T, _2: *mut T, _3: usize) -> () {
// CHECK:     debug src => _1;
// CHECK:     debug dst => _2;
// CHECK:     debug count => _3;
// CHECK:     let mut _0: ();
// CHECK:     let _4: ();
// CHECK:     let mut _5: *const ();
// CHECK:     let mut _6: *mut ();
// CHECK:     scope 1 (inlined core::ub_checks::check_language_ub) {
// CHECK:         scope 2 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined std::mem::size_of::<T>) {
// CHECK:     }
// CHECK:     scope 4 (inlined std::mem::align_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(UbChecks) -> [0: bb3, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = copy _1 as *const () (PtrToPtr);
// CHECK:         StorageLive(_6);
// CHECK:         _6 = copy _2 as *mut () (PtrToPtr);
// CHECK:         _4 = std::ptr::copy_nonoverlapping::precondition_check(move _5, move _6, const <T as std::mem::SizedTypeProperties>::SIZE, const <T as std::mem::SizedTypeProperties>::ALIGN, copy _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         copy_nonoverlapping(dst = copy _2, src = copy _1, count = copy _3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core3ptr19copy_nonoverlappinghECs7z8KAC7jnax_6memops(%src: ptr, %dst: ptr, %count: int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %src
// CHECK:     v2 = param %dst
// CHECK:     v3:u64 = param %count
// CHECK:     v4 = iconst 0
// CHECK:     v5 = iconst 0
// CHECK:     v6 = icmp.eq v4, v5
// CHECK:     brif v6, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     br bb2(v8)
// CHECK:
// CHECK:   bb2(v10: mem):
// CHECK:     br bb3(v10)
// CHECK:
// CHECK:   bb3(v12: mem):
// CHECK:     v13 = symbol_addr @memcpy
// CHECK:     v14, v15 = call v13(v2, v1, v3), v12 -> int
// CHECK:     ret v14
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::copy(_1: *const T, _2: *mut T, _3: usize) -> () {
// CHECK:     debug src => _1;
// CHECK:     debug dst => _2;
// CHECK:     debug count => _3;
// CHECK:     let mut _0: ();
// CHECK:     let _4: ();
// CHECK:     let mut _5: *const ();
// CHECK:     let mut _6: *mut ();
// CHECK:     let mut _7: bool;
// CHECK:     scope 1 (inlined core::ub_checks::check_language_ub) {
// CHECK:         scope 2 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined std::mem::align_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(UbChecks) -> [0: bb6, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = copy _1 as *const () (PtrToPtr);
// CHECK:         StorageLive(_6);
// CHECK:         _6 = copy _2 as *mut () (PtrToPtr);
// CHECK:         StorageLive(_7);
// CHECK:         switchInt(const <T as std::mem::SizedTypeProperties>::IS_ZST) -> [0: bb3, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _7 = const true;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _7 = Eq(copy _3, const 0_usize);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _4 = std::ptr::copy::precondition_check(move _5, move _6, const <T as std::mem::SizedTypeProperties>::ALIGN, move _7) -> [return: bb5, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb6;
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         _0 = std::intrinsics::copy::<T>(move _1, move _2, move _3) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtCsgc7BJoiPOQP_4core3ptr4copyhECs7z8KAC7jnax_6memops(%src: ptr, %dst: ptr, %count: int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %src
// CHECK:     v2 = param %dst
// CHECK:     v3:u64 = param %count
// CHECK:     v4 = stack_slot 1
// CHECK:     v5 = iconst 0
// CHECK:     v6 = iconst 0
// CHECK:     v7 = icmp.eq v5, v6
// CHECK:     brif v7, bb6(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10 = bconst false
// CHECK:     v11 = bool_to_int v10
// CHECK:     v12 = iconst 255
// CHECK:     v13 = and v11, v12
// CHECK:     v14 = iconst 0
// CHECK:     v15 = icmp.eq v13, v14
// CHECK:     brif v15, bb3(v9), bb2(v9)
// CHECK:
// CHECK:   bb2(v17: mem):
// CHECK:     v18 = bconst true
// CHECK:     v19 = store.1 v18, v4, v17
// CHECK:     br bb4(v19)
// CHECK:
// CHECK:   bb3(v21: mem):
// CHECK:     v22 = iconst 0
// CHECK:     v23 = icmp.eq v3:u64, v22:u64
// CHECK:     v24 = bool_to_int v23
// CHECK:     v25 = store.1 v24, v4, v21
// CHECK:     br bb4(v25)
// CHECK:
// CHECK:   bb4(v27: mem):
// CHECK:     br bb5(v27)
// CHECK:
// CHECK:   bb5(v29: mem):
// CHECK:     br bb6(v29)
// CHECK:
// CHECK:   bb6(v31: mem):
// CHECK:     v32 = memmove v2, v1, v3, align=1, v31
// CHECK:     br bb7(v32)
// CHECK:
// CHECK:   bb7(v34: mem):
// CHECK:     ret v34
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::const_ptr::<impl *const T>::is_aligned_to(_1: *const T, _2: usize) -> bool {
// CHECK:     debug self => _1;
// CHECK:     debug align => _2;
// CHECK:     let mut _0: bool;
// CHECK:     let _3: !;
// CHECK:     let mut _4: std::fmt::Arguments<'_>;
// CHECK:     let mut _5: usize;
// CHECK:     let mut _6: usize;
// CHECK:     let mut _7: usize;
// CHECK:     let mut _10: &str;
// CHECK:     scope 1 (inlined core::num::<impl usize>::is_power_of_two) {
// CHECK:         debug self => _2;
// CHECK:         let mut _8: u32;
// CHECK:         scope 2 (inlined core::num::<impl usize>::count_ones) {
// CHECK:             debug self => _2;
// CHECK:         }
// CHECK:     }
// CHECK:     scope 3 (inlined std::ptr::const_ptr::<impl *const T>::addr) {
// CHECK:         debug self => _1;
// CHECK:         let mut _9: *const ();
// CHECK:         scope 4 (inlined std::ptr::const_ptr::<impl *const T>::cast::<()>) {
// CHECK:             debug self => _1;
// CHECK:         }
// CHECK:     }
// CHECK:     scope 5 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _10;
// CHECK:         let mut _11: std::ptr::NonNull<u8>;
// CHECK:         let mut _12: *const u8;
// CHECK:         let mut _13: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _14: usize;
// CHECK:         let mut _15: usize;
// CHECK:         let mut _16: usize;
// CHECK:         scope 6 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _10;
// CHECK:             let mut _17: *const str;
// CHECK:         }
// CHECK:         scope 7 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _10;
// CHECK:             let _18: &[u8];
// CHECK:             scope 8 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _10;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_8);
// CHECK:         _8 = std::intrinsics::ctpop::<usize>(copy _2) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_8);
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _1 as *const () (PtrToPtr);
// CHECK:         _6 = copy _9 as usize (Transmute);
// CHECK:         StorageDead(_9);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = Sub(copy _2, const 1_usize);
// CHECK:         _5 = BitAnd(move _6, move _7);
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_6);
// CHECK:         _0 = Eq(move _5, const 0_usize);
// CHECK:         StorageDead(_5);
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_8);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = const "is_aligned_to: align is not a power-of-two";
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = &raw const (*_10);
// CHECK:         _12 = copy _17 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_17);
// CHECK:         _11 = copy _12 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_12);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         StorageLive(_16);
// CHECK:         StorageLive(_18);
// CHECK:         _18 = const "is_aligned_to: align is not a power-of-two" as &[u8] (Transmute);
// CHECK:         _16 = PtrMetadata(copy _18);
// CHECK:         StorageDead(_18);
// CHECK:         _15 = Shl(move _16, const 1_i32);
// CHECK:         StorageDead(_16);
// CHECK:         _14 = BitOr(move _15, const 1_usize);
// CHECK:         StorageDead(_15);
// CHECK:         _13 = move _14 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_14);
// CHECK:         _4 = std::fmt::Arguments::<'_> { template: move _11, args: move _13 };
// CHECK:         StorageDead(_13);
// CHECK:         StorageDead(_11);
// CHECK:         StorageDead(_10);
// CHECK:         _3 = std::rt::panic_fmt(move _4) -> unwind continue;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         switchInt(copy _8) -> [1: bb1, otherwise: bb2];
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc5 (size: 42, align: 1) {
// CHECK:     0x00 │ 69 73 5f 61 6c 69 67 6e 65 64 5f 74 6f 3a 20 61 │ is_aligned_to: a
// CHECK:     0x10 │ 6c 69 67 6e 20 69 73 20 6e 6f 74 20 61 20 70 6f │ lign is not a po
// CHECK:     0x20 │ 77 65 72 2d 6f 66 2d 74 77 6f                   │ wer-of-two
// CHECK: }
// CHECK: data @.Lstr.0 = "is_aligned_to: align is not a power-of-two"
// CHECK: data @.Lstr.1 = "is_aligned_to: align is not a power-of-two"
// CHECK: data @.Lloc_file.2 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/panic.rs"
// CHECK: data @.Lloc.3 = "\0\0\0\0\0\0\0\0l\0\0\0\0\0\0\0>\0\0\0\t\0\0\0"
// CHECK: func @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops(%self: ptr, %align: int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %self
// CHECK:     v2:u64 = param %align
// CHECK:     v3 = stack_slot 16
// CHECK:     v4 = stack_slot 16
// CHECK:     v5 = count_ones v2
// CHECK:     br bb3(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     v8 = ptrtoaddr v1
// CHECK:     v9 = iconst 1
// CHECK:     v10:i64 = sub v2:u64, v9:u64
// CHECK:     v11 = zext v10:i64, 64
// CHECK:     v12:u64 = and v8:u64, v11:u64
// CHECK:     v13 = iconst 0
// CHECK:     v14 = icmp.eq v12:u64, v13:u64
// CHECK:     v15 = bool_to_int v14
// CHECK:     v16 = int_to_bool v15
// CHECK:     ret v16, v7
// CHECK:
// CHECK:   bb2(v18: mem):
// CHECK:     v19 = symbol_addr @.Lstr.0
// CHECK:     v20 = iconst 42
// CHECK:     v21 = iconst 42
// CHECK:     v22 = store.8 v19, v4, v18
// CHECK:     v23 = iconst 8
// CHECK:     v24 = ptradd v4, v23
// CHECK:     v25 = store.8 v21, v24, v22
// CHECK:     v26 = iconst 42
// CHECK:     v27 = iconst 8
// CHECK:     v28 = ptradd v4, v27
// CHECK:     v29 = store.8 v26, v28, v25
// CHECK:     v30 = load.8 v4, v29
// CHECK:     v31 = ptrtoaddr v30
// CHECK:     v32 = symbol_addr @.Lstr.1
// CHECK:     v33 = iconst 42
// CHECK:     v34 = store.8 v31, v3, v29
// CHECK:     v35 = iconst 0
// CHECK:     v36 = iconst 8
// CHECK:     v37 = ptradd v3, v36
// CHECK:     v38 = store.8 v35, v37, v34
// CHECK:     v39 = load.8 v3, v38
// CHECK:     v40 = iconst 8
// CHECK:     v41 = ptradd v3, v40
// CHECK:     v42 = load.8 v41, v38
// CHECK:     v43 = symbol_addr @.Lloc.3
// CHECK:     v44 = symbol_addr @_RNvNtCsgc7BJoiPOQP_4core9panicking9panic_fmt
// CHECK:     v45, v46 = call v44(v39, v42, v43), v38 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v48: mem):
// CHECK:     v49 = iconst 4294967295
// CHECK:     v50 = and v5, v49
// CHECK:     v51 = iconst 1
// CHECK:     v52 = icmp.eq v50, v51
// CHECK:     brif v52, bb1(v48), bb2(v48)
// CHECK: }
// CHECK:
// CHECK: fn std::intrinsics::cold_path() -> () {
// CHECK:     let mut _0: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsgc7BJoiPOQP_4core10intrinsics9cold_pathCs7z8KAC7jnax_6memops() {
// CHECK:   bb0(v0: mem):
// CHECK:     ret v0
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::write_bytes::precondition_check(_1: *const (), _2: usize, _3: bool) -> () {
// CHECK:     debug addr => _1;
// CHECK:     debug align => _2;
// CHECK:     debug zero_size => _3;
// CHECK:     let mut _0: ();
// CHECK:     let mut _4: bool;
// CHECK:     let _5: &str;
// CHECK:     let _6: !;
// CHECK:     let mut _7: std::fmt::Arguments<'_>;
// CHECK:     scope 1 {
// CHECK:         debug msg => _5;
// CHECK:         scope 10 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:             debug s => _5;
// CHECK:             let mut _11: std::ptr::NonNull<u8>;
// CHECK:             let mut _12: *const u8;
// CHECK:             let mut _13: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:             let mut _14: usize;
// CHECK:             let mut _15: usize;
// CHECK:             let mut _16: usize;
// CHECK:             scope 11 (inlined core::str::<impl str>::as_ptr) {
// CHECK:                 debug self => _5;
// CHECK:                 let mut _17: *const str;
// CHECK:             }
// CHECK:             scope 12 (inlined core::str::<impl str>::len) {
// CHECK:                 debug self => _5;
// CHECK:                 let _18: &[u8];
// CHECK:                 scope 13 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                     debug self => _5;
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 2 (inlined core::ub_checks::maybe_is_aligned_and_not_null) {
// CHECK:         debug ptr => _1;
// CHECK:         debug align => _2;
// CHECK:         debug is_zst => _3;
// CHECK:         let mut _8: bool;
// CHECK:         let mut _9: bool;
// CHECK:         scope 3 (inlined core::ub_checks::maybe_is_aligned) {
// CHECK:             debug ptr => _1;
// CHECK:             debug align => _2;
// CHECK:             scope 4 (inlined core::ub_checks::maybe_is_aligned::runtime) {
// CHECK:                 debug ptr => _1;
// CHECK:                 debug align => _2;
// CHECK:             }
// CHECK:         }
// CHECK:         scope 5 (inlined std::ptr::const_ptr::<impl *const ()>::is_null) {
// CHECK:             debug self => _1;
// CHECK:             scope 6 {
// CHECK:                 scope 7 (inlined std::ptr::const_ptr::<impl *const T>::is_null::runtime) {
// CHECK:                     let mut _10: usize;
// CHECK:                     scope 8 (inlined std::ptr::const_ptr::<impl *const u8>::addr) {
// CHECK:                         scope 9 (inlined std::ptr::const_ptr::<impl *const u8>::cast::<()>) {
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(copy _1, move _2) -> [return: bb7, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_4);
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _5 = const "unsafe precondition(s) violated: ptr::write_bytes requires that the destination pointer is aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.";
// CHECK:         StorageLive(_7);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = &raw const (*_5);
// CHECK:         _12 = copy _17 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_17);
// CHECK:         _11 = copy _12 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_12);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         StorageLive(_16);
// CHECK:         StorageLive(_18);
// CHECK:         _18 = const "unsafe precondition(s) violated: ptr::write_bytes requires that the destination pointer is aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety." as &[u8] (Transmute);
// CHECK:         _16 = PtrMetadata(copy _18);
// CHECK:         StorageDead(_18);
// CHECK:         _15 = Shl(move _16, const 1_i32);
// CHECK:         StorageDead(_16);
// CHECK:         _14 = BitOr(move _15, const 1_usize);
// CHECK:         StorageDead(_15);
// CHECK:         _13 = move _14 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_14);
// CHECK:         _7 = std::fmt::Arguments::<'_> { template: move _11, args: move _13 };
// CHECK:         StorageDead(_13);
// CHECK:         StorageDead(_11);
// CHECK:         _6 = core::panicking::panic_nounwind_fmt(move _7, const false) -> unwind unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         switchInt(copy _3) -> [0: bb6, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageDead(_8);
// CHECK:         goto -> bb2;
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageDead(_8);
// CHECK:         goto -> bb1;
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_10);
// CHECK:         _10 = copy _1 as usize (Transmute);
// CHECK:         _9 = Eq(move _10, const 0_usize);
// CHECK:         StorageDead(_10);
// CHECK:         _4 = Not(move _9);
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         switchInt(move _4) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         switchInt(move _8) -> [0: bb4, otherwise: bb3];
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc4 (size: 228, align: 1) {
// CHECK:     0x00 │ 75 6e 73 61 66 65 20 70 72 65 63 6f 6e 64 69 74 │ unsafe precondit
// CHECK:     0x10 │ 69 6f 6e 28 73 29 20 76 69 6f 6c 61 74 65 64 3a │ ion(s) violated:
// CHECK:     0x20 │ 20 70 74 72 3a 3a 77 72 69 74 65 5f 62 79 74 65 │  ptr::write_byte
// CHECK:     0x30 │ 73 20 72 65 71 75 69 72 65 73 20 74 68 61 74 20 │ s requires that
// CHECK:     0x40 │ 74 68 65 20 64 65 73 74 69 6e 61 74 69 6f 6e 20 │ the destination
// CHECK:     0x50 │ 70 6f 69 6e 74 65 72 20 69 73 20 61 6c 69 67 6e │ pointer is align
// CHECK:     0x60 │ 65 64 20 61 6e 64 20 6e 6f 6e 2d 6e 75 6c 6c 0a │ ed and non-null.
// CHECK:     0x70 │ 0a 54 68 69 73 20 69 6e 64 69 63 61 74 65 73 20 │ .This indicates
// CHECK:     0x80 │ 61 20 62 75 67 20 69 6e 20 74 68 65 20 70 72 6f │ a bug in the pro
// CHECK:     0x90 │ 67 72 61 6d 2e 20 54 68 69 73 20 55 6e 64 65 66 │ gram. This Undef
// CHECK:     0xa0 │ 69 6e 65 64 20 42 65 68 61 76 69 6f 72 20 63 68 │ ined Behavior ch
// CHECK:     0xb0 │ 65 63 6b 20 69 73 20 6f 70 74 69 6f 6e 61 6c 2c │ eck is optional,
// CHECK:     0xc0 │ 20 61 6e 64 20 63 61 6e 6e 6f 74 20 62 65 20 72 │  and cannot be r
// CHECK:     0xd0 │ 65 6c 69 65 64 20 6f 6e 20 66 6f 72 20 73 61 66 │ elied on for saf
// CHECK:     0xe0 │ 65 74 79 2e                                     │ ety.
// CHECK: }
// CHECK: data @.Lstr.4 = "unsafe precondition(s) violated: ptr::write_bytes requires that the destination pointer is aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lstr.5 = "unsafe precondition(s) violated: ptr::write_bytes requires that the destination pointer is aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lloc_file.6 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.7 = "\0\0\0\0\0\0\0\0p\0\0\0\0\0\0\0I\0\0\0\x15\0\0\0"
// CHECK: func @_RNvNvNtCsgc7BJoiPOQP_4core3ptr11write_bytes18precondition_checkCs7z8KAC7jnax_6memops(%self: ptr, %align: int:u64, %is_zst: bool) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %self
// CHECK:     v2:u64 = param %align
// CHECK:     v3 = param %is_zst
// CHECK:     v4 = stack_slot 16
// CHECK:     v5 = stack_slot 16
// CHECK:     v6 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v7, v8 = call v6(v1, v2), v0 -> bool
// CHECK:     br bb7(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v10
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13 = symbol_addr @.Lstr.4
// CHECK:     v14 = iconst 228
// CHECK:     v15 = iconst 228
// CHECK:     v16 = store.8 v13, v5, v12
// CHECK:     v17 = iconst 8
// CHECK:     v18 = ptradd v5, v17
// CHECK:     v19 = store.8 v15, v18, v16
// CHECK:     v20 = iconst 228
// CHECK:     v21 = iconst 8
// CHECK:     v22 = ptradd v5, v21
// CHECK:     v23 = store.8 v20, v22, v19
// CHECK:     v24 = load.8 v5, v23
// CHECK:     v25 = ptrtoaddr v24
// CHECK:     v26 = symbol_addr @.Lstr.5
// CHECK:     v27 = iconst 228
// CHECK:     v28 = store.8 v25, v4, v23
// CHECK:     v29 = iconst 0
// CHECK:     v30 = iconst 8
// CHECK:     v31 = ptradd v4, v30
// CHECK:     v32 = store.8 v29, v31, v28
// CHECK:     v33 = load.8 v4, v32
// CHECK:     v34 = iconst 8
// CHECK:     v35 = ptradd v4, v34
// CHECK:     v36 = load.8 v35, v32
// CHECK:     v37 = bconst false
// CHECK:     v38 = symbol_addr @.Lloc.7
// CHECK:     v39 = symbol_addr @_RNvNtCsgc7BJoiPOQP_4core9panicking18panic_nounwind_fmt
// CHECK:     v40, v41 = call v39(v33, v36, v37, v38), v32 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v43: mem):
// CHECK:     v44 = bool_to_int v3
// CHECK:     v45 = iconst 255
// CHECK:     v46 = and v44, v45
// CHECK:     v47 = iconst 0
// CHECK:     v48 = icmp.eq v46, v47
// CHECK:     brif v48, bb6(v43), bb5(v43)
// CHECK:
// CHECK:   bb4(v50: mem):
// CHECK:     br bb2(v50)
// CHECK:
// CHECK:   bb5(v52: mem):
// CHECK:     br bb1(v52)
// CHECK:
// CHECK:   bb6(v54: mem):
// CHECK:     v55 = ptrtoaddr v1
// CHECK:     v56 = iconst 0
// CHECK:     v57 = icmp.eq v55:u64, v56:u64
// CHECK:     v58 = bool_to_int v57
// CHECK:     v59 = iconst 1
// CHECK:     v60 = xor v58, v59
// CHECK:     v61 = iconst 255
// CHECK:     v62 = and v60, v61
// CHECK:     v63 = iconst 0
// CHECK:     v64 = icmp.eq v62, v63
// CHECK:     brif v64, bb2(v54), bb1(v54)
// CHECK:
// CHECK:   bb7(v66: mem):
// CHECK:     v67 = bool_to_int v8
// CHECK:     v68 = iconst 255
// CHECK:     v69 = and v67, v68
// CHECK:     v70 = iconst 0
// CHECK:     v71 = icmp.eq v69, v70
// CHECK:     brif v71, bb4(v66), bb3(v66)
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::copy_nonoverlapping::precondition_check(_1: *const (), _2: *mut (), _3: usize, _4: usize, _5: usize) -> () {
// CHECK:     debug src => _1;
// CHECK:     debug dst => _2;
// CHECK:     debug size => _3;
// CHECK:     debug align => _4;
// CHECK:     debug count => _5;
// CHECK:     let mut _0: ();
// CHECK:     let mut _6: bool;
// CHECK:     let _7: bool;
// CHECK:     let mut _8: bool;
// CHECK:     let mut _9: bool;
// CHECK:     let mut _10: bool;
// CHECK:     let mut _11: *const ();
// CHECK:     let _12: &str;
// CHECK:     let _13: !;
// CHECK:     let mut _14: std::fmt::Arguments<'_>;
// CHECK:     scope 1 {
// CHECK:         debug zero_size => _7;
// CHECK:         scope 3 (inlined core::ub_checks::maybe_is_aligned_and_not_null) {
// CHECK:             debug ptr => _1;
// CHECK:             debug align => _4;
// CHECK:             debug is_zst => _9;
// CHECK:             let mut _15: bool;
// CHECK:             let mut _16: bool;
// CHECK:             scope 4 (inlined core::ub_checks::maybe_is_aligned) {
// CHECK:                 debug ptr => _1;
// CHECK:                 debug align => _4;
// CHECK:                 scope 5 (inlined core::ub_checks::maybe_is_aligned::runtime) {
// CHECK:                     debug ptr => _1;
// CHECK:                     debug align => _4;
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 6 (inlined std::ptr::const_ptr::<impl *const ()>::is_null) {
// CHECK:                 debug self => _1;
// CHECK:                 scope 7 {
// CHECK:                     scope 8 (inlined std::ptr::const_ptr::<impl *const T>::is_null::runtime) {
// CHECK:                         let mut _17: usize;
// CHECK:                         scope 9 (inlined std::ptr::const_ptr::<impl *const u8>::addr) {
// CHECK:                             scope 10 (inlined std::ptr::const_ptr::<impl *const u8>::cast::<()>) {
// CHECK:                             }
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 11 (inlined core::ub_checks::maybe_is_aligned_and_not_null) {
// CHECK:             debug ptr => _11;
// CHECK:             debug align => _4;
// CHECK:             debug is_zst => _7;
// CHECK:             let mut _18: bool;
// CHECK:             let mut _19: bool;
// CHECK:             scope 12 (inlined core::ub_checks::maybe_is_aligned) {
// CHECK:                 debug ptr => _11;
// CHECK:                 debug align => _4;
// CHECK:                 scope 13 (inlined core::ub_checks::maybe_is_aligned::runtime) {
// CHECK:                     debug ptr => _11;
// CHECK:                     debug align => _4;
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 14 (inlined std::ptr::const_ptr::<impl *const ()>::is_null) {
// CHECK:                 debug self => _11;
// CHECK:                 scope 15 {
// CHECK:                     scope 16 (inlined std::ptr::const_ptr::<impl *const T>::is_null::runtime) {
// CHECK:                         let mut _20: usize;
// CHECK:                         scope 17 (inlined std::ptr::const_ptr::<impl *const u8>::addr) {
// CHECK:                             scope 18 (inlined std::ptr::const_ptr::<impl *const u8>::cast::<()>) {
// CHECK:                             }
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 19 (inlined core::ub_checks::maybe_is_nonoverlapping) {
// CHECK:             debug src => _1;
// CHECK:             debug dst => _11;
// CHECK:             debug size => _3;
// CHECK:             debug count => _5;
// CHECK:         }
// CHECK:     }
// CHECK:     scope 2 {
// CHECK:         debug msg => _12;
// CHECK:         scope 20 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:             debug s => _12;
// CHECK:             let mut _21: std::ptr::NonNull<u8>;
// CHECK:             let mut _22: *const u8;
// CHECK:             let mut _23: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:             let mut _24: usize;
// CHECK:             let mut _25: usize;
// CHECK:             let mut _26: usize;
// CHECK:             scope 21 (inlined core::str::<impl str>::as_ptr) {
// CHECK:                 debug self => _12;
// CHECK:                 let mut _27: *const str;
// CHECK:             }
// CHECK:             scope 22 (inlined core::str::<impl str>::len) {
// CHECK:                 debug self => _12;
// CHECK:                 let _28: &[u8];
// CHECK:                 scope 23 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                     debug self => _12;
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_6);
// CHECK:         switchInt(copy _5) -> [0: bb1, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _7 = const true;
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _7 = Eq(copy _3, const 0_usize);
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageLive(_8);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = copy _7;
// CHECK:         StorageLive(_15);
// CHECK:         _15 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(copy _1, copy _4) -> [return: bb15, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageDead(_9);
// CHECK:         StorageLive(_10);
// CHECK:         _11 = copy _2 as *const () (PtrToPtr);
// CHECK:         StorageLive(_18);
// CHECK:         _18 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(copy _11, move _4) -> [return: bb20, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _6 = core::ub_checks::maybe_is_nonoverlapping::runtime(move _1, move _11, move _3, move _5) -> [return: bb21, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         goto -> bb8;
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_9);
// CHECK:         goto -> bb8;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_8);
// CHECK:         goto -> bb9;
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         _12 = const "unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.";
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_27);
// CHECK:         _27 = &raw const (*_12);
// CHECK:         _22 = copy _27 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_27);
// CHECK:         _21 = copy _22 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_22);
// CHECK:         StorageLive(_23);
// CHECK:         StorageLive(_24);
// CHECK:         StorageLive(_25);
// CHECK:         StorageLive(_26);
// CHECK:         StorageLive(_28);
// CHECK:         _28 = const "unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety." as &[u8] (Transmute);
// CHECK:         _26 = PtrMetadata(copy _28);
// CHECK:         StorageDead(_28);
// CHECK:         _25 = Shl(move _26, const 1_i32);
// CHECK:         StorageDead(_26);
// CHECK:         _24 = BitOr(move _25, const 1_usize);
// CHECK:         StorageDead(_25);
// CHECK:         _23 = move _24 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_24);
// CHECK:         _14 = std::fmt::Arguments::<'_> { template: move _21, args: move _23 };
// CHECK:         StorageDead(_23);
// CHECK:         StorageDead(_21);
// CHECK:         _13 = core::panicking::panic_nounwind_fmt(move _14, const false) -> unwind unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         StorageDead(_6);
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         switchInt(copy _9) -> [0: bb14, otherwise: bb13];
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         StorageDead(_15);
// CHECK:         goto -> bb7;
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         StorageDead(_15);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageLive(_16);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = copy _1 as usize (Transmute);
// CHECK:         _16 = Eq(move _17, const 0_usize);
// CHECK:         StorageDead(_17);
// CHECK:         _8 = Not(move _16);
// CHECK:         StorageDead(_16);
// CHECK:         StorageDead(_15);
// CHECK:         switchInt(move _8) -> [0: bb7, otherwise: bb4];
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         switchInt(move _15) -> [0: bb12, otherwise: bb11];
// CHECK:     }
// CHECK:
// CHECK:     bb16: {
// CHECK:         switchInt(copy _7) -> [0: bb19, otherwise: bb18];
// CHECK:     }
// CHECK:
// CHECK:     bb17: {
// CHECK:         StorageDead(_18);
// CHECK:         goto -> bb6;
// CHECK:     }
// CHECK:
// CHECK:     bb18: {
// CHECK:         StorageDead(_18);
// CHECK:         goto -> bb5;
// CHECK:     }
// CHECK:
// CHECK:     bb19: {
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_20);
// CHECK:         _20 = copy _2 as usize (Transmute);
// CHECK:         _19 = Eq(move _20, const 0_usize);
// CHECK:         StorageDead(_20);
// CHECK:         _10 = Not(move _19);
// CHECK:         StorageDead(_19);
// CHECK:         StorageDead(_18);
// CHECK:         switchInt(move _10) -> [0: bb6, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb20: {
// CHECK:         switchInt(move _18) -> [0: bb17, otherwise: bb16];
// CHECK:     }
// CHECK:
// CHECK:     bb21: {
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_8);
// CHECK:         switchInt(move _6) -> [0: bb9, otherwise: bb10];
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc6 (size: 283, align: 1) {
// CHECK:     0x000 │ 75 6e 73 61 66 65 20 70 72 65 63 6f 6e 64 69 74 │ unsafe precondit
// CHECK:     0x010 │ 69 6f 6e 28 73 29 20 76 69 6f 6c 61 74 65 64 3a │ ion(s) violated:
// CHECK:     0x020 │ 20 70 74 72 3a 3a 63 6f 70 79 5f 6e 6f 6e 6f 76 │  ptr::copy_nonov
// CHECK:     0x030 │ 65 72 6c 61 70 70 69 6e 67 20 72 65 71 75 69 72 │ erlapping requir
// CHECK:     0x040 │ 65 73 20 74 68 61 74 20 62 6f 74 68 20 70 6f 69 │ es that both poi
// CHECK:     0x050 │ 6e 74 65 72 20 61 72 67 75 6d 65 6e 74 73 20 61 │ nter arguments a
// CHECK:     0x060 │ 72 65 20 61 6c 69 67 6e 65 64 20 61 6e 64 20 6e │ re aligned and n
// CHECK:     0x070 │ 6f 6e 2d 6e 75 6c 6c 20 61 6e 64 20 74 68 65 20 │ on-null and the
// CHECK:     0x080 │ 73 70 65 63 69 66 69 65 64 20 6d 65 6d 6f 72 79 │ specified memory
// CHECK:     0x090 │ 20 72 61 6e 67 65 73 20 64 6f 20 6e 6f 74 20 6f │  ranges do not o
// CHECK:     0x0a0 │ 76 65 72 6c 61 70 0a 0a 54 68 69 73 20 69 6e 64 │ verlap..This ind
// CHECK:     0x0b0 │ 69 63 61 74 65 73 20 61 20 62 75 67 20 69 6e 20 │ icates a bug in
// CHECK:     0x0c0 │ 74 68 65 20 70 72 6f 67 72 61 6d 2e 20 54 68 69 │ the program. Thi
// CHECK:     0x0d0 │ 73 20 55 6e 64 65 66 69 6e 65 64 20 42 65 68 61 │ s Undefined Beha
// CHECK:     0x0e0 │ 76 69 6f 72 20 63 68 65 63 6b 20 69 73 20 6f 70 │ vior check is op
// CHECK:     0x0f0 │ 74 69 6f 6e 61 6c 2c 20 61 6e 64 20 63 61 6e 6e │ tional, and cann
// CHECK:     0x100 │ 6f 74 20 62 65 20 72 65 6c 69 65 64 20 6f 6e 20 │ ot be relied on
// CHECK:     0x110 │ 66 6f 72 20 73 61 66 65 74 79 2e                │ for safety.
// CHECK: }
// CHECK: data @.Lstr.8 = "unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lstr.9 = "unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lloc_file.10 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.11 = "\0\0\0\0\0\0\0\0p\0\0\0\0\0\0\0I\0\0\0\x15\0\0\0"
// CHECK: func @_RNvNvNtCsgc7BJoiPOQP_4core3ptr19copy_nonoverlapping18precondition_checkCs7z8KAC7jnax_6memops(%self: ptr, %dst: ptr, %size: int:u64, %count: int:u64, %count: int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %self
// CHECK:     v2 = param %dst
// CHECK:     v3:u64 = param %size
// CHECK:     v4:u64 = param %count
// CHECK:     v5:u64 = param %count
// CHECK:     v6 = stack_slot 1
// CHECK:     v7 = stack_slot 16
// CHECK:     v8 = stack_slot 16
// CHECK:     v9 = iconst 0
// CHECK:     v10 = icmp.eq v5, v9
// CHECK:     brif v10, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     v13 = bconst true
// CHECK:     v14 = store.1 v13, v6, v12
// CHECK:     br bb3(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17 = iconst 0
// CHECK:     v18 = icmp.eq v3:u64, v17:u64
// CHECK:     v19 = bool_to_int v18
// CHECK:     v20 = store.1 v19, v6, v16
// CHECK:     br bb3(v20)
// CHECK:
// CHECK:   bb3(v22: mem):
// CHECK:     v23 = load.1 v6, v22
// CHECK:     v24 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v25, v26 = call v24(v1, v4), v22 -> bool
// CHECK:     br bb15(v25)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     v29 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v30, v31 = call v29(v2, v4), v28 -> bool
// CHECK:     br bb20(v30)
// CHECK:
// CHECK:   bb5(v33: mem):
// CHECK:     v34 = symbol_addr @_RNvNvNtCsgc7BJoiPOQP_4core9ub_checks23maybe_is_nonoverlapping7runtimeCs7z8KAC7jnax_6memops
// CHECK:     v35, v36 = call v34(v1, v2, v3, v5), v33 -> bool
// CHECK:     br bb21(v35)
// CHECK:
// CHECK:   bb6(v38: mem):
// CHECK:     br bb8(v38)
// CHECK:
// CHECK:   bb7(v40: mem):
// CHECK:     br bb8(v40)
// CHECK:
// CHECK:   bb8(v42: mem):
// CHECK:     br bb9(v42)
// CHECK:
// CHECK:   bb9(v44: mem):
// CHECK:     v45 = symbol_addr @.Lstr.8
// CHECK:     v46 = iconst 283
// CHECK:     v47 = iconst 283
// CHECK:     v48 = store.8 v45, v8, v44
// CHECK:     v49 = iconst 8
// CHECK:     v50 = ptradd v8, v49
// CHECK:     v51 = store.8 v47, v50, v48
// CHECK:     v52 = iconst 283
// CHECK:     v53 = iconst 8
// CHECK:     v54 = ptradd v8, v53
// CHECK:     v55 = store.8 v52, v54, v51
// CHECK:     v56 = load.8 v8, v55
// CHECK:     v57 = ptrtoaddr v56
// CHECK:     v58 = symbol_addr @.Lstr.9
// CHECK:     v59 = iconst 283
// CHECK:     v60 = store.8 v57, v7, v55
// CHECK:     v61 = iconst 0
// CHECK:     v62 = iconst 8
// CHECK:     v63 = ptradd v7, v62
// CHECK:     v64 = store.8 v61, v63, v60
// CHECK:     v65 = load.8 v7, v64
// CHECK:     v66 = iconst 8
// CHECK:     v67 = ptradd v7, v66
// CHECK:     v68 = load.8 v67, v64
// CHECK:     v69 = bconst false
// CHECK:     v70 = symbol_addr @.Lloc.11
// CHECK:     v71 = symbol_addr @_RNvNtCsgc7BJoiPOQP_4core9panicking18panic_nounwind_fmt
// CHECK:     v72, v73 = call v71(v65, v68, v69, v70), v64 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v75: mem):
// CHECK:     ret v75
// CHECK:
// CHECK:   bb11(v77: mem):
// CHECK:     v78 = bool_to_int v23
// CHECK:     v79 = iconst 255
// CHECK:     v80 = and v78, v79
// CHECK:     v81 = iconst 0
// CHECK:     v82 = icmp.eq v80, v81
// CHECK:     brif v82, bb14(v77), bb13(v77)
// CHECK:
// CHECK:   bb12(v84: mem):
// CHECK:     br bb7(v84)
// CHECK:
// CHECK:   bb13(v86: mem):
// CHECK:     br bb4(v86)
// CHECK:
// CHECK:   bb14(v88: mem):
// CHECK:     v89 = ptrtoaddr v1
// CHECK:     v90 = iconst 0
// CHECK:     v91 = icmp.eq v89:u64, v90:u64
// CHECK:     v92 = bool_to_int v91
// CHECK:     v93 = iconst 1
// CHECK:     v94 = xor v92, v93
// CHECK:     v95 = iconst 255
// CHECK:     v96 = and v94, v95
// CHECK:     v97 = iconst 0
// CHECK:     v98 = icmp.eq v96, v97
// CHECK:     brif v98, bb7(v88), bb4(v88)
// CHECK:
// CHECK:   bb15(v100: mem):
// CHECK:     v101 = bool_to_int v26
// CHECK:     v102 = iconst 255
// CHECK:     v103 = and v101, v102
// CHECK:     v104 = iconst 0
// CHECK:     v105 = icmp.eq v103, v104
// CHECK:     brif v105, bb12(v100), bb11(v100)
// CHECK:
// CHECK:   bb16(v107: mem):
// CHECK:     v108 = load.1 v6, v107
// CHECK:     v109 = bool_to_int v108
// CHECK:     v110 = iconst 255
// CHECK:     v111 = and v109, v110
// CHECK:     v112 = iconst 0
// CHECK:     v113 = icmp.eq v111, v112
// CHECK:     brif v113, bb19(v107), bb18(v107)
// CHECK:
// CHECK:   bb17(v115: mem):
// CHECK:     br bb6(v115)
// CHECK:
// CHECK:   bb18(v117: mem):
// CHECK:     br bb5(v117)
// CHECK:
// CHECK:   bb19(v119: mem):
// CHECK:     v120 = ptrtoaddr v2
// CHECK:     v121 = iconst 0
// CHECK:     v122 = icmp.eq v120:u64, v121:u64
// CHECK:     v123 = bool_to_int v122
// CHECK:     v124 = iconst 1
// CHECK:     v125 = xor v123, v124
// CHECK:     v126 = iconst 255
// CHECK:     v127 = and v125, v126
// CHECK:     v128 = iconst 0
// CHECK:     v129 = icmp.eq v127, v128
// CHECK:     brif v129, bb6(v119), bb5(v119)
// CHECK:
// CHECK:   bb20(v131: mem):
// CHECK:     v132 = bool_to_int v31
// CHECK:     v133 = iconst 255
// CHECK:     v134 = and v132, v133
// CHECK:     v135 = iconst 0
// CHECK:     v136 = icmp.eq v134, v135
// CHECK:     brif v136, bb17(v131), bb16(v131)
// CHECK:
// CHECK:   bb21(v138: mem):
// CHECK:     v139 = bool_to_int v36
// CHECK:     v140 = iconst 255
// CHECK:     v141 = and v139, v140
// CHECK:     v142 = iconst 0
// CHECK:     v143 = icmp.eq v141, v142
// CHECK:     brif v143, bb9(v138), bb10(v138)
// CHECK: }
// CHECK:
// CHECK: fn std::ptr::copy::precondition_check(_1: *const (), _2: *mut (), _3: usize, _4: bool) -> () {
// CHECK:     debug src => _1;
// CHECK:     debug dst => _2;
// CHECK:     debug align => _3;
// CHECK:     debug zero_size => _4;
// CHECK:     let mut _0: ();
// CHECK:     let mut _5: bool;
// CHECK:     let mut _6: bool;
// CHECK:     let mut _7: *const ();
// CHECK:     let mut _8: usize;
// CHECK:     let _9: &str;
// CHECK:     let _10: !;
// CHECK:     let mut _11: std::fmt::Arguments<'_>;
// CHECK:     scope 1 {
// CHECK:         debug msg => _9;
// CHECK:         scope 18 (inlined std::fmt::Arguments::<'_>::from_str) {
// CHECK:             debug s => _9;
// CHECK:             let mut _18: std::ptr::NonNull<u8>;
// CHECK:             let mut _19: *const u8;
// CHECK:             let mut _20: std::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:             let mut _21: usize;
// CHECK:             let mut _22: usize;
// CHECK:             let mut _23: usize;
// CHECK:             scope 19 (inlined core::str::<impl str>::as_ptr) {
// CHECK:                 debug self => _9;
// CHECK:                 let mut _24: *const str;
// CHECK:             }
// CHECK:             scope 20 (inlined core::str::<impl str>::len) {
// CHECK:                 debug self => _9;
// CHECK:                 let _25: &[u8];
// CHECK:                 scope 21 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                     debug self => _9;
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 2 (inlined core::ub_checks::maybe_is_aligned_and_not_null) {
// CHECK:         debug ptr => _1;
// CHECK:         debug align => _3;
// CHECK:         debug is_zst => _4;
// CHECK:         let mut _12: bool;
// CHECK:         let mut _13: bool;
// CHECK:         scope 3 (inlined core::ub_checks::maybe_is_aligned) {
// CHECK:             debug ptr => _1;
// CHECK:             debug align => _3;
// CHECK:             scope 4 (inlined core::ub_checks::maybe_is_aligned::runtime) {
// CHECK:                 debug ptr => _1;
// CHECK:                 debug align => _3;
// CHECK:             }
// CHECK:         }
// CHECK:         scope 5 (inlined std::ptr::const_ptr::<impl *const ()>::is_null) {
// CHECK:             debug self => _1;
// CHECK:             scope 6 {
// CHECK:                 scope 7 (inlined std::ptr::const_ptr::<impl *const T>::is_null::runtime) {
// CHECK:                     let mut _14: usize;
// CHECK:                     scope 8 (inlined std::ptr::const_ptr::<impl *const u8>::addr) {
// CHECK:                         scope 9 (inlined std::ptr::const_ptr::<impl *const u8>::cast::<()>) {
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 10 (inlined core::ub_checks::maybe_is_aligned_and_not_null) {
// CHECK:         debug ptr => _7;
// CHECK:         debug align => _8;
// CHECK:         debug is_zst => _4;
// CHECK:         let mut _15: bool;
// CHECK:         let mut _16: bool;
// CHECK:         scope 11 (inlined core::ub_checks::maybe_is_aligned) {
// CHECK:             debug ptr => _7;
// CHECK:             debug align => _8;
// CHECK:             scope 12 (inlined core::ub_checks::maybe_is_aligned::runtime) {
// CHECK:                 debug ptr => _7;
// CHECK:                 debug align => _8;
// CHECK:             }
// CHECK:         }
// CHECK:         scope 13 (inlined std::ptr::const_ptr::<impl *const ()>::is_null) {
// CHECK:             debug self => _7;
// CHECK:             scope 14 {
// CHECK:                 scope 15 (inlined std::ptr::const_ptr::<impl *const T>::is_null::runtime) {
// CHECK:                     let mut _17: usize;
// CHECK:                     scope 16 (inlined std::ptr::const_ptr::<impl *const u8>::addr) {
// CHECK:                         scope 17 (inlined std::ptr::const_ptr::<impl *const u8>::cast::<()>) {
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_12);
// CHECK:         _12 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(copy _1, copy _3) -> [return: bb9, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_7);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _9 = const "unsafe precondition(s) violated: ptr::copy requires that both pointer arguments are aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.";
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_18);
// CHECK:         StorageLive(_19);
// CHECK:         StorageLive(_24);
// CHECK:         _24 = &raw const (*_9);
// CHECK:         _19 = copy _24 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_24);
// CHECK:         _18 = copy _19 as std::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_19);
// CHECK:         StorageLive(_20);
// CHECK:         StorageLive(_21);
// CHECK:         StorageLive(_22);
// CHECK:         StorageLive(_23);
// CHECK:         StorageLive(_25);
// CHECK:         _25 = const "unsafe precondition(s) violated: ptr::copy requires that both pointer arguments are aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety." as &[u8] (Transmute);
// CHECK:         _23 = PtrMetadata(copy _25);
// CHECK:         StorageDead(_25);
// CHECK:         _22 = Shl(move _23, const 1_i32);
// CHECK:         StorageDead(_23);
// CHECK:         _21 = BitOr(move _22, const 1_usize);
// CHECK:         StorageDead(_22);
// CHECK:         _20 = move _21 as std::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_21);
// CHECK:         _11 = std::fmt::Arguments::<'_> { template: move _18, args: move _20 };
// CHECK:         StorageDead(_20);
// CHECK:         StorageDead(_18);
// CHECK:         _10 = core::panicking::panic_nounwind_fmt(move _11, const false) -> unwind unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         switchInt(copy _4) -> [0: bb8, otherwise: bb7];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageDead(_12);
// CHECK:         goto -> bb3;
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_12);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = copy _2 as *const () (PtrToPtr);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _3;
// CHECK:         StorageLive(_15);
// CHECK:         _15 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(move _7, move _3) -> [return: bb13, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         _14 = copy _1 as usize (Transmute);
// CHECK:         _13 = Eq(move _14, const 0_usize);
// CHECK:         StorageDead(_14);
// CHECK:         _5 = Not(move _13);
// CHECK:         StorageDead(_13);
// CHECK:         StorageDead(_12);
// CHECK:         switchInt(move _5) -> [0: bb3, otherwise: bb14];
// CHECK:     }
// CHECK:
// CHECK:     bb9: {
// CHECK:         switchInt(move _12) -> [0: bb6, otherwise: bb5];
// CHECK:     }
// CHECK:
// CHECK:     bb10: {
// CHECK:         StorageDead(_15);
// CHECK:         goto -> bb2;
// CHECK:     }
// CHECK:
// CHECK:     bb11: {
// CHECK:         StorageDead(_15);
// CHECK:         goto -> bb1;
// CHECK:     }
// CHECK:
// CHECK:     bb12: {
// CHECK:         StorageLive(_16);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = copy _2 as usize (Transmute);
// CHECK:         _16 = Eq(move _17, const 0_usize);
// CHECK:         StorageDead(_17);
// CHECK:         _6 = Not(move _16);
// CHECK:         StorageDead(_16);
// CHECK:         StorageDead(_15);
// CHECK:         switchInt(move _6) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb13: {
// CHECK:         switchInt(move _15) -> [0: bb10, otherwise: bb11];
// CHECK:     }
// CHECK:
// CHECK:     bb14: {
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = copy _2 as *const () (PtrToPtr);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = copy _3;
// CHECK:         StorageLive(_15);
// CHECK:         _15 = std::ptr::const_ptr::<impl *const ()>::is_aligned_to(move _7, move _3) -> [return: bb15, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb15: {
// CHECK:         switchInt(move _15) -> [0: bb10, otherwise: bb12];
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc9 (size: 221, align: 1) {
// CHECK:     0x00 │ 75 6e 73 61 66 65 20 70 72 65 63 6f 6e 64 69 74 │ unsafe precondit
// CHECK:     0x10 │ 69 6f 6e 28 73 29 20 76 69 6f 6c 61 74 65 64 3a │ ion(s) violated:
// CHECK:     0x20 │ 20 70 74 72 3a 3a 63 6f 70 79 20 72 65 71 75 69 │  ptr::copy requi
// CHECK:     0x30 │ 72 65 73 20 74 68 61 74 20 62 6f 74 68 20 70 6f │ res that both po
// CHECK:     0x40 │ 69 6e 74 65 72 20 61 72 67 75 6d 65 6e 74 73 20 │ inter arguments
// CHECK:     0x50 │ 61 72 65 20 61 6c 69 67 6e 65 64 20 61 6e 64 20 │ are aligned and
// CHECK:     0x60 │ 6e 6f 6e 2d 6e 75 6c 6c 0a 0a 54 68 69 73 20 69 │ non-null..This i
// CHECK:     0x70 │ 6e 64 69 63 61 74 65 73 20 61 20 62 75 67 20 69 │ ndicates a bug i
// CHECK:     0x80 │ 6e 20 74 68 65 20 70 72 6f 67 72 61 6d 2e 20 54 │ n the program. T
// CHECK:     0x90 │ 68 69 73 20 55 6e 64 65 66 69 6e 65 64 20 42 65 │ his Undefined Be
// CHECK:     0xa0 │ 68 61 76 69 6f 72 20 63 68 65 63 6b 20 69 73 20 │ havior check is
// CHECK:     0xb0 │ 6f 70 74 69 6f 6e 61 6c 2c 20 61 6e 64 20 63 61 │ optional, and ca
// CHECK:     0xc0 │ 6e 6e 6f 74 20 62 65 20 72 65 6c 69 65 64 20 6f │ nnot be relied o
// CHECK:     0xd0 │ 6e 20 66 6f 72 20 73 61 66 65 74 79 2e          │ n for safety.
// CHECK: }
// CHECK: data @.Lstr.12 = "unsafe precondition(s) violated: ptr::copy requires that both pointer arguments are aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lstr.13 = "unsafe precondition(s) violated: ptr::copy requires that both pointer arguments are aligned and non-null\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
// CHECK: data @.Lloc_file.14 = "/usr/local/rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.15 = "\0\0\0\0\0\0\0\0p\0\0\0\0\0\0\0I\0\0\0\x15\0\0\0"
// CHECK: func @_RNvNvNtCsgc7BJoiPOQP_4core3ptr4copy18precondition_checkCs7z8KAC7jnax_6memops(%self: ptr, %align: ptr, %is_zst: int:u64, %zero_size: bool) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %self
// CHECK:     v2 = param %align
// CHECK:     v3:u64 = param %is_zst
// CHECK:     v4 = param %zero_size
// CHECK:     v5 = stack_slot 8
// CHECK:     v6 = stack_slot 8
// CHECK:     v7 = stack_slot 1
// CHECK:     v8 = stack_slot 16
// CHECK:     v9 = stack_slot 16
// CHECK:     v10 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v11, v12 = call v10(v1, v3), v0 -> bool
// CHECK:     br bb9(v11)
// CHECK:
// CHECK:   bb1(v14: mem):
// CHECK:     ret v14
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     br bb4(v16)
// CHECK:
// CHECK:   bb3(v18: mem):
// CHECK:     br bb4(v18)
// CHECK:
// CHECK:   bb4(v20: mem):
// CHECK:     v21 = symbol_addr @.Lstr.12
// CHECK:     v22 = iconst 221
// CHECK:     v23 = iconst 221
// CHECK:     v24 = store.8 v21, v9, v20
// CHECK:     v25 = iconst 8
// CHECK:     v26 = ptradd v9, v25
// CHECK:     v27 = store.8 v23, v26, v24
// CHECK:     v28 = iconst 221
// CHECK:     v29 = iconst 8
// CHECK:     v30 = ptradd v9, v29
// CHECK:     v31 = store.8 v28, v30, v27
// CHECK:     v32 = load.8 v9, v31
// CHECK:     v33 = ptrtoaddr v32
// CHECK:     v34 = symbol_addr @.Lstr.13
// CHECK:     v35 = iconst 221
// CHECK:     v36 = store.8 v33, v8, v31
// CHECK:     v37 = iconst 0
// CHECK:     v38 = iconst 8
// CHECK:     v39 = ptradd v8, v38
// CHECK:     v40 = store.8 v37, v39, v36
// CHECK:     v41 = load.8 v8, v40
// CHECK:     v42 = iconst 8
// CHECK:     v43 = ptradd v8, v42
// CHECK:     v44 = load.8 v43, v40
// CHECK:     v45 = bconst false
// CHECK:     v46 = symbol_addr @.Lloc.15
// CHECK:     v47 = symbol_addr @_RNvNtCsgc7BJoiPOQP_4core9panicking18panic_nounwind_fmt
// CHECK:     v48, v49 = call v47(v41, v44, v45, v46), v40 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb5(v51: mem):
// CHECK:     v52 = bool_to_int v4
// CHECK:     v53 = iconst 255
// CHECK:     v54 = and v52, v53
// CHECK:     v55 = iconst 0
// CHECK:     v56 = icmp.eq v54, v55
// CHECK:     brif v56, bb8(v51), bb7(v51)
// CHECK:
// CHECK:   bb6(v58: mem):
// CHECK:     br bb3(v58)
// CHECK:
// CHECK:   bb7(v60: mem):
// CHECK:     v61 = store.8 v2, v5, v60
// CHECK:     v62 = store.8 v3, v6, v61
// CHECK:     v63 = load.8 v5, v62
// CHECK:     v64 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v65, v66 = call v64(v63, v3), v62 -> bool
// CHECK:     v67 = store.1 v66, v7, v65
// CHECK:     br bb13(v67)
// CHECK:
// CHECK:   bb8(v69: mem):
// CHECK:     v70 = ptrtoaddr v1
// CHECK:     v71 = iconst 0
// CHECK:     v72 = icmp.eq v70:u64, v71:u64
// CHECK:     v73 = bool_to_int v72
// CHECK:     v74 = iconst 1
// CHECK:     v75 = xor v73, v74
// CHECK:     v76 = iconst 255
// CHECK:     v77 = and v75, v76
// CHECK:     v78 = iconst 0
// CHECK:     v79 = icmp.eq v77, v78
// CHECK:     brif v79, bb3(v69), bb14(v69)
// CHECK:
// CHECK:   bb9(v81: mem):
// CHECK:     v82 = bool_to_int v12
// CHECK:     v83 = iconst 255
// CHECK:     v84 = and v82, v83
// CHECK:     v85 = iconst 0
// CHECK:     v86 = icmp.eq v84, v85
// CHECK:     brif v86, bb6(v81), bb5(v81)
// CHECK:
// CHECK:   bb10(v88: mem):
// CHECK:     br bb2(v88)
// CHECK:
// CHECK:   bb11(v90: mem):
// CHECK:     br bb1(v90)
// CHECK:
// CHECK:   bb12(v92: mem):
// CHECK:     v93 = ptrtoaddr v2
// CHECK:     v94 = iconst 0
// CHECK:     v95 = icmp.eq v93:u64, v94:u64
// CHECK:     v96 = bool_to_int v95
// CHECK:     v97 = iconst 1
// CHECK:     v98 = xor v96, v97
// CHECK:     v99 = iconst 255
// CHECK:     v100 = and v98, v99
// CHECK:     v101 = iconst 0
// CHECK:     v102 = icmp.eq v100, v101
// CHECK:     brif v102, bb2(v92), bb1(v92)
// CHECK:
// CHECK:   bb13(v104: mem):
// CHECK:     v105 = load.1 v7, v104
// CHECK:     v106 = bool_to_int v105
// CHECK:     v107 = iconst 255
// CHECK:     v108 = and v106, v107
// CHECK:     v109 = iconst 0
// CHECK:     v110 = icmp.eq v108, v109
// CHECK:     brif v110, bb10(v104), bb11(v104)
// CHECK:
// CHECK:   bb14(v112: mem):
// CHECK:     v113 = store.8 v2, v5, v112
// CHECK:     v114 = store.8 v3, v6, v113
// CHECK:     v115 = load.8 v5, v114
// CHECK:     v116 = symbol_addr @_RNvMNtNtCsgc7BJoiPOQP_4core3ptr9const_ptrPu13is_aligned_toCs7z8KAC7jnax_6memops
// CHECK:     v117, v118 = call v116(v115, v3), v114 -> bool
// CHECK:     v119 = store.1 v118, v7, v117
// CHECK:     br bb15(v119)
// CHECK:
// CHECK:   bb15(v121: mem):
// CHECK:     v122 = load.1 v7, v121
// CHECK:     v123 = bool_to_int v122
// CHECK:     v124 = iconst 255
// CHECK:     v125 = and v123, v124
// CHECK:     v126 = iconst 0
// CHECK:     v127 = icmp.eq v125, v126
// CHECK:     brif v127, bb10(v121), bb12(v121)
// CHECK: }
// CHECK:
// CHECK: fn core::ub_checks::maybe_is_nonoverlapping::runtime(_1: *const (), _2: *const (), _3: usize, _4: usize) -> bool {
// CHECK:     debug src => _1;
// CHECK:     debug dst => _2;
// CHECK:     debug size => _3;
// CHECK:     debug count => _4;
// CHECK:     let mut _0: bool;
// CHECK:     let _5: usize;
// CHECK:     let mut _7: !;
// CHECK:     let mut _9: std::option::Option<usize>;
// CHECK:     scope 1 {
// CHECK:         debug src_usize => _5;
// CHECK:         let _6: usize;
// CHECK:         scope 2 {
// CHECK:             debug dst_usize => _6;
// CHECK:             let _8: usize;
// CHECK:             scope 3 {
// CHECK:                 debug size => _8;
// CHECK:                 let _10: usize;
// CHECK:                 scope 4 {
// CHECK:                     debug diff => _10;
// CHECK:                 }
// CHECK:                 scope 14 (inlined core::num::<impl usize>::abs_diff) {
// CHECK:                     debug self => _5;
// CHECK:                     debug other => _6;
// CHECK:                     let mut _18: i32;
// CHECK:                     let mut _19: i32;
// CHECK:                     let mut _20: i32;
// CHECK:                     let mut _21: bool;
// CHECK:                     scope 15 (inlined std::mem::size_of::<usize>) {
// CHECK:                     }
// CHECK:                     scope 16 (inlined core::num::<impl i32>::wrapping_sub) {
// CHECK:                         debug self => _19;
// CHECK:                         debug rhs => _20;
// CHECK:                     }
// CHECK:                     scope 17 (inlined core::num::<impl i32>::unsigned_abs) {
// CHECK:                         debug self => _18;
// CHECK:                         scope 18 (inlined core::num::<impl i32>::wrapping_abs) {
// CHECK:                             debug self => _18;
// CHECK:                             scope 19 (inlined core::num::<impl i32>::is_negative) {
// CHECK:                                 debug self => _18;
// CHECK:                             }
// CHECK:                             scope 20 (inlined core::num::<impl i32>::wrapping_neg) {
// CHECK:                                 debug self => _18;
// CHECK:                                 scope 21 (inlined core::num::<impl i32>::wrapping_sub) {
// CHECK:                                 }
// CHECK:                             }
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 9 (inlined core::num::<impl usize>::checked_mul) {
// CHECK:                 debug self => _3;
// CHECK:                 debug rhs => _4;
// CHECK:                 scope 10 {
// CHECK:                     debug a => _16;
// CHECK:                     debug b => _12;
// CHECK:                     scope 13 (inlined std::intrinsics::unlikely) {
// CHECK:                         debug b => _12;
// CHECK:                         let _17: ();
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 11 (inlined core::num::<impl usize>::overflowing_mul) {
// CHECK:                     debug self => _3;
// CHECK:                     debug rhs => _4;
// CHECK:                     let _11: u64;
// CHECK:                     let _12: bool;
// CHECK:                     let mut _13: (u64, bool);
// CHECK:                     let mut _14: u64;
// CHECK:                     let mut _15: u64;
// CHECK:                     let mut _16: usize;
// CHECK:                     scope 12 {
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 7 (inlined std::ptr::const_ptr::<impl *const ()>::addr) {
// CHECK:             debug self => _2;
// CHECK:             scope 8 (inlined std::ptr::const_ptr::<impl *const ()>::cast::<()>) {
// CHECK:                 debug self => _2;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 5 (inlined std::ptr::const_ptr::<impl *const ()>::addr) {
// CHECK:         debug self => _1;
// CHECK:         scope 6 (inlined std::ptr::const_ptr::<impl *const ()>::cast::<()>) {
// CHECK:             debug self => _1;
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _5 = copy _1 as usize (Transmute);
// CHECK:         _6 = copy _2 as usize (Transmute);
// CHECK:         StorageLive(_9);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_16);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         _14 = copy _3 as u64 (IntToInt);
// CHECK:         StorageLive(_15);
// CHECK:         _15 = copy _4 as u64 (IntToInt);
// CHECK:         _13 = MulWithOverflow(move _14, move _15);
// CHECK:         StorageDead(_15);
// CHECK:         StorageDead(_14);
// CHECK:         _11 = copy (_13.0: u64);
// CHECK:         _12 = copy (_13.1: bool);
// CHECK:         StorageDead(_13);
// CHECK:         _16 = copy _11 as usize (IntToInt);
// CHECK:         StorageDead(_11);
// CHECK:         switchInt(copy _12) -> [0: bb3, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _17 = std::intrinsics::cold_path() -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_16);
// CHECK:         StorageDead(_12);
// CHECK:         StorageDead(_9);
// CHECK:         _7 = core::panicking::panic_nounwind(const "is_nonoverlapping: `size_of::<T>() * count` overflows a usize") -> unwind unreachable;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _9 = std::option::Option::<usize>::Some(copy _16);
// CHECK:         StorageDead(_16);
// CHECK:         StorageDead(_12);
// CHECK:         _8 = copy ((_9 as Some).0: usize);
// CHECK:         StorageDead(_9);
// CHECK:         StorageLive(_21);
// CHECK:         _21 = Lt(copy _5, copy _6);
// CHECK:         switchInt(move _21) -> [0: bb5, otherwise: bb4];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         _10 = Sub(copy _6, copy _5);
// CHECK:         goto -> bb6;
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         _10 = Sub(copy _5, copy _6);
// CHECK:         goto -> bb6;
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageDead(_21);
// CHECK:         _0 = Ge(move _10, copy _8);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc7 (size: 61, align: 1) {
// CHECK:     0x00 │ 69 73 5f 6e 6f 6e 6f 76 65 72 6c 61 70 70 69 6e │ is_nonoverlappin
// CHECK:     0x10 │ 67 3a 20 60 73 69 7a 65 5f 6f 66 3a 3a 3c 54 3e │ g: `size_of::<T>
// CHECK:     0x20 │ 28 29 20 2a 20 63 6f 75 6e 74 60 20 6f 76 65 72 │ () * count` over
// CHECK:     0x30 │ 66 6c 6f 77 73 20 61 20 75 73 69 7a 65          │ flows a usize
// CHECK: }
// CHECK: data @.Lstr.16 = "is_nonoverlapping: `size_of::<T>() * count` overflows a usize"
// CHECK: func @_RNvNvNtCsgc7BJoiPOQP_4core9ub_checks23maybe_is_nonoverlapping7runtimeCs7z8KAC7jnax_6memops(%self: ptr, %rhs: ptr, %size: int:u64, %count: int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %self
// CHECK:     v2 = param %rhs
// CHECK:     v3:u64 = param %size
// CHECK:     v4:u64 = param %count
// CHECK:     v5 = stack_slot 8
// CHECK:     v6 = stack_slot 16
// CHECK:     v7 = ptrtoaddr v1
// CHECK:     v8 = ptrtoaddr v2
// CHECK:     v9 = umul_overflow.64 v3:u64, v4:u64
// CHECK:     v11 = bool_to_int v10
// CHECK:     v12 = iconst 255
// CHECK:     v13 = and v11, v12
// CHECK:     v14 = iconst 0
// CHECK:     v15 = icmp.eq v13, v14
// CHECK:     brif v15, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     br bb2(v17)
// CHECK:
// CHECK:   bb2(v19: mem):
// CHECK:     v20 = symbol_addr @.Lstr.16
// CHECK:     v21 = iconst 61
// CHECK:     v22 = iconst 61
// CHECK:     v23 = symbol_addr @_RNvNtCsgc7BJoiPOQP_4core9panicking14panic_nounwind
// CHECK:     v24, v25 = call v23(v20, v22), v19 -> int
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v27: mem):
// CHECK:     v28 = iconst 0
// CHECK:     v29 = store.8 v28, v6, v27
// CHECK:     v30 = iconst 8
// CHECK:     v31 = ptradd v6, v30
// CHECK:     v32 = store.8 v28, v31, v29
// CHECK:     v33 = iconst 8
// CHECK:     v34 = ptradd v6, v33
// CHECK:     v35 = store.8 v9, v34, v32
// CHECK:     v36 = iconst 1
// CHECK:     v37 = store.8 v36, v6, v35
// CHECK:     v38 = iconst 8
// CHECK:     v39 = ptradd v6, v38
// CHECK:     v40 = load.8 v39, v37
// CHECK:     v41 = icmp.lt v7:u64, v8:u64
// CHECK:     v42 = bool_to_int v41
// CHECK:     v43 = iconst 255
// CHECK:     v44 = and v42, v43
// CHECK:     v45 = iconst 0
// CHECK:     v46 = icmp.eq v44, v45
// CHECK:     brif v46, bb5(v37), bb4(v37)
// CHECK:
// CHECK:   bb4(v48: mem):
// CHECK:     v49:i64 = sub v8:u64, v7:u64
// CHECK:     v50 = zext v49:i64, 64
// CHECK:     v51 = store.8 v50, v5, v48
// CHECK:     br bb6(v51)
// CHECK:
// CHECK:   bb5(v53: mem):
// CHECK:     v54:i64 = sub v7:u64, v8:u64
// CHECK:     v55 = zext v54:i64, 64
// CHECK:     v56 = store.8 v55, v5, v53
// CHECK:     br bb6(v56)
// CHECK:
// CHECK:   bb6(v58: mem):
// CHECK:     v59:u64 = load.8 v5, v58
// CHECK:     v60 = icmp.ge v59:u64, v40:u64
// CHECK:     v61 = bool_to_int v60
// CHECK:     v62 = int_to_bool v61
// CHECK:     ret v62, v58
// CHECK: }
// CHECK:
// CHECK: fn test_copy(_1: *mut u8, _2: *const u8) -> () {
// CHECK:     debug dst => _1;
// CHECK:     debug src => _2;
// CHECK:     let mut _0: ();
// CHECK:     let _3: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = std::ptr::copy::<u8>(copy _2, copy _1, const 16_usize) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @test_copy(%dst: ptr, %src: ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %dst
// CHECK:     v2 = param %src
// CHECK:     v3 = iconst 16
// CHECK:     v4 = symbol_addr @_RINvNtCsgc7BJoiPOQP_4core3ptr4copyhECs7z8KAC7jnax_6memops
// CHECK:     v5 = call v4(v2, v1, v3), v0
// CHECK:     v6 = iconst 0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v8
// CHECK: }
// CHECK:
// CHECK: fn test_copy_nonoverlapping(_1: *mut u8, _2: *const u8) -> () {
// CHECK:     debug dst => _1;
// CHECK:     debug src => _2;
// CHECK:     let mut _0: ();
// CHECK:     let _3: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = std::ptr::copy_nonoverlapping::<u8>(copy _2, copy _1, const 16_usize) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @test_copy_nonoverlapping(%dst: ptr, %src: ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %dst
// CHECK:     v2 = param %src
// CHECK:     v3 = iconst 16
// CHECK:     v4 = symbol_addr @_RINvNtCsgc7BJoiPOQP_4core3ptr19copy_nonoverlappinghECs7z8KAC7jnax_6memops
// CHECK:     v5 = call v4(v2, v1, v3), v0
// CHECK:     v6 = iconst 0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v8
// CHECK: }
// CHECK:
// CHECK: fn test_write_bytes(_1: *mut u8) -> () {
// CHECK:     debug dst => _1;
// CHECK:     let mut _0: ();
// CHECK:     let _2: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         _2 = std::ptr::write_bytes::<u8>(copy _1, const 66_u8, const 8_usize) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @test_write_bytes(%dst: ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %dst
// CHECK:     v2 = iconst 66
// CHECK:     v3 = iconst 8
// CHECK:     v4 = symbol_addr @_RINvNtCsgc7BJoiPOQP_4core3ptr11write_byteshECs7z8KAC7jnax_6memops
// CHECK:     v5 = call v4(v1, v2, v3), v0
// CHECK:     v6 = iconst 0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     ret v8
// CHECK: }
// CHECK:

#![crate_type = "lib"]

use std::ptr;

#[no_mangle]
pub unsafe fn test_write_bytes(dst: *mut u8) {
    ptr::write_bytes(dst, 0x42, 8);
}

#[no_mangle]
pub unsafe fn test_copy_nonoverlapping(dst: *mut u8, src: *const u8) {
    ptr::copy_nonoverlapping(src, dst, 16);
}

#[no_mangle]
pub unsafe fn test_copy(dst: *mut u8, src: *const u8) {
    ptr::copy(src, dst, 16);
}
