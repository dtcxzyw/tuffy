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
// CHECK: func @_RINvNtCsa3SJzwB9S2T_4core3ptr11write_byteshECse33uD6zc4Cp_6memops(ptr, int:u8, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u8 = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: ptr = stack_slot 1
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb6(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: bool = bconst false
// CHECK:     v11: int:u64 = iconst 1
// CHECK:     v12: int:u64 = iconst 0
// CHECK:     v13: int:u64 = select v10, v11, v12
// CHECK:     v14: int:i64 = iconst 255
// CHECK:     v15: int:u64 = and v13, v14
// CHECK:     v16: int:i8 = iconst 0
// CHECK:     v17: bool = icmp.eq v15, v16
// CHECK:     brif v17, bb3(v9), bb2(v9)
// CHECK:
// CHECK:   bb2(v19: mem):
// CHECK:     v20: bool = bconst true
// CHECK:     v21: mem = store.1 v20, v4, v19
// CHECK:     br bb4(v21)
// CHECK:
// CHECK:   bb3(v23: mem):
// CHECK:     v24: int:i64 = iconst 0
// CHECK:     v25: bool = icmp.eq v3, v24:u64
// CHECK:     v26: mem = store.1 v25, v4, v23
// CHECK:     br bb4(v26)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     br bb5(v28)
// CHECK:
// CHECK:   bb5(v30: mem):
// CHECK:     br bb6(v30)
// CHECK:
// CHECK:   bb6(v32: mem):
// CHECK:     v33: mem = memset v1:align1, v2, v3, v32
// CHECK:     br bb7(v33)
// CHECK:
// CHECK:   bb7(v35: mem):
// CHECK:     ret v35
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
// CHECK: func @_RINvNtCsa3SJzwB9S2T_4core3ptr19copy_nonoverlappinghECse33uD6zc4Cp_6memops(ptr, ptr, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:i64 = iconst 0
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: bool = icmp.eq v4, v5
// CHECK:     brif v6, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     br bb2(v8)
// CHECK:
// CHECK:   bb2(v10: mem):
// CHECK:     br bb3(v10)
// CHECK:
// CHECK:   bb3(v12: mem):
// CHECK:     v13: ptr = symbol_addr @memcpy
// CHECK:     v14: mem, v15: int:u64 = call v13(v2, v1, v3), v12 -> int:u64
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
// CHECK: func @_RINvNtCsa3SJzwB9S2T_4core3ptr4copyhECse33uD6zc4Cp_6memops(ptr, ptr, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: ptr = stack_slot 1
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     v7: bool = icmp.eq v5, v6
// CHECK:     brif v7, bb6(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v9: mem):
// CHECK:     v10: bool = bconst false
// CHECK:     v11: int:u64 = iconst 1
// CHECK:     v12: int:u64 = iconst 0
// CHECK:     v13: int:u64 = select v10, v11, v12
// CHECK:     v14: int:i64 = iconst 255
// CHECK:     v15: int:u64 = and v13, v14
// CHECK:     v16: int:i8 = iconst 0
// CHECK:     v17: bool = icmp.eq v15, v16
// CHECK:     brif v17, bb3(v9), bb2(v9)
// CHECK:
// CHECK:   bb2(v19: mem):
// CHECK:     v20: bool = bconst true
// CHECK:     v21: mem = store.1 v20, v4, v19
// CHECK:     br bb4(v21)
// CHECK:
// CHECK:   bb3(v23: mem):
// CHECK:     v24: int:i64 = iconst 0
// CHECK:     v25: bool = icmp.eq v3, v24:u64
// CHECK:     v26: mem = store.1 v25, v4, v23
// CHECK:     br bb4(v26)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     br bb5(v28)
// CHECK:
// CHECK:   bb5(v30: mem):
// CHECK:     br bb6(v30)
// CHECK:
// CHECK:   bb6(v32: mem):
// CHECK:     v33: mem = memmove v2:align1, v1:align1, v3, v32
// CHECK:     br bb7(v33)
// CHECK:
// CHECK:   bb7(v35: mem):
// CHECK:     ret v35
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
// CHECK: data @.Lloc_file.2 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.3 = "..." relocs [0: @.Lloc_file.2]
// CHECK: func @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops(ptr, int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: ptr = stack_slot 16
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: int:u64 = count_ones v2
// CHECK:     br bb3(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     v8: int:u64 = ptrtoaddr v1
// CHECK:     v9: int:i64 = iconst 1
// CHECK:     v10: int:i64 = sub v2, v9:u64
// CHECK:     v11: int:u64 = zext v10, 64
// CHECK:     v12: int:i64 = and v8, v11
// CHECK:     v13: int:u64 = zext v12, 64
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: bool = icmp.eq v13, v14:u64
// CHECK:     ret v15, v7
// CHECK:
// CHECK:   bb2(v17: mem):
// CHECK:     v18: ptr = symbol_addr @.Lstr.0
// CHECK:     v19: int:i64 = iconst 42
// CHECK:     v20: mem = store.8 v18, v4, v17
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v4, v21
// CHECK:     v23: mem = store.8 v19, v22, v20
// CHECK:     v24: int:i64 = iconst 42
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v4, v25
// CHECK:     v27: mem = store.8 v24, v26, v23
// CHECK:     v28: ptr = load.8 v4, v27
// CHECK:     v29: int:u64 = ptrtoaddr v28
// CHECK:     v30: ptr = symbol_addr @.Lstr.1
// CHECK:     v31: mem = store.8 v29, v3, v27
// CHECK:     v32: int:i64 = iconst 0
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v3, v33
// CHECK:     v35: mem = store.8 v32, v34, v31
// CHECK:     v36: int:i64 = load.8 v3, v35
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v3, v37
// CHECK:     v39: int:i64 = load.8 v38, v35
// CHECK:     v40: ptr = symbol_addr @.Lloc.3
// CHECK:     v41: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking9panic_fmt
// CHECK:     v42: mem = call v41(v36, v39, v40), v35
// CHECK:     v43: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v45: mem):
// CHECK:     v46: int:i64 = iconst 4294967295
// CHECK:     v47: int:u64 = and v5, v46
// CHECK:     v48: int:i32 = iconst 1
// CHECK:     v49: bool = icmp.eq v47, v48
// CHECK:     brif v49, bb1(v45), bb2(v45)
// CHECK: }
// CHECK:
// CHECK: fn std::intrinsics::cold_path() -> () {
// CHECK:     let mut _0: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtCsa3SJzwB9S2T_4core10intrinsics9cold_pathCse33uD6zc4Cp_6memops() {
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
// CHECK: data @.Lloc_file.6 = "$SYSROOT/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.7 = "..." relocs [0: @.Lloc_file.6]
// CHECK: func @_RNvNvNtCsa3SJzwB9S2T_4core3ptr11write_bytes18precondition_checkCse33uD6zc4Cp_6memops(ptr, int:u64, bool) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: bool = param 2
// CHECK:     v4: ptr = stack_slot 16
// CHECK:     v5: ptr = stack_slot 16
// CHECK:     v6: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v7: mem, v8: bool = call v6(v1, v2), v0 -> bool
// CHECK:     br bb7(v7)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     ret v10
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13: ptr = symbol_addr @.Lstr.4
// CHECK:     v14: int:i64 = iconst 228
// CHECK:     v15: mem = store.8 v13, v5, v12
// CHECK:     v16: int:i64 = iconst 8
// CHECK:     v17: ptr = ptradd v5, v16
// CHECK:     v18: mem = store.8 v14, v17, v15
// CHECK:     v19: int:i64 = iconst 228
// CHECK:     v20: int:i64 = iconst 8
// CHECK:     v21: ptr = ptradd v5, v20
// CHECK:     v22: mem = store.8 v19, v21, v18
// CHECK:     v23: ptr = load.8 v5, v22
// CHECK:     v24: int:u64 = ptrtoaddr v23
// CHECK:     v25: ptr = symbol_addr @.Lstr.5
// CHECK:     v26: mem = store.8 v24, v4, v22
// CHECK:     v27: int:i64 = iconst 0
// CHECK:     v28: int:i64 = iconst 8
// CHECK:     v29: ptr = ptradd v4, v28
// CHECK:     v30: mem = store.8 v27, v29, v26
// CHECK:     v31: int:i64 = load.8 v4, v30
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v4, v32
// CHECK:     v34: int:i64 = load.8 v33, v30
// CHECK:     v35: bool = bconst false
// CHECK:     v36: ptr = symbol_addr @.Lloc.7
// CHECK:     v37: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking18panic_nounwind_fmt
// CHECK:     v38: mem = call v37(v31, v34, v35, v36), v30
// CHECK:     v39: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v41: mem):
// CHECK:     v42: int:u64 = iconst 1
// CHECK:     v43: int:u64 = iconst 0
// CHECK:     v44: int:u64 = select v3, v42, v43
// CHECK:     v45: int:i64 = iconst 255
// CHECK:     v46: int:u64 = and v44, v45
// CHECK:     v47: int:i8 = iconst 0
// CHECK:     v48: bool = icmp.eq v46, v47
// CHECK:     brif v48, bb6(v41), bb5(v41)
// CHECK:
// CHECK:   bb4(v50: mem):
// CHECK:     br bb2(v50)
// CHECK:
// CHECK:   bb5(v52: mem):
// CHECK:     br bb1(v52)
// CHECK:
// CHECK:   bb6(v54: mem):
// CHECK:     v55: int:u64 = ptrtoaddr v1
// CHECK:     v56: int:i64 = iconst 0
// CHECK:     v57: bool = icmp.eq v55, v56:u64
// CHECK:     v58: int:u64 = iconst 1
// CHECK:     v59: int:u64 = iconst 0
// CHECK:     v60: int:u64 = select v57, v58, v59
// CHECK:     v61: int:i64 = iconst 1
// CHECK:     v62: int:i64 = xor v60, v61
// CHECK:     v63: int:i64 = iconst 255
// CHECK:     v64: int:u64 = and v62, v63
// CHECK:     v65: int:i8 = iconst 0
// CHECK:     v66: bool = icmp.eq v64, v65
// CHECK:     brif v66, bb2(v54), bb1(v54)
// CHECK:
// CHECK:   bb7(v68: mem):
// CHECK:     v69: int:u64 = iconst 1
// CHECK:     v70: int:u64 = iconst 0
// CHECK:     v71: int:u64 = select v8, v69, v70
// CHECK:     v72: int:i64 = iconst 255
// CHECK:     v73: int:u64 = and v71, v72
// CHECK:     v74: int:i8 = iconst 0
// CHECK:     v75: bool = icmp.eq v73, v74
// CHECK:     brif v75, bb4(v68), bb3(v68)
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
// CHECK: data @.Lloc_file.10 = "$SYSROOT/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.11 = "..." relocs [0: @.Lloc_file.10]
// CHECK: func @_RNvNvNtCsa3SJzwB9S2T_4core3ptr19copy_nonoverlapping18precondition_checkCse33uD6zc4Cp_6memops(ptr, ptr, int:u64, int:u64, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: int:u64 = param 4
// CHECK:     v6: ptr = stack_slot 1
// CHECK:     v7: ptr = stack_slot 16
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: int:i64 = iconst 0
// CHECK:     v10: bool = icmp.eq v5, v9
// CHECK:     brif v10, bb1(v0), bb2(v0)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     v13: bool = bconst true
// CHECK:     v14: mem = store.1 v13, v6, v12
// CHECK:     br bb3(v14)
// CHECK:
// CHECK:   bb2(v16: mem):
// CHECK:     v17: int:i64 = iconst 0
// CHECK:     v18: bool = icmp.eq v3, v17:u64
// CHECK:     v19: mem = store.1 v18, v6, v16
// CHECK:     br bb3(v19)
// CHECK:
// CHECK:   bb3(v21: mem):
// CHECK:     v22: bool = load.1 v6, v21
// CHECK:     v23: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v24: mem, v25: bool = call v23(v1, v4), v21 -> bool
// CHECK:     br bb15(v24)
// CHECK:
// CHECK:   bb4(v27: mem):
// CHECK:     v28: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v29: mem, v30: bool = call v28(v2, v4), v27 -> bool
// CHECK:     br bb20(v29)
// CHECK:
// CHECK:   bb5(v32: mem):
// CHECK:     v33: ptr = symbol_addr @_RNvNvNtCsa3SJzwB9S2T_4core9ub_checks23maybe_is_nonoverlapping7runtimeCse33uD6zc4Cp_6memops
// CHECK:     v34: mem, v35: bool = call v33(v1, v2, v3, v5), v32 -> bool
// CHECK:     br bb21(v34)
// CHECK:
// CHECK:   bb6(v37: mem):
// CHECK:     br bb8(v37)
// CHECK:
// CHECK:   bb7(v39: mem):
// CHECK:     br bb8(v39)
// CHECK:
// CHECK:   bb8(v41: mem):
// CHECK:     br bb9(v41)
// CHECK:
// CHECK:   bb9(v43: mem):
// CHECK:     v44: ptr = symbol_addr @.Lstr.8
// CHECK:     v45: int:i64 = iconst 283
// CHECK:     v46: mem = store.8 v44, v8, v43
// CHECK:     v47: int:i64 = iconst 8
// CHECK:     v48: ptr = ptradd v8, v47
// CHECK:     v49: mem = store.8 v45, v48, v46
// CHECK:     v50: int:i64 = iconst 283
// CHECK:     v51: int:i64 = iconst 8
// CHECK:     v52: ptr = ptradd v8, v51
// CHECK:     v53: mem = store.8 v50, v52, v49
// CHECK:     v54: ptr = load.8 v8, v53
// CHECK:     v55: int:u64 = ptrtoaddr v54
// CHECK:     v56: ptr = symbol_addr @.Lstr.9
// CHECK:     v57: mem = store.8 v55, v7, v53
// CHECK:     v58: int:i64 = iconst 0
// CHECK:     v59: int:i64 = iconst 8
// CHECK:     v60: ptr = ptradd v7, v59
// CHECK:     v61: mem = store.8 v58, v60, v57
// CHECK:     v62: int:i64 = load.8 v7, v61
// CHECK:     v63: int:i64 = iconst 8
// CHECK:     v64: ptr = ptradd v7, v63
// CHECK:     v65: int:i64 = load.8 v64, v61
// CHECK:     v66: bool = bconst false
// CHECK:     v67: ptr = symbol_addr @.Lloc.11
// CHECK:     v68: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking18panic_nounwind_fmt
// CHECK:     v69: mem = call v68(v62, v65, v66, v67), v61
// CHECK:     v70: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb10(v72: mem):
// CHECK:     ret v72
// CHECK:
// CHECK:   bb11(v74: mem):
// CHECK:     v75: int:u64 = iconst 1
// CHECK:     v76: int:u64 = iconst 0
// CHECK:     v77: int:u64 = select v22, v75, v76
// CHECK:     v78: int:i64 = iconst 255
// CHECK:     v79: int:u64 = and v77, v78
// CHECK:     v80: int:i8 = iconst 0
// CHECK:     v81: bool = icmp.eq v79, v80
// CHECK:     brif v81, bb14(v74), bb13(v74)
// CHECK:
// CHECK:   bb12(v83: mem):
// CHECK:     br bb7(v83)
// CHECK:
// CHECK:   bb13(v85: mem):
// CHECK:     br bb4(v85)
// CHECK:
// CHECK:   bb14(v87: mem):
// CHECK:     v88: int:u64 = ptrtoaddr v1
// CHECK:     v89: int:i64 = iconst 0
// CHECK:     v90: bool = icmp.eq v88, v89:u64
// CHECK:     v91: int:u64 = iconst 1
// CHECK:     v92: int:u64 = iconst 0
// CHECK:     v93: int:u64 = select v90, v91, v92
// CHECK:     v94: int:i64 = iconst 1
// CHECK:     v95: int:i64 = xor v93, v94
// CHECK:     v96: int:i64 = iconst 255
// CHECK:     v97: int:u64 = and v95, v96
// CHECK:     v98: int:i8 = iconst 0
// CHECK:     v99: bool = icmp.eq v97, v98
// CHECK:     brif v99, bb7(v87), bb4(v87)
// CHECK:
// CHECK:   bb15(v101: mem):
// CHECK:     v102: int:u64 = iconst 1
// CHECK:     v103: int:u64 = iconst 0
// CHECK:     v104: int:u64 = select v25, v102, v103
// CHECK:     v105: int:i64 = iconst 255
// CHECK:     v106: int:u64 = and v104, v105
// CHECK:     v107: int:i8 = iconst 0
// CHECK:     v108: bool = icmp.eq v106, v107
// CHECK:     brif v108, bb12(v101), bb11(v101)
// CHECK:
// CHECK:   bb16(v110: mem):
// CHECK:     v111: bool = load.1 v6, v110
// CHECK:     v112: int:u64 = iconst 1
// CHECK:     v113: int:u64 = iconst 0
// CHECK:     v114: int:u64 = select v111, v112, v113
// CHECK:     v115: int:i64 = iconst 255
// CHECK:     v116: int:u64 = and v114, v115
// CHECK:     v117: int:i8 = iconst 0
// CHECK:     v118: bool = icmp.eq v116, v117
// CHECK:     brif v118, bb19(v110), bb18(v110)
// CHECK:
// CHECK:   bb17(v120: mem):
// CHECK:     br bb6(v120)
// CHECK:
// CHECK:   bb18(v122: mem):
// CHECK:     br bb5(v122)
// CHECK:
// CHECK:   bb19(v124: mem):
// CHECK:     v125: int:u64 = ptrtoaddr v2
// CHECK:     v126: int:i64 = iconst 0
// CHECK:     v127: bool = icmp.eq v125, v126:u64
// CHECK:     v128: int:u64 = iconst 1
// CHECK:     v129: int:u64 = iconst 0
// CHECK:     v130: int:u64 = select v127, v128, v129
// CHECK:     v131: int:i64 = iconst 1
// CHECK:     v132: int:i64 = xor v130, v131
// CHECK:     v133: int:i64 = iconst 255
// CHECK:     v134: int:u64 = and v132, v133
// CHECK:     v135: int:i8 = iconst 0
// CHECK:     v136: bool = icmp.eq v134, v135
// CHECK:     brif v136, bb6(v124), bb5(v124)
// CHECK:
// CHECK:   bb20(v138: mem):
// CHECK:     v139: int:u64 = iconst 1
// CHECK:     v140: int:u64 = iconst 0
// CHECK:     v141: int:u64 = select v30, v139, v140
// CHECK:     v142: int:i64 = iconst 255
// CHECK:     v143: int:u64 = and v141, v142
// CHECK:     v144: int:i8 = iconst 0
// CHECK:     v145: bool = icmp.eq v143, v144
// CHECK:     brif v145, bb17(v138), bb16(v138)
// CHECK:
// CHECK:   bb21(v147: mem):
// CHECK:     v148: int:u64 = iconst 1
// CHECK:     v149: int:u64 = iconst 0
// CHECK:     v150: int:u64 = select v35, v148, v149
// CHECK:     v151: int:i64 = iconst 255
// CHECK:     v152: int:u64 = and v150, v151
// CHECK:     v153: int:i8 = iconst 0
// CHECK:     v154: bool = icmp.eq v152, v153
// CHECK:     brif v154, bb9(v147), bb10(v147)
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
// CHECK: data @.Lloc_file.14 = "$SYSROOT/library/core/src/ub_checks.rs"
// CHECK: data @.Lloc.15 = "..." relocs [0: @.Lloc_file.14]
// CHECK: func @_RNvNvNtCsa3SJzwB9S2T_4core3ptr4copy18precondition_checkCse33uD6zc4Cp_6memops(ptr, ptr, int:u64, bool) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: bool = param 3
// CHECK:     v5: ptr = stack_slot 8
// CHECK:     v6: ptr = stack_slot 8
// CHECK:     v7: ptr = stack_slot 1
// CHECK:     v8: ptr = stack_slot 16
// CHECK:     v9: ptr = stack_slot 16
// CHECK:     v10: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v11: mem, v12: bool = call v10(v1, v3), v0 -> bool
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
// CHECK:     v21: ptr = symbol_addr @.Lstr.12
// CHECK:     v22: int:i64 = iconst 221
// CHECK:     v23: mem = store.8 v21, v9, v20
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v9, v24
// CHECK:     v26: mem = store.8 v22, v25, v23
// CHECK:     v27: int:i64 = iconst 221
// CHECK:     v28: int:i64 = iconst 8
// CHECK:     v29: ptr = ptradd v9, v28
// CHECK:     v30: mem = store.8 v27, v29, v26
// CHECK:     v31: ptr = load.8 v9, v30
// CHECK:     v32: int:u64 = ptrtoaddr v31
// CHECK:     v33: ptr = symbol_addr @.Lstr.13
// CHECK:     v34: mem = store.8 v32, v8, v30
// CHECK:     v35: int:i64 = iconst 0
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v8, v36
// CHECK:     v38: mem = store.8 v35, v37, v34
// CHECK:     v39: int:i64 = load.8 v8, v38
// CHECK:     v40: int:i64 = iconst 8
// CHECK:     v41: ptr = ptradd v8, v40
// CHECK:     v42: int:i64 = load.8 v41, v38
// CHECK:     v43: bool = bconst false
// CHECK:     v44: ptr = symbol_addr @.Lloc.15
// CHECK:     v45: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking18panic_nounwind_fmt
// CHECK:     v46: mem = call v45(v39, v42, v43, v44), v38
// CHECK:     v47: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb5(v49: mem):
// CHECK:     v50: int:u64 = iconst 1
// CHECK:     v51: int:u64 = iconst 0
// CHECK:     v52: int:u64 = select v4, v50, v51
// CHECK:     v53: int:i64 = iconst 255
// CHECK:     v54: int:u64 = and v52, v53
// CHECK:     v55: int:i8 = iconst 0
// CHECK:     v56: bool = icmp.eq v54, v55
// CHECK:     brif v56, bb8(v49), bb7(v49)
// CHECK:
// CHECK:   bb6(v58: mem):
// CHECK:     br bb3(v58)
// CHECK:
// CHECK:   bb7(v60: mem):
// CHECK:     v61: mem = store.8 v2, v5, v60
// CHECK:     v62: mem = store.8 v3, v6, v61
// CHECK:     v63: ptr = load.8 v5, v62
// CHECK:     v64: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v65: mem, v66: bool = call v64(v63, v3), v62 -> bool
// CHECK:     v67: mem = store.1 v66, v7, v65
// CHECK:     br bb13(v67)
// CHECK:
// CHECK:   bb8(v69: mem):
// CHECK:     v70: int:u64 = ptrtoaddr v1
// CHECK:     v71: int:i64 = iconst 0
// CHECK:     v72: bool = icmp.eq v70, v71:u64
// CHECK:     v73: int:u64 = iconst 1
// CHECK:     v74: int:u64 = iconst 0
// CHECK:     v75: int:u64 = select v72, v73, v74
// CHECK:     v76: int:i64 = iconst 1
// CHECK:     v77: int:i64 = xor v75, v76
// CHECK:     v78: int:i64 = iconst 255
// CHECK:     v79: int:u64 = and v77, v78
// CHECK:     v80: int:i8 = iconst 0
// CHECK:     v81: bool = icmp.eq v79, v80
// CHECK:     brif v81, bb3(v69), bb14(v69)
// CHECK:
// CHECK:   bb9(v83: mem):
// CHECK:     v84: int:u64 = iconst 1
// CHECK:     v85: int:u64 = iconst 0
// CHECK:     v86: int:u64 = select v12, v84, v85
// CHECK:     v87: int:i64 = iconst 255
// CHECK:     v88: int:u64 = and v86, v87
// CHECK:     v89: int:i8 = iconst 0
// CHECK:     v90: bool = icmp.eq v88, v89
// CHECK:     brif v90, bb6(v83), bb5(v83)
// CHECK:
// CHECK:   bb10(v92: mem):
// CHECK:     br bb2(v92)
// CHECK:
// CHECK:   bb11(v94: mem):
// CHECK:     br bb1(v94)
// CHECK:
// CHECK:   bb12(v96: mem):
// CHECK:     v97: int:u64 = ptrtoaddr v2
// CHECK:     v98: int:i64 = iconst 0
// CHECK:     v99: bool = icmp.eq v97, v98:u64
// CHECK:     v100: int:u64 = iconst 1
// CHECK:     v101: int:u64 = iconst 0
// CHECK:     v102: int:u64 = select v99, v100, v101
// CHECK:     v103: int:i64 = iconst 1
// CHECK:     v104: int:i64 = xor v102, v103
// CHECK:     v105: int:i64 = iconst 255
// CHECK:     v106: int:u64 = and v104, v105
// CHECK:     v107: int:i8 = iconst 0
// CHECK:     v108: bool = icmp.eq v106, v107
// CHECK:     brif v108, bb2(v96), bb1(v96)
// CHECK:
// CHECK:   bb13(v110: mem):
// CHECK:     v111: bool = load.1 v7, v110
// CHECK:     v112: int:u64 = iconst 1
// CHECK:     v113: int:u64 = iconst 0
// CHECK:     v114: int:u64 = select v111, v112, v113
// CHECK:     v115: int:i64 = iconst 255
// CHECK:     v116: int:u64 = and v114, v115
// CHECK:     v117: int:i8 = iconst 0
// CHECK:     v118: bool = icmp.eq v116, v117
// CHECK:     brif v118, bb10(v110), bb11(v110)
// CHECK:
// CHECK:   bb14(v120: mem):
// CHECK:     v121: mem = store.8 v2, v5, v120
// CHECK:     v122: mem = store.8 v3, v6, v121
// CHECK:     v123: ptr = load.8 v5, v122
// CHECK:     v124: ptr = symbol_addr @_RNvMNtNtCsa3SJzwB9S2T_4core3ptr9const_ptrPu13is_aligned_toCse33uD6zc4Cp_6memops
// CHECK:     v125: mem, v126: bool = call v124(v123, v3), v122 -> bool
// CHECK:     v127: mem = store.1 v126, v7, v125
// CHECK:     br bb15(v127)
// CHECK:
// CHECK:   bb15(v129: mem):
// CHECK:     v130: bool = load.1 v7, v129
// CHECK:     v131: int:u64 = iconst 1
// CHECK:     v132: int:u64 = iconst 0
// CHECK:     v133: int:u64 = select v130, v131, v132
// CHECK:     v134: int:i64 = iconst 255
// CHECK:     v135: int:u64 = and v133, v134
// CHECK:     v136: int:i8 = iconst 0
// CHECK:     v137: bool = icmp.eq v135, v136
// CHECK:     brif v137, bb10(v129), bb12(v129)
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
// CHECK: func @_RNvNvNtCsa3SJzwB9S2T_4core9ub_checks23maybe_is_nonoverlapping7runtimeCse33uD6zc4Cp_6memops(ptr, ptr, int:u64, int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = stack_slot 8
// CHECK:     v6: ptr = stack_slot 16
// CHECK:     v7: int:u64 = ptrtoaddr v1
// CHECK:     v8: int:u64 = ptrtoaddr v2
// CHECK:     v9: int:u64, v10: bool = umul_overflow.64 v3, v4
// CHECK:     v11: int:u64 = iconst 1
// CHECK:     v12: int:u64 = iconst 0
// CHECK:     v13: int:u64 = select v10, v11, v12
// CHECK:     v14: int:i64 = iconst 255
// CHECK:     v15: int:u64 = and v13, v14
// CHECK:     v16: int:i8 = iconst 0
// CHECK:     v17: bool = icmp.eq v15, v16
// CHECK:     brif v17, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v19: mem):
// CHECK:     br bb2(v19)
// CHECK:
// CHECK:   bb2(v21: mem):
// CHECK:     v22: ptr = symbol_addr @.Lstr.16
// CHECK:     v23: int:i64 = iconst 61
// CHECK:     v24: ptr = symbol_addr @_RNvNtCsa3SJzwB9S2T_4core9panicking14panic_nounwind
// CHECK:     v25: mem = call v24(v22, v23), v21
// CHECK:     v26: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v28: mem):
// CHECK:     v29: int:i64 = iconst 0
// CHECK:     v30: mem = store.8 v29, v6, v28
// CHECK:     v31: int:i64 = iconst 8
// CHECK:     v32: ptr = ptradd v6, v31
// CHECK:     v33: mem = store.8 v29, v32, v30
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v6, v34
// CHECK:     v36: mem = store.8 v9, v35, v33
// CHECK:     v37: int:i64 = iconst 1
// CHECK:     v38: mem = store.8 v37, v6, v36
// CHECK:     v39: int:i64 = iconst 8
// CHECK:     v40: ptr = ptradd v6, v39
// CHECK:     v41: int:i64 = load.8 v40, v38
// CHECK:     v42: bool = icmp.lt v7, v8
// CHECK:     v43: int:u64 = iconst 1
// CHECK:     v44: int:u64 = iconst 0
// CHECK:     v45: int:u64 = select v42, v43, v44
// CHECK:     v46: int:i64 = iconst 255
// CHECK:     v47: int:u64 = and v45, v46
// CHECK:     v48: int:i8 = iconst 0
// CHECK:     v49: bool = icmp.eq v47, v48
// CHECK:     brif v49, bb5(v38), bb4(v38)
// CHECK:
// CHECK:   bb4(v51: mem):
// CHECK:     v52: int:i64 = sub v8, v7
// CHECK:     v53: int:u64 = zext v52, 64
// CHECK:     v54: mem = store.8 v53, v5, v51
// CHECK:     br bb6(v54)
// CHECK:
// CHECK:   bb5(v56: mem):
// CHECK:     v57: int:i64 = sub v7, v8
// CHECK:     v58: int:u64 = zext v57, 64
// CHECK:     v59: mem = store.8 v58, v5, v56
// CHECK:     br bb6(v59)
// CHECK:
// CHECK:   bb6(v61: mem):
// CHECK:     v62: int:u64 = load.8 v5, v61
// CHECK:     v63: bool = icmp.ge v62, v41:u64
// CHECK:     ret v63, v61
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
// CHECK: func @test_copy(ptr, ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:i64 = iconst 16
// CHECK:     v4: ptr = symbol_addr @_RINvNtCsa3SJzwB9S2T_4core3ptr4copyhECse33uD6zc4Cp_6memops
// CHECK:     v5: mem = call v4(v2, v1, v3), v0
// CHECK:     v6: int:i64 = iconst 0
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
// CHECK: func @test_copy_nonoverlapping(ptr, ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:i64 = iconst 16
// CHECK:     v4: ptr = symbol_addr @_RINvNtCsa3SJzwB9S2T_4core3ptr19copy_nonoverlappinghECse33uD6zc4Cp_6memops
// CHECK:     v5: mem = call v4(v2, v1, v3), v0
// CHECK:     v6: int:i64 = iconst 0
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
// CHECK: func @test_write_bytes(ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i8 = iconst 66
// CHECK:     v3: int:i64 = iconst 8
// CHECK:     v4: ptr = symbol_addr @_RINvNtCsa3SJzwB9S2T_4core3ptr11write_byteshECse33uD6zc4Cp_6memops
// CHECK:     v5: mem = call v4(v1, v2, v3), v0
// CHECK:     v6: int:i64 = iconst 0
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
