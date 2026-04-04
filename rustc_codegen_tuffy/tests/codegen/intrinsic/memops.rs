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
// CHECK: func @_RINvNtC$HASH_4core3ptr11write_byteshEC$HASH_6memops(ptr, int:u8, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u8 = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: ptr = stack_slot 1 align 1
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
// CHECK: func @_RINvNtC$HASH_4core3ptr19copy_nonoverlappinghEC$HASH_6memops(ptr, ptr, int:u64) {
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
// CHECK: func @_RINvNtC$HASH_4core3ptr4copyhEC$HASH_6memops(ptr, ptr, int:u64) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: ptr = stack_slot 1 align 1
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
// CHECK: func @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops(ptr, int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: ptr = stack_slot 16 align 8
// CHECK:     v5: int:u64 = count_ones v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     v8: int:i64 = iconst 4294967295
// CHECK:     v9: int:u64 = and v5, v8
// CHECK:     v10: int:i32 = iconst 1
// CHECK:     v11: bool = icmp.eq v9, v10
// CHECK:     brif v11, bb3(v7), bb2(v7)
// CHECK:
// CHECK:   bb2(v13: mem):
// CHECK:     v14: ptr = symbol_addr @.Lstr.0
// CHECK:     v15: int:i64 = iconst 42
// CHECK:     v16: mem = store.8 v14, v4, v13
// CHECK:     v17: int:i64 = iconst 8
// CHECK:     v18: ptr = ptradd v4, v17
// CHECK:     v19: mem = store.8 v15, v18, v16
// CHECK:     v20: int:i64 = iconst 42
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v4, v21
// CHECK:     v23: mem = store.8 v20, v22, v19
// CHECK:     v24: ptr = load.8 v4, v23
// CHECK:     v25: int:i64 = iconst 8
// CHECK:     v26: ptr = ptradd v4, v25
// CHECK:     v27: int:i64 = load.8 v26, v23
// CHECK:     v28: ptr = stack_slot 16
// CHECK:     v29: mem = store.8 v24, v28, v23
// CHECK:     v30: int:i64 = iconst 8
// CHECK:     v31: ptr = ptradd v28, v30
// CHECK:     v32: mem = store.8 v27, v31, v29
// CHECK:     v33: int:i64 = iconst 8
// CHECK:     v34: ptr = ptradd v4, v33
// CHECK:     v35: int:i64 = load.8 v34, v32
// CHECK:     v36: int:i64 = iconst 8
// CHECK:     v37: ptr = ptradd v28, v36
// CHECK:     v38: mem = store.8 v35, v37, v32
// CHECK:     v39: ptr = load.8 v28, v38
// CHECK:     v40: ptr = symbol_addr @.Lstr.1
// CHECK:     v41: int:i64 = iconst 42
// CHECK:     v42: int:i32 = iconst 1
// CHECK:     v43: int:i64 = iconst 63
// CHECK:     v44: int:i64 = and v42, v43
// CHECK:     v45: int:i64 = shl v41:u64, v44
// CHECK:     v46: int:u64 = zext v45, 64
// CHECK:     v47: int:i64 = iconst 1
// CHECK:     v48: int:i64 = or v46, v47:u64
// CHECK:     v49: int:u64 = zext v48, 64
// CHECK:     v50: mem = store.8 v39, v3, v38
// CHECK:     v51: int:i64 = iconst 8
// CHECK:     v52: ptr = ptradd v3, v51
// CHECK:     v53: mem = store.8 v49, v52, v50
// CHECK:     v54: int:i64 = load.8 v3, v53
// CHECK:     v55: int:i64 = iconst 8
// CHECK:     v56: ptr = ptradd v3, v55
// CHECK:     v57: int:i64 = load.8 v56, v53
// CHECK:     v58: ptr = symbol_addr @.Lloc.3
// CHECK:     v59: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v60: mem = call v59(v54, v57, v58), v53
// CHECK:     v61: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v63: mem):
// CHECK:     v64: int:u64 = ptrtoaddr v1
// CHECK:     v65: int:i64 = iconst 1
// CHECK:     v66: int:i64 = sub v2, v65:u64
// CHECK:     v67: int:u64 = zext v66, 64
// CHECK:     v68: int:i64 = and v64, v67
// CHECK:     v69: int:u64 = zext v68, 64
// CHECK:     v70: int:i64 = iconst 0
// CHECK:     v71: bool = icmp.eq v69, v70:u64
// CHECK:     ret v71, v63
// CHECK: }
// CHECK:
// CHECK: fn std::intrinsics::cold_path() -> () {
// CHECK:     let mut _0: ();
// CHECK:
// CHECK:     bb0: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvNtC$HASH_4core10intrinsics9cold_pathC$HASH_6memops() {
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
// CHECK: func @_RNvNvNtC$HASH_4core3ptr11write_bytes18precondition_checkC$HASH_6memops(ptr, int:u64, bool, ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: bool = param 2
// CHECK:     v4: ptr = param 3
// CHECK:     v5: ptr = stack_slot 16 align 8
// CHECK:     v6: ptr = stack_slot 16 align 8
// CHECK:     v7: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v8: mem, v9: bool = call v7(v1, v2), v0 -> bool
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u64 = iconst 1
// CHECK:     v13: int:u64 = iconst 0
// CHECK:     v14: int:u64 = select v9, v12, v13
// CHECK:     v15: int:i64 = iconst 255
// CHECK:     v16: int:u64 = and v14, v15
// CHECK:     v17: int:i8 = iconst 0
// CHECK:     v18: bool = icmp.eq v16, v17
// CHECK:     brif v18, bb6(v11), bb2(v11)
// CHECK:
// CHECK:   bb2(v20: mem):
// CHECK:     v21: int:u64 = iconst 1
// CHECK:     v22: int:u64 = iconst 0
// CHECK:     v23: int:u64 = select v3, v21, v22
// CHECK:     v24: int:i64 = iconst 255
// CHECK:     v25: int:u64 = and v23, v24
// CHECK:     v26: int:i8 = iconst 0
// CHECK:     v27: bool = icmp.eq v25, v26
// CHECK:     brif v27, bb4(v20), bb3(v20)
// CHECK:
// CHECK:   bb3(v29: mem):
// CHECK:     br bb5(v29)
// CHECK:
// CHECK:   bb4(v31: mem):
// CHECK:     v32: int:u64 = ptrtoaddr v1
// CHECK:     v33: int:i64 = iconst 0
// CHECK:     v34: bool = icmp.eq v32, v33:u64
// CHECK:     v35: int:u64 = iconst 1
// CHECK:     v36: int:u64 = iconst 0
// CHECK:     v37: int:u64 = select v34, v35, v36
// CHECK:     v38: int:i64 = iconst 1
// CHECK:     v39: int:i64 = xor v37, v38
// CHECK:     v40: int:i64 = iconst 255
// CHECK:     v41: int:u64 = and v39, v40
// CHECK:     v42: int:i8 = iconst 0
// CHECK:     v43: bool = icmp.eq v41, v42
// CHECK:     brif v43, bb7(v31), bb5(v31)
// CHECK:
// CHECK:   bb5(v45: mem):
// CHECK:     ret v45
// CHECK:
// CHECK:   bb6(v47: mem):
// CHECK:     br bb7(v47)
// CHECK:
// CHECK:   bb7(v49: mem):
// CHECK:     v50: ptr = symbol_addr @.Lstr.4
// CHECK:     v51: int:i64 = iconst 228
// CHECK:     v52: mem = store.8 v50, v6, v49
// CHECK:     v53: int:i64 = iconst 8
// CHECK:     v54: ptr = ptradd v6, v53
// CHECK:     v55: mem = store.8 v51, v54, v52
// CHECK:     v56: int:i64 = iconst 228
// CHECK:     v57: int:i64 = iconst 8
// CHECK:     v58: ptr = ptradd v6, v57
// CHECK:     v59: mem = store.8 v56, v58, v55
// CHECK:     v60: ptr = load.8 v6, v59
// CHECK:     v61: int:i64 = iconst 8
// CHECK:     v62: ptr = ptradd v6, v61
// CHECK:     v63: int:i64 = load.8 v62, v59
// CHECK:     v64: ptr = stack_slot 16
// CHECK:     v65: mem = store.8 v60, v64, v59
// CHECK:     v66: int:i64 = iconst 8
// CHECK:     v67: ptr = ptradd v64, v66
// CHECK:     v68: mem = store.8 v63, v67, v65
// CHECK:     v69: int:i64 = iconst 8
// CHECK:     v70: ptr = ptradd v6, v69
// CHECK:     v71: int:i64 = load.8 v70, v68
// CHECK:     v72: int:i64 = iconst 8
// CHECK:     v73: ptr = ptradd v64, v72
// CHECK:     v74: mem = store.8 v71, v73, v68
// CHECK:     v75: ptr = load.8 v64, v74
// CHECK:     v76: ptr = symbol_addr @.Lstr.5
// CHECK:     v77: int:i64 = iconst 228
// CHECK:     v78: int:i32 = iconst 1
// CHECK:     v79: int:i64 = iconst 63
// CHECK:     v80: int:i64 = and v78, v79
// CHECK:     v81: int:i64 = shl v77:u64, v80
// CHECK:     v82: int:u64 = zext v81, 64
// CHECK:     v83: int:i64 = iconst 1
// CHECK:     v84: int:i64 = or v82, v83:u64
// CHECK:     v85: int:u64 = zext v84, 64
// CHECK:     v86: mem = store.8 v75, v5, v74
// CHECK:     v87: int:i64 = iconst 8
// CHECK:     v88: ptr = ptradd v5, v87
// CHECK:     v89: mem = store.8 v85, v88, v86
// CHECK:     v90: int:i64 = load.8 v5, v89
// CHECK:     v91: int:i64 = iconst 8
// CHECK:     v92: ptr = ptradd v5, v91
// CHECK:     v93: int:i64 = load.8 v92, v89
// CHECK:     v94: bool = bconst false
// CHECK:     v95: ptr = symbol_addr @.Lloc.7
// CHECK:     v96: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking18panic_nounwind_fmt
// CHECK:     v97: mem = call v96(v90, v93, v94, v95), v89
// CHECK:     v98: int:i64 = iconst 0
// CHECK:     unreachable
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
// CHECK: func @_RNvNvNtC$HASH_4core3ptr19copy_nonoverlapping18precondition_checkC$HASH_6memops(ptr, ptr, int:u64, int:u64, int:u64, ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: int:u64 = param 4
// CHECK:     v6: ptr = param 5
// CHECK:     v7: ptr = stack_slot 1 align 1
// CHECK:     v8: ptr = stack_slot 16 align 8
// CHECK:     v9: ptr = stack_slot 16 align 8
// CHECK:     v10: int:i64 = iconst 0
// CHECK:     v11: bool = icmp.eq v5, v10
// CHECK:     brif v11, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v13: mem):
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: bool = icmp.eq v3, v14:u64
// CHECK:     v16: mem = store.1 v15, v7, v13
// CHECK:     br bb3(v16)
// CHECK:
// CHECK:   bb2(v18: mem):
// CHECK:     v19: bool = bconst true
// CHECK:     v20: mem = store.1 v19, v7, v18
// CHECK:     br bb3(v20)
// CHECK:
// CHECK:   bb3(v22: mem):
// CHECK:     v23: bool = load.1 v7, v22
// CHECK:     v24: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v25: mem, v26: bool = call v24(v1, v4), v22 -> bool
// CHECK:     br bb4(v25)
// CHECK:
// CHECK:   bb4(v28: mem):
// CHECK:     v29: int:u64 = iconst 1
// CHECK:     v30: int:u64 = iconst 0
// CHECK:     v31: int:u64 = select v26, v29, v30
// CHECK:     v32: int:i64 = iconst 255
// CHECK:     v33: int:u64 = and v31, v32
// CHECK:     v34: int:i8 = iconst 0
// CHECK:     v35: bool = icmp.eq v33, v34
// CHECK:     brif v35, bb18(v28), bb5(v28)
// CHECK:
// CHECK:   bb5(v37: mem):
// CHECK:     v38: int:u64 = iconst 1
// CHECK:     v39: int:u64 = iconst 0
// CHECK:     v40: int:u64 = select v23, v38, v39
// CHECK:     v41: int:i64 = iconst 255
// CHECK:     v42: int:u64 = and v40, v41
// CHECK:     v43: int:i8 = iconst 0
// CHECK:     v44: bool = icmp.eq v42, v43
// CHECK:     brif v44, bb7(v37), bb6(v37)
// CHECK:
// CHECK:   bb6(v46: mem):
// CHECK:     br bb8(v46)
// CHECK:
// CHECK:   bb7(v48: mem):
// CHECK:     v49: int:u64 = ptrtoaddr v1
// CHECK:     v50: int:i64 = iconst 0
// CHECK:     v51: bool = icmp.eq v49, v50:u64
// CHECK:     v52: int:u64 = iconst 1
// CHECK:     v53: int:u64 = iconst 0
// CHECK:     v54: int:u64 = select v51, v52, v53
// CHECK:     v55: int:i64 = iconst 1
// CHECK:     v56: int:i64 = xor v54, v55
// CHECK:     v57: int:i64 = iconst 255
// CHECK:     v58: int:u64 = and v56, v57
// CHECK:     v59: int:i8 = iconst 0
// CHECK:     v60: bool = icmp.eq v58, v59
// CHECK:     brif v60, bb19(v48), bb8(v48)
// CHECK:
// CHECK:   bb8(v62: mem):
// CHECK:     v63: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v64: mem, v65: bool = call v63(v2, v4), v62 -> bool
// CHECK:     br bb9(v64)
// CHECK:
// CHECK:   bb9(v67: mem):
// CHECK:     v68: int:u64 = iconst 1
// CHECK:     v69: int:u64 = iconst 0
// CHECK:     v70: int:u64 = select v65, v68, v69
// CHECK:     v71: int:i64 = iconst 255
// CHECK:     v72: int:u64 = and v70, v71
// CHECK:     v73: int:i8 = iconst 0
// CHECK:     v74: bool = icmp.eq v72, v73
// CHECK:     brif v74, bb16(v67), bb10(v67)
// CHECK:
// CHECK:   bb10(v76: mem):
// CHECK:     v77: bool = load.1 v7, v76
// CHECK:     v78: int:u64 = iconst 1
// CHECK:     v79: int:u64 = iconst 0
// CHECK:     v80: int:u64 = select v77, v78, v79
// CHECK:     v81: int:i64 = iconst 255
// CHECK:     v82: int:u64 = and v80, v81
// CHECK:     v83: int:i8 = iconst 0
// CHECK:     v84: bool = icmp.eq v82, v83
// CHECK:     brif v84, bb12(v76), bb11(v76)
// CHECK:
// CHECK:   bb11(v86: mem):
// CHECK:     br bb13(v86)
// CHECK:
// CHECK:   bb12(v88: mem):
// CHECK:     v89: int:u64 = ptrtoaddr v2
// CHECK:     v90: int:i64 = iconst 0
// CHECK:     v91: bool = icmp.eq v89, v90:u64
// CHECK:     v92: int:u64 = iconst 1
// CHECK:     v93: int:u64 = iconst 0
// CHECK:     v94: int:u64 = select v91, v92, v93
// CHECK:     v95: int:i64 = iconst 1
// CHECK:     v96: int:i64 = xor v94, v95
// CHECK:     v97: int:i64 = iconst 255
// CHECK:     v98: int:u64 = and v96, v97
// CHECK:     v99: int:i8 = iconst 0
// CHECK:     v100: bool = icmp.eq v98, v99
// CHECK:     brif v100, bb17(v88), bb13(v88)
// CHECK:
// CHECK:   bb13(v102: mem):
// CHECK:     v103: ptr = symbol_addr @_RNvNvNtC$HASH_4core9ub_checks23maybe_is_nonoverlapping7runtimeC$HASH_6memops
// CHECK:     v104: mem, v105: bool = call v103(v1, v2, v3, v5), v102 -> bool
// CHECK:     br bb14(v104)
// CHECK:
// CHECK:   bb14(v107: mem):
// CHECK:     v108: int:u64 = iconst 1
// CHECK:     v109: int:u64 = iconst 0
// CHECK:     v110: int:u64 = select v105, v108, v109
// CHECK:     v111: int:i64 = iconst 255
// CHECK:     v112: int:u64 = and v110, v111
// CHECK:     v113: int:i8 = iconst 0
// CHECK:     v114: bool = icmp.eq v112, v113
// CHECK:     brif v114, bb21(v107), bb15(v107)
// CHECK:
// CHECK:   bb15(v116: mem):
// CHECK:     ret v116
// CHECK:
// CHECK:   bb16(v118: mem):
// CHECK:     br bb17(v118)
// CHECK:
// CHECK:   bb17(v120: mem):
// CHECK:     br bb20(v120)
// CHECK:
// CHECK:   bb18(v122: mem):
// CHECK:     br bb19(v122)
// CHECK:
// CHECK:   bb19(v124: mem):
// CHECK:     br bb20(v124)
// CHECK:
// CHECK:   bb20(v126: mem):
// CHECK:     br bb21(v126)
// CHECK:
// CHECK:   bb21(v128: mem):
// CHECK:     v129: ptr = symbol_addr @.Lstr.8
// CHECK:     v130: int:i64 = iconst 283
// CHECK:     v131: mem = store.8 v129, v9, v128
// CHECK:     v132: int:i64 = iconst 8
// CHECK:     v133: ptr = ptradd v9, v132
// CHECK:     v134: mem = store.8 v130, v133, v131
// CHECK:     v135: int:i64 = iconst 283
// CHECK:     v136: int:i64 = iconst 8
// CHECK:     v137: ptr = ptradd v9, v136
// CHECK:     v138: mem = store.8 v135, v137, v134
// CHECK:     v139: ptr = load.8 v9, v138
// CHECK:     v140: int:i64 = iconst 8
// CHECK:     v141: ptr = ptradd v9, v140
// CHECK:     v142: int:i64 = load.8 v141, v138
// CHECK:     v143: ptr = stack_slot 16
// CHECK:     v144: mem = store.8 v139, v143, v138
// CHECK:     v145: int:i64 = iconst 8
// CHECK:     v146: ptr = ptradd v143, v145
// CHECK:     v147: mem = store.8 v142, v146, v144
// CHECK:     v148: int:i64 = iconst 8
// CHECK:     v149: ptr = ptradd v9, v148
// CHECK:     v150: int:i64 = load.8 v149, v147
// CHECK:     v151: int:i64 = iconst 8
// CHECK:     v152: ptr = ptradd v143, v151
// CHECK:     v153: mem = store.8 v150, v152, v147
// CHECK:     v154: ptr = load.8 v143, v153
// CHECK:     v155: ptr = symbol_addr @.Lstr.9
// CHECK:     v156: int:i64 = iconst 283
// CHECK:     v157: int:i32 = iconst 1
// CHECK:     v158: int:i64 = iconst 63
// CHECK:     v159: int:i64 = and v157, v158
// CHECK:     v160: int:i64 = shl v156:u64, v159
// CHECK:     v161: int:u64 = zext v160, 64
// CHECK:     v162: int:i64 = iconst 1
// CHECK:     v163: int:i64 = or v161, v162:u64
// CHECK:     v164: int:u64 = zext v163, 64
// CHECK:     v165: mem = store.8 v154, v8, v153
// CHECK:     v166: int:i64 = iconst 8
// CHECK:     v167: ptr = ptradd v8, v166
// CHECK:     v168: mem = store.8 v164, v167, v165
// CHECK:     v169: int:i64 = load.8 v8, v168
// CHECK:     v170: int:i64 = iconst 8
// CHECK:     v171: ptr = ptradd v8, v170
// CHECK:     v172: int:i64 = load.8 v171, v168
// CHECK:     v173: bool = bconst false
// CHECK:     v174: ptr = symbol_addr @.Lloc.11
// CHECK:     v175: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking18panic_nounwind_fmt
// CHECK:     v176: mem = call v175(v169, v172, v173, v174), v168
// CHECK:     v177: int:i64 = iconst 0
// CHECK:     unreachable
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
// CHECK: func @_RNvNvNtC$HASH_4core3ptr4copy18precondition_checkC$HASH_6memops(ptr, ptr, int:u64, bool, ptr) {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: bool = param 3
// CHECK:     v5: ptr = param 4
// CHECK:     v6: ptr = stack_slot 8 align 8
// CHECK:     v7: ptr = stack_slot 8 align 8
// CHECK:     v8: ptr = stack_slot 1 align 1
// CHECK:     v9: ptr = stack_slot 16 align 8
// CHECK:     v10: ptr = stack_slot 16 align 8
// CHECK:     v11: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v12: mem, v13: bool = call v11(v1, v3), v0 -> bool
// CHECK:     br bb1(v12)
// CHECK:
// CHECK:   bb1(v15: mem):
// CHECK:     v16: int:u64 = iconst 1
// CHECK:     v17: int:u64 = iconst 0
// CHECK:     v18: int:u64 = select v13, v16, v17
// CHECK:     v19: int:i64 = iconst 255
// CHECK:     v20: int:u64 = and v18, v19
// CHECK:     v21: int:i8 = iconst 0
// CHECK:     v22: bool = icmp.eq v20, v21
// CHECK:     brif v22, bb13(v15), bb2(v15)
// CHECK:
// CHECK:   bb2(v24: mem):
// CHECK:     v25: int:u64 = iconst 1
// CHECK:     v26: int:u64 = iconst 0
// CHECK:     v27: int:u64 = select v4, v25, v26
// CHECK:     v28: int:i64 = iconst 255
// CHECK:     v29: int:u64 = and v27, v28
// CHECK:     v30: int:i8 = iconst 0
// CHECK:     v31: bool = icmp.eq v29, v30
// CHECK:     brif v31, bb6(v24), bb3(v24)
// CHECK:
// CHECK:   bb3(v33: mem):
// CHECK:     v34: mem = store.8 v2, v6, v33
// CHECK:     v35: mem = store.8 v3, v7, v34
// CHECK:     v36: ptr = load.8 v6, v35
// CHECK:     v37: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v38: mem, v39: bool = call v37(v36, v3), v35 -> bool
// CHECK:     v40: mem = store.1 v39, v8, v38
// CHECK:     br bb4(v40)
// CHECK:
// CHECK:   bb4(v42: mem):
// CHECK:     v43: bool = load.1 v8, v42
// CHECK:     v44: int:u64 = iconst 1
// CHECK:     v45: int:u64 = iconst 0
// CHECK:     v46: int:u64 = select v43, v44, v45
// CHECK:     v47: int:i64 = iconst 255
// CHECK:     v48: int:u64 = and v46, v47
// CHECK:     v49: int:i8 = iconst 0
// CHECK:     v50: bool = icmp.eq v48, v49
// CHECK:     brif v50, bb11(v42), bb5(v42)
// CHECK:
// CHECK:   bb5(v52: mem):
// CHECK:     br bb10(v52)
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
// CHECK:     brif v66, bb14(v54), bb7(v54)
// CHECK:
// CHECK:   bb7(v68: mem):
// CHECK:     v69: mem = store.8 v2, v6, v68
// CHECK:     v70: mem = store.8 v3, v7, v69
// CHECK:     v71: ptr = load.8 v6, v70
// CHECK:     v72: ptr = symbol_addr @_RNvMNtNtC$HASH_4core3ptr9const_ptrPu13is_aligned_toC$HASH_6memops
// CHECK:     v73: mem, v74: bool = call v72(v71, v3), v70 -> bool
// CHECK:     v75: mem = store.1 v74, v8, v73
// CHECK:     br bb8(v75)
// CHECK:
// CHECK:   bb8(v77: mem):
// CHECK:     v78: bool = load.1 v8, v77
// CHECK:     v79: int:u64 = iconst 1
// CHECK:     v80: int:u64 = iconst 0
// CHECK:     v81: int:u64 = select v78, v79, v80
// CHECK:     v82: int:i64 = iconst 255
// CHECK:     v83: int:u64 = and v81, v82
// CHECK:     v84: int:i8 = iconst 0
// CHECK:     v85: bool = icmp.eq v83, v84
// CHECK:     brif v85, bb11(v77), bb9(v77)
// CHECK:
// CHECK:   bb9(v87: mem):
// CHECK:     v88: int:u64 = ptrtoaddr v2
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
// CHECK:     brif v99, bb12(v87), bb10(v87)
// CHECK:
// CHECK:   bb10(v101: mem):
// CHECK:     ret v101
// CHECK:
// CHECK:   bb11(v103: mem):
// CHECK:     br bb12(v103)
// CHECK:
// CHECK:   bb12(v105: mem):
// CHECK:     br bb15(v105)
// CHECK:
// CHECK:   bb13(v107: mem):
// CHECK:     br bb14(v107)
// CHECK:
// CHECK:   bb14(v109: mem):
// CHECK:     br bb15(v109)
// CHECK:
// CHECK:   bb15(v111: mem):
// CHECK:     v112: ptr = symbol_addr @.Lstr.12
// CHECK:     v113: int:i64 = iconst 221
// CHECK:     v114: mem = store.8 v112, v10, v111
// CHECK:     v115: int:i64 = iconst 8
// CHECK:     v116: ptr = ptradd v10, v115
// CHECK:     v117: mem = store.8 v113, v116, v114
// CHECK:     v118: int:i64 = iconst 221
// CHECK:     v119: int:i64 = iconst 8
// CHECK:     v120: ptr = ptradd v10, v119
// CHECK:     v121: mem = store.8 v118, v120, v117
// CHECK:     v122: ptr = load.8 v10, v121
// CHECK:     v123: int:i64 = iconst 8
// CHECK:     v124: ptr = ptradd v10, v123
// CHECK:     v125: int:i64 = load.8 v124, v121
// CHECK:     v126: ptr = stack_slot 16
// CHECK:     v127: mem = store.8 v122, v126, v121
// CHECK:     v128: int:i64 = iconst 8
// CHECK:     v129: ptr = ptradd v126, v128
// CHECK:     v130: mem = store.8 v125, v129, v127
// CHECK:     v131: int:i64 = iconst 8
// CHECK:     v132: ptr = ptradd v10, v131
// CHECK:     v133: int:i64 = load.8 v132, v130
// CHECK:     v134: int:i64 = iconst 8
// CHECK:     v135: ptr = ptradd v126, v134
// CHECK:     v136: mem = store.8 v133, v135, v130
// CHECK:     v137: ptr = load.8 v126, v136
// CHECK:     v138: ptr = symbol_addr @.Lstr.13
// CHECK:     v139: int:i64 = iconst 221
// CHECK:     v140: int:i32 = iconst 1
// CHECK:     v141: int:i64 = iconst 63
// CHECK:     v142: int:i64 = and v140, v141
// CHECK:     v143: int:i64 = shl v139:u64, v142
// CHECK:     v144: int:u64 = zext v143, 64
// CHECK:     v145: int:i64 = iconst 1
// CHECK:     v146: int:i64 = or v144, v145:u64
// CHECK:     v147: int:u64 = zext v146, 64
// CHECK:     v148: mem = store.8 v137, v9, v136
// CHECK:     v149: int:i64 = iconst 8
// CHECK:     v150: ptr = ptradd v9, v149
// CHECK:     v151: mem = store.8 v147, v150, v148
// CHECK:     v152: int:i64 = load.8 v9, v151
// CHECK:     v153: int:i64 = iconst 8
// CHECK:     v154: ptr = ptradd v9, v153
// CHECK:     v155: int:i64 = load.8 v154, v151
// CHECK:     v156: bool = bconst false
// CHECK:     v157: ptr = symbol_addr @.Lloc.15
// CHECK:     v158: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking18panic_nounwind_fmt
// CHECK:     v159: mem = call v158(v152, v155, v156, v157), v151
// CHECK:     v160: int:i64 = iconst 0
// CHECK:     unreachable
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
// CHECK: func @_RNvNvNtC$HASH_4core9ub_checks23maybe_is_nonoverlapping7runtimeC$HASH_6memops(ptr, ptr, int:u64, int:u64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:u64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = stack_slot 8 align 8
// CHECK:     v6: ptr = stack_slot 16 align 8
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
// CHECK:     v20: ptr = symbol_addr @_RNvNtC$HASH_4core10intrinsics9cold_pathC$HASH_6memops
// CHECK:     v21: mem = call v20(), v19
// CHECK:     v22: int:i64 = iconst 0
// CHECK:     br bb2(v21)
// CHECK:
// CHECK:   bb2(v24: mem):
// CHECK:     v25: ptr = symbol_addr @.Lstr.16
// CHECK:     v26: int:i64 = iconst 61
// CHECK:     v27: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking14panic_nounwind
// CHECK:     v28: mem = call v27(v25, v26), v24
// CHECK:     v29: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK:
// CHECK:   bb3(v31: mem):
// CHECK:     v32: int:i64 = iconst 0
// CHECK:     v33: mem = store.8 v32, v6, v31
// CHECK:     v34: int:i64 = iconst 8
// CHECK:     v35: ptr = ptradd v6, v34
// CHECK:     v36: mem = store.8 v32, v35, v33
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v6, v37
// CHECK:     v39: mem = store.8 v9, v38, v36
// CHECK:     v40: int:i64 = iconst 1
// CHECK:     v41: mem = store.8 v40, v6, v39
// CHECK:     v42: int:i64 = iconst 8
// CHECK:     v43: ptr = ptradd v6, v42
// CHECK:     v44: int:i64 = load.8 v43, v41
// CHECK:     v45: bool = icmp.lt v7, v8
// CHECK:     v46: int:u64 = iconst 1
// CHECK:     v47: int:u64 = iconst 0
// CHECK:     v48: int:u64 = select v45, v46, v47
// CHECK:     v49: int:i64 = iconst 255
// CHECK:     v50: int:u64 = and v48, v49
// CHECK:     v51: int:i8 = iconst 0
// CHECK:     v52: bool = icmp.eq v50, v51
// CHECK:     brif v52, bb5(v41), bb4(v41)
// CHECK:
// CHECK:   bb4(v54: mem):
// CHECK:     v55: int:i64 = sub v8, v7
// CHECK:     v56: int:u64 = zext v55, 64
// CHECK:     v57: mem = store.8 v56, v5, v54
// CHECK:     br bb6(v57)
// CHECK:
// CHECK:   bb5(v59: mem):
// CHECK:     v60: int:i64 = sub v7, v8
// CHECK:     v61: int:u64 = zext v60, 64
// CHECK:     v62: mem = store.8 v61, v5, v59
// CHECK:     br bb6(v62)
// CHECK:
// CHECK:   bb6(v64: mem):
// CHECK:     v65: int:u64 = load.8 v5, v64
// CHECK:     v66: bool = icmp.ge v65, v44:u64
// CHECK:     ret v66, v64
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
// CHECK:     v4: ptr = symbol_addr @_RINvNtC$HASH_4core3ptr4copyhEC$HASH_6memops
// CHECK:     v5: mem = call v4(v2, v1, v3:u64), v0
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
// CHECK:     v4: ptr = symbol_addr @_RINvNtC$HASH_4core3ptr19copy_nonoverlappinghEC$HASH_6memops
// CHECK:     v5: mem = call v4(v2, v1, v3:u64), v0
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
// CHECK:     v4: ptr = symbol_addr @_RINvNtC$HASH_4core3ptr11write_byteshEC$HASH_6memops
// CHECK:     v5: mem = call v4(v1, v2:u8, v3:u64), v0
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
