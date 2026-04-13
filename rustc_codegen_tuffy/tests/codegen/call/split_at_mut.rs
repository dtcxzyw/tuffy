// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn core::slice::<impl [T]>::split_at_mut(_1: &mut [T], _2: usize) -> (&mut [T], &mut [T]) {
// CHECK:     debug self => _1;
// CHECK:     debug mid => _2;
// CHECK:     let mut _0: (&mut [T], &mut [T]);
// CHECK:     let mut _3: core::option::Option<(&mut [T], &mut [T])>;
// CHECK:     let _4: !;
// CHECK:     let mut _5: core::fmt::Arguments<'_>;
// CHECK:     let mut _9: &str;
// CHECK:     scope 1 {
// CHECK:         debug pair => _0;
// CHECK:     }
// CHECK:     scope 2 (inlined core::slice::<impl [T]>::split_at_mut_checked) {
// CHECK:         debug self => _1;
// CHECK:         debug mid => _2;
// CHECK:         let mut _6: bool;
// CHECK:         let mut _7: usize;
// CHECK:         let mut _8: (&mut [T], &mut [T]);
// CHECK:     }
// CHECK:     scope 3 (inlined core::fmt::Arguments::<'_>::from_str) {
// CHECK:         debug s => _9;
// CHECK:         let mut _10: core::ptr::NonNull<u8>;
// CHECK:         let mut _11: *const u8;
// CHECK:         let mut _12: core::ptr::NonNull<core::fmt::rt::Argument<'_>>;
// CHECK:         let mut _13: usize;
// CHECK:         let mut _14: usize;
// CHECK:         let mut _15: usize;
// CHECK:         scope 4 (inlined core::str::<impl str>::as_ptr) {
// CHECK:             debug self => _9;
// CHECK:             let mut _16: *const str;
// CHECK:         }
// CHECK:         scope 5 (inlined core::str::<impl str>::len) {
// CHECK:             debug self => _9;
// CHECK:             let _17: &[u8];
// CHECK:             scope 6 (inlined core::str::<impl str>::as_bytes) {
// CHECK:                 debug self => _9;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = PtrMetadata(copy _1);
// CHECK:         _6 = Le(copy _2, move _7);
// CHECK:         switchInt(move _6) -> [0: bb3, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = core::slice::<impl [T]>::split_at_mut_unchecked(move _1, move _2) -> [return: bb2, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _3 = core::option::Option::<(&mut [T], &mut [T])>::Some(move _8);
// CHECK:         StorageDead(_8);
// CHECK:         StorageDead(_6);
// CHECK:         _0 = move ((_3 as Some).0: (&mut [T], &mut [T]));
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_6);
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = const "mid > len";
// CHECK:         StorageLive(_10);
// CHECK:         StorageLive(_11);
// CHECK:         StorageLive(_16);
// CHECK:         _16 = &raw const (*_9);
// CHECK:         _11 = copy _16 as *const u8 (PtrToPtr);
// CHECK:         StorageDead(_16);
// CHECK:         _10 = copy _11 as core::ptr::NonNull<u8> (Transmute);
// CHECK:         StorageDead(_11);
// CHECK:         StorageLive(_12);
// CHECK:         StorageLive(_13);
// CHECK:         StorageLive(_14);
// CHECK:         StorageLive(_15);
// CHECK:         StorageLive(_17);
// CHECK:         _17 = const "mid > len" as &[u8] (Transmute);
// CHECK:         _15 = PtrMetadata(copy _17);
// CHECK:         StorageDead(_17);
// CHECK:         _14 = Shl(move _15, const 1_i32);
// CHECK:         StorageDead(_15);
// CHECK:         _13 = BitOr(move _14, const 1_usize);
// CHECK:         StorageDead(_14);
// CHECK:         _12 = move _13 as core::ptr::NonNull<core::fmt::rt::Argument<'_>> (Transmute);
// CHECK:         StorageDead(_13);
// CHECK:         _5 = core::fmt::Arguments::<'_> { template: move _10, args: move _12 };
// CHECK:         StorageDead(_12);
// CHECK:         StorageDead(_10);
// CHECK:         StorageDead(_9);
// CHECK:         _4 = core::panicking::panic_fmt(move _5) -> unwind continue;
// CHECK:     }
// CHECK: }
// CHECK:
// CHECK: alloc1 (size: 9, align: 1) {
// CHECK:     6d 69 64 20 3e 20 6c 65 6e                      │ mid > len
// CHECK: }
// CHECK: data @.Lstr.0 = "mid > len"
// CHECK: data @.Lloc_file.1 = "$SYSROOT/library/core/src/panic.rs"
// CHECK: data @.Lloc.2 = "..." relocs [0: @.Lloc_file.1]
// CHECK: func @_RNvMNtC$HASH_4core5sliceSy12split_at_mutC$HASH_12split_at_mut(ptr, ptr, int:i64, int:u64, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:i64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = param 4
// CHECK:     v6: ptr = stack_slot 32 align 8
// CHECK:     v7: ptr = stack_slot 16 align 8
// CHECK:     v8: bool = icmp.le v4, v3:u64
// CHECK:     v9: int:u64 = iconst 1
// CHECK:     v10: int:u64 = iconst 0
// CHECK:     v11: int:u64 = select v8, v9, v10
// CHECK:     v12: int:i64 = iconst 255
// CHECK:     v13: int:u64 = and v11, v12
// CHECK:     v14: int:i8 = iconst 0
// CHECK:     v15: bool = icmp.eq v13, v14
// CHECK:     brif v15, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:u64 = iconst 8
// CHECK:     v19: int:u64 = mul v4, v18
// CHECK:     v20: ptr = ptradd v2, v19
// CHECK:     v21: int:u64 = sub v3, v4
// CHECK:     v22: ptr = stack_slot 32 align 8
// CHECK:     v23: mem = store.8 v2, v22, v17
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v22, v24
// CHECK:     v26: mem = store.8 v4, v25, v23
// CHECK:     v27: int:i64 = iconst 16
// CHECK:     v28: ptr = ptradd v22, v27
// CHECK:     v29: mem = store.8 v20, v28, v26
// CHECK:     v30: int:i64 = iconst 24
// CHECK:     v31: ptr = ptradd v22, v30
// CHECK:     v32: mem = store.8 v21, v31, v29
// CHECK:     br bb2(v32)
// CHECK:
// CHECK:   bb2(v34: mem):
// CHECK:     v35: int:i64 = load.8 v22, v34
// CHECK:     v36: mem = store.8 v35, v6, v34
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v22, v37
// CHECK:     v39: int:i64 = load.8 v38, v36
// CHECK:     v40: int:i64 = iconst 8
// CHECK:     v41: ptr = ptradd v6, v40
// CHECK:     v42: mem = store.8 v39, v41, v36
// CHECK:     v43: int:i64 = iconst 16
// CHECK:     v44: ptr = ptradd v22, v43
// CHECK:     v45: int:i64 = load.8 v44, v42
// CHECK:     v46: int:i64 = iconst 16
// CHECK:     v47: ptr = ptradd v6, v46
// CHECK:     v48: mem = store.8 v45, v47, v42
// CHECK:     v49: int:i64 = iconst 24
// CHECK:     v50: ptr = ptradd v22, v49
// CHECK:     v51: int:i64 = load.8 v50, v48
// CHECK:     v52: int:i64 = iconst 24
// CHECK:     v53: ptr = ptradd v6, v52
// CHECK:     v54: mem = store.8 v51, v53, v48
// CHECK:     v55: int:i64 = load.8 v6, v54
// CHECK:     v56: mem = store.8 v55, v1, v54
// CHECK:     v57: int:i64 = iconst 8
// CHECK:     v58: ptr = ptradd v6, v57
// CHECK:     v59: int:i64 = load.8 v58, v56
// CHECK:     v60: int:i64 = iconst 8
// CHECK:     v61: ptr = ptradd v1, v60
// CHECK:     v62: mem = store.8 v59, v61, v56
// CHECK:     v63: int:i64 = iconst 16
// CHECK:     v64: ptr = ptradd v6, v63
// CHECK:     v65: int:i64 = load.8 v64, v62
// CHECK:     v66: int:i64 = iconst 16
// CHECK:     v67: ptr = ptradd v1, v66
// CHECK:     v68: mem = store.8 v65, v67, v62
// CHECK:     v69: int:i64 = iconst 24
// CHECK:     v70: ptr = ptradd v6, v69
// CHECK:     v71: int:i64 = load.8 v70, v68
// CHECK:     v72: int:i64 = iconst 24
// CHECK:     v73: ptr = ptradd v1, v72
// CHECK:     v74: mem = store.8 v71, v73, v68
// CHECK:     ret v1, v74
// CHECK:
// CHECK:   bb3(v76: mem):
// CHECK:     v77: ptr = symbol_addr @.Lstr.0
// CHECK:     v78: int:i64 = iconst 9
// CHECK:     v79: ptr = symbol_addr @.Lstr.0
// CHECK:     v80: int:i64 = iconst 9
// CHECK:     v81: int:i32 = iconst 1
// CHECK:     v82: int:i64 = iconst 63
// CHECK:     v83: int:i64 = and v81, v82
// CHECK:     v84: int:i64 = shl v80:u64, v83
// CHECK:     v85: int:u64 = zext v84, 64
// CHECK:     v86: int:i64 = iconst 1
// CHECK:     v87: int:i64 = or v85, v86:u64
// CHECK:     v88: int:u64 = zext v87, 64
// CHECK:     v89: mem = store.8 v77, v7, v76
// CHECK:     v90: int:i64 = iconst 8
// CHECK:     v91: ptr = ptradd v7, v90
// CHECK:     v92: mem = store.8 v88, v91, v89
// CHECK:     v93: int:i64 = load.8 v7, v92
// CHECK:     v94: int:i64 = iconst 8
// CHECK:     v95: ptr = ptradd v7, v94
// CHECK:     v96: int:i64 = load.8 v95, v92
// CHECK:     v97: ptr = symbol_addr @.Lloc.2
// CHECK:     v98: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking9panic_fmt
// CHECK:     v99: mem = call v98(v93, v96, v97), v92
// CHECK:     v100: int:i64 = iconst 0
// CHECK:     unreachable
// CHECK: }
// CHECK:
// CHECK: fn core::slice::<impl [T]>::split_at_mut_unchecked(_1: &mut [T], _2: usize) -> (&mut [T], &mut [T]) {
// CHECK:     debug self => _1;
// CHECK:     debug mid => _2;
// CHECK:     let mut _0: (&mut [T], &mut [T]);
// CHECK:     let _3: usize;
// CHECK:     let _5: ();
// CHECK:     let mut _6: &mut [T];
// CHECK:     let mut _7: &mut [T];
// CHECK:     let mut _8: *mut T;
// CHECK:     let mut _9: usize;
// CHECK:     scope 1 {
// CHECK:         debug len => _3;
// CHECK:         let _4: *mut T;
// CHECK:         scope 2 {
// CHECK:             debug ptr => _4;
// CHECK:             scope 4 (inlined #[track_caller] core::slice::from_raw_parts_mut::<'_, T>) {
// CHECK:                 debug data => _4;
// CHECK:                 debug len => _2;
// CHECK:                 let _11: ();
// CHECK:                 let mut _12: *mut ();
// CHECK:                 let mut _13: *mut [T];
// CHECK:                 scope 5 (inlined core::ub_checks::check_language_ub) {
// CHECK:                     scope 6 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 7 (inlined core::mem::size_of::<T>) {
// CHECK:                 }
// CHECK:                 scope 8 (inlined core::mem::align_of::<T>) {
// CHECK:                 }
// CHECK:                 scope 9 (inlined core::ptr::slice_from_raw_parts_mut::<T>) {
// CHECK:                     debug data => _4;
// CHECK:                     debug len => _2;
// CHECK:                     scope 10 (inlined core::ptr::from_raw_parts_mut::<[T], T>) {
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 11 (inlined #[track_caller] core::ptr::mut_ptr::<impl *mut T>::add) {
// CHECK:                 debug self => _4;
// CHECK:                 debug count => _2;
// CHECK:             }
// CHECK:             scope 12 (inlined #[track_caller] core::slice::from_raw_parts_mut::<'_, T>) {
// CHECK:                 debug data => _8;
// CHECK:                 debug len => _9;
// CHECK:                 let _14: ();
// CHECK:                 let mut _15: *mut ();
// CHECK:                 let mut _16: *mut [T];
// CHECK:                 scope 13 (inlined core::ub_checks::check_language_ub) {
// CHECK:                     scope 14 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:                     }
// CHECK:                 }
// CHECK:                 scope 15 (inlined core::mem::size_of::<T>) {
// CHECK:                 }
// CHECK:                 scope 16 (inlined core::mem::align_of::<T>) {
// CHECK:                 }
// CHECK:                 scope 17 (inlined core::ptr::slice_from_raw_parts_mut::<T>) {
// CHECK:                     debug data => _8;
// CHECK:                     debug len => _9;
// CHECK:                     scope 18 (inlined core::ptr::from_raw_parts_mut::<[T], T>) {
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:         scope 3 (inlined core::slice::<impl [T]>::as_mut_ptr) {
// CHECK:             debug self => _1;
// CHECK:             let mut _10: *mut [T];
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = PtrMetadata(copy _1);
// CHECK:         _10 = &raw mut (*_1);
// CHECK:         _4 = copy _10 as *mut T (PtrToPtr);
// CHECK:         switchInt(UbChecks) -> [0: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _5 = core::slice::<impl [T]>::split_at_mut_unchecked::precondition_check(copy _2, copy _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         switchInt(UbChecks) -> [0: bb5, otherwise: bb3];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageLive(_12);
// CHECK:         _12 = copy _10 as *mut () (PtrToPtr);
// CHECK:         _11 = core::slice::from_raw_parts_mut::precondition_check(move _12, const <T as core::mem::SizedTypeProperties>::SIZE, const <T as core::mem::SizedTypeProperties>::ALIGN, copy _2) -> [return: bb4, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         StorageDead(_12);
// CHECK:         goto -> bb5;
// CHECK:     }
// CHECK:
// CHECK:     bb5: {
// CHECK:         StorageLive(_13);
// CHECK:         _13 = *mut [T] from (copy _4, copy _2);
// CHECK:         _6 = &mut (*_13);
// CHECK:         StorageDead(_13);
// CHECK:         StorageLive(_8);
// CHECK:         _8 = Offset(copy _4, copy _2);
// CHECK:         StorageLive(_9);
// CHECK:         _9 = SubUnchecked(copy _3, copy _2);
// CHECK:         switchInt(UbChecks) -> [0: bb8, otherwise: bb6];
// CHECK:     }
// CHECK:
// CHECK:     bb6: {
// CHECK:         StorageLive(_15);
// CHECK:         _15 = copy _8 as *mut () (PtrToPtr);
// CHECK:         _14 = core::slice::from_raw_parts_mut::precondition_check(move _15, const <T as core::mem::SizedTypeProperties>::SIZE, const <T as core::mem::SizedTypeProperties>::ALIGN, copy _9) -> [return: bb7, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb7: {
// CHECK:         StorageDead(_15);
// CHECK:         goto -> bb8;
// CHECK:     }
// CHECK:
// CHECK:     bb8: {
// CHECK:         StorageLive(_16);
// CHECK:         _16 = *mut [T] from (copy _8, copy _9);
// CHECK:         _7 = &mut (*_16);
// CHECK:         StorageDead(_16);
// CHECK:         StorageDead(_9);
// CHECK:         StorageDead(_8);
// CHECK:         _0 = (copy _6, copy _7);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvMNtC$HASH_4core5sliceSy22split_at_mut_uncheckedC$HASH_12split_at_mut(ptr, ptr, int:i64, int:u64, ptr) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:i64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: ptr = param 4
// CHECK:     v6: int:i64 = iconst 0
// CHECK:     v7: int:i64 = iconst 0
// CHECK:     v8: bool = icmp.eq v6, v7
// CHECK:     brif v8, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     br bb2(v10)
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13: int:i64 = iconst 0
// CHECK:     v14: int:i64 = iconst 0
// CHECK:     v15: bool = icmp.eq v13, v14
// CHECK:     brif v15, bb5(v12), bb3(v12)
// CHECK:
// CHECK:   bb3(v17: mem):
// CHECK:     br bb4(v17)
// CHECK:
// CHECK:   bb4(v19: mem):
// CHECK:     br bb5(v19)
// CHECK:
// CHECK:   bb5(v21: mem):
// CHECK:     v22: int:u64 = ptrtoaddr v2
// CHECK:     v23: int:i64 = iconst 8
// CHECK:     v24: int:i64 = mul v4, v23
// CHECK:     v25: ptr = ptradd v2, v24
// CHECK:     v26: int:u64 = sub v3:u64, v4
// CHECK:     v27: int:i64 = iconst 0
// CHECK:     v28: int:i64 = iconst 0
// CHECK:     v29: bool = icmp.eq v27, v28
// CHECK:     brif v29, bb8(v21), bb6(v21)
// CHECK:
// CHECK:   bb6(v31: mem):
// CHECK:     br bb7(v31)
// CHECK:
// CHECK:   bb7(v33: mem):
// CHECK:     br bb8(v33)
// CHECK:
// CHECK:   bb8(v35: mem):
// CHECK:     v36: mem = store.8 v2, v1, v35
// CHECK:     v37: int:i64 = iconst 8
// CHECK:     v38: ptr = ptradd v1, v37
// CHECK:     v39: mem = store.8 v4, v38, v36
// CHECK:     v40: int:i64 = iconst 16
// CHECK:     v41: ptr = ptradd v1, v40
// CHECK:     v42: mem = store.8 v25, v41, v39
// CHECK:     v43: int:i64 = iconst 8
// CHECK:     v44: ptr = ptradd v41, v43
// CHECK:     v45: mem = store.8 v26, v44, v42
// CHECK:     ret v1, v45
// CHECK: }
// CHECK:
// CHECK: fn split_slice(_1: &mut [u64], _2: usize) -> (&mut [u64], &mut [u64]) {
// CHECK:     debug slice => _1;
// CHECK:     debug mid => _2;
// CHECK:     let mut _0: (&mut [u64], &mut [u64]);
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::slice::<impl [u64]>::split_at_mut(move _1, move _2) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: data @.Lloc_file.3 = "/tuffy/rustc_codegen_tuffy/tests/codegen/call/split_at_mut.rs"
// CHECK: data @.Lloc.4 = "..." relocs [0: @.Lloc_file.3]
// CHECK: func @split_slice(ptr, ptr, int:i64, int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:i64 = param 2
// CHECK:     v4: int:u64 = param 3
// CHECK:     v5: int:u64 = iconst 8
// CHECK:     v6: int:u64 = mul v4, v5
// CHECK:     v7: ptr = ptradd v2, v6
// CHECK:     v8: int:u64 = sub v3, v4
// CHECK:     v9: bool = icmp.le v4, v3
// CHECK:     brif v9, bb2(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     ret v1, v11
// CHECK:
// CHECK:   bb2(v13: mem):
// CHECK:     v14: mem = store.8 v2, v1, v13
// CHECK:     v15: int:i64 = iconst 8
// CHECK:     v16: ptr = ptradd v1, v15
// CHECK:     v17: mem = store.8 v4, v16, v14
// CHECK:     v18: int:i64 = iconst 16
// CHECK:     v19: ptr = ptradd v1, v18
// CHECK:     v20: mem = store.8 v7, v19, v17
// CHECK:     v21: int:i64 = iconst 24
// CHECK:     v22: ptr = ptradd v1, v21
// CHECK:     v23: mem = store.8 v8, v22, v20
// CHECK:     br bb1(v23)
// CHECK:
// CHECK:   bb3(v25: mem):
// CHECK:     v26: ptr = symbol_addr @.Lloc.4
// CHECK:     v27: ptr = symbol_addr @_RNvNtC$HASH_4core9panicking18panic_bounds_check
// CHECK:     v28: mem = call v27(v4, v3, v26), v25
// CHECK:     trap
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn split_slice(slice: &mut [u64], mid: usize) -> (&mut [u64], &mut [u64]) {
    slice.split_at_mut(mid)
}
