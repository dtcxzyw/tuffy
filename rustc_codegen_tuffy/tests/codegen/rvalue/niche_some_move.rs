// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn some_slice_then_unwrap(_1: *mut u64, _2: usize) -> &mut [u64] {
// CHECK:     debug ptr => _1;
// CHECK:     debug len => _2;
// CHECK:     let mut _0: &mut [u64];
// CHECK:     scope 1 {
// CHECK:         debug payload => _0;
// CHECK:         let _3: core::option::Option<&mut [u64]>;
// CHECK:         scope 2 {
// CHECK:             debug wrapped => _3;
// CHECK:             scope 3 {
// CHECK:                 debug value => _0;
// CHECK:             }
// CHECK:             scope 11 (inlined #[track_caller] core::hint::unreachable_unchecked) {
// CHECK:                 scope 12 (inlined core::ub_checks::check_language_ub) {
// CHECK:                     scope 13 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:     scope 4 (inlined #[track_caller] core::slice::from_raw_parts_mut::<'_, u64>) {
// CHECK:         let mut _4: *mut [u64];
// CHECK:         scope 5 (inlined core::ub_checks::check_language_ub) {
// CHECK:             scope 6 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:             }
// CHECK:         }
// CHECK:         scope 7 (inlined core::mem::size_of::<u64>) {
// CHECK:         }
// CHECK:         scope 8 (inlined core::mem::align_of::<u64>) {
// CHECK:         }
// CHECK:         scope 9 (inlined core::ptr::slice_from_raw_parts_mut::<u64>) {
// CHECK:             scope 10 (inlined core::ptr::from_raw_parts_mut::<[u64], u64>) {
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _4 = *mut [u64] from (copy _1, copy _2);
// CHECK:         _0 = &mut (*_4);
// CHECK:         _3 = core::option::Option::<&mut [u64]>::Some(copy _0);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @some_slice_then_unwrap(ptr, int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: ptr = stack_slot 16 align 8
// CHECK:     v5: mem = store.8 v1, v4, v0
// CHECK:     v6: int:i64 = iconst 8
// CHECK:     v7: ptr = ptradd v4, v6
// CHECK:     v8: mem = store.8 v2, v7, v5
// CHECK:     v9: int:i64 = iconst 8
// CHECK:     v10: ptr = ptradd v4, v9
// CHECK:     v11: mem = store.8 v2, v10, v8
// CHECK:     v12: int:i64 = iconst 8
// CHECK:     v13: ptr = ptradd v4, v12
// CHECK:     v14: int:i64 = load.8 v13, v11
// CHECK:     v15: ptr = load.8 v4, v11
// CHECK:     v16: mem = store.8 v15, v3, v11
// CHECK:     v17: int:i64 = iconst 8
// CHECK:     v18: ptr = ptradd v3, v17
// CHECK:     v19: mem = store.8 v14, v18, v16
// CHECK:     v20: ptr = load.8 v4, v19
// CHECK:     v21: int:i64 = iconst 8
// CHECK:     v22: ptr = ptradd v4, v21
// CHECK:     v23: int:i64 = load.8 v22, v19
// CHECK:     ret v20, v23, v19
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub unsafe fn some_slice_then_unwrap<'a>(ptr: *mut u64, len: usize) -> &'a mut [u64] {
    let payload = core::slice::from_raw_parts_mut(ptr, len);
    let wrapped = Some(payload);
    match wrapped {
        Some(value) => value,
        None => core::hint::unreachable_unchecked(),
    }
}
