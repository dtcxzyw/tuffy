// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn reborrow_raw_parts(_1: *mut u64, _2: usize) -> &mut [u64] {
// CHECK:     debug ptr => _1;
// CHECK:     debug len => _2;
// CHECK:     let mut _0: &mut [u64];
// CHECK:     let _3: *mut [u64];
// CHECK:     scope 1 {
// CHECK:         debug raw => _3;
// CHECK:     }
// CHECK:     scope 2 (inlined core::ptr::slice_from_raw_parts_mut::<u64>) {
// CHECK:         scope 3 (inlined core::ptr::from_raw_parts_mut::<[u64], u64>) {
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _3 = *mut [u64] from (copy _1, copy _2);
// CHECK:         _0 = &mut (*_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @reborrow_raw_parts(ptr, int:u64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:u64 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: mem = store.8 v1, v3, v0
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v3, v5
// CHECK:     v7: mem = store.8 v2, v6, v4
// CHECK:     v8: int:i64 = iconst 8
// CHECK:     v9: ptr = ptradd v3, v8
// CHECK:     v10: mem = store.8 v2, v9, v7
// CHECK:     v11: ptr = load.8 v3, v10
// CHECK:     v12: int:i64 = iconst 8
// CHECK:     v13: ptr = ptradd v3, v12
// CHECK:     v14: int:i64 = load.8 v13, v10
// CHECK:     ret v11, v14, v10
// CHECK: }
// CHECK:
// CHECK: fn slice_as_mut_ptr(_1: &mut [u64]) -> *mut u64 {
// CHECK:     debug slice => _1;
// CHECK:     let mut _0: *mut u64;
// CHECK:     scope 1 (inlined core::slice::<impl [u64]>::as_mut_ptr) {
// CHECK:         let mut _2: *mut [u64];
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _2 = &raw mut (*_1);
// CHECK:         _0 = copy _2 as *mut u64 (PtrToPtr);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @slice_as_mut_ptr(ptr, int:i64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i64 = param 1
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn slice_as_mut_ptr(slice: &mut [u64]) -> *mut u64 {
    slice.as_mut_ptr()
}

#[no_mangle]
pub unsafe fn reborrow_raw_parts<'a>(ptr: *mut u64, len: usize) -> &'a mut [u64] {
    let raw = core::ptr::slice_from_raw_parts_mut(ptr, len);
    &mut *raw
}
