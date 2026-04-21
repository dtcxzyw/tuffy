// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn slice_metadata(_1: *const [u8]) -> usize {
// CHECK:     debug ptr => _1;
// CHECK:     let mut _0: usize;
// CHECK:     scope 1 (inlined core::ptr::metadata::<[u8]>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = PtrMetadata(copy _1);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @slice_metadata(ptr, int:i64) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:i64 = param 1
// CHECK:     ret v2, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(ptr_metadata)]

#[no_mangle]
pub fn slice_metadata(ptr: *const [u8]) -> usize {
    core::ptr::metadata(ptr)
}
