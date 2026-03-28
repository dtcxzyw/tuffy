// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn arith_offset_u32(_1: *const u32, _2: isize) -> *const u32 {
// CHECK:     debug ptr => _1;
// CHECK:     debug offset => _2;
// CHECK:     let mut _0: *const u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::arith_offset::<u32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @arith_offset_u32(ptr, int:s64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: int:s64 = param 1
// CHECK:     v3: int:i64 = iconst 4
// CHECK:     v4: int:u64 = mul v2, v3
// CHECK:     v5: ptr = ptradd v1, v4
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:
// CHECK: fn ptr_offset_from_u32(_1: *const u32, _2: *const u32) -> usize {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: usize;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::ptr_offset_from_unsigned::<u32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ptr_offset_from_u32(ptr, ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = param 1
// CHECK:     v3: int:s64 = ptrdiff v1, v2
// CHECK:     v4: int:i64 = iconst 4
// CHECK:     v5: int:u64 = div v3, v4
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::{arith_offset, ptr_offset_from_unsigned};

#[no_mangle]
pub unsafe fn arith_offset_u32(ptr: *const u32, offset: isize) -> *const u32 {
    arith_offset(ptr, offset)
}

#[no_mangle]
pub unsafe fn ptr_offset_from_u32(a: *const u32, b: *const u32) -> usize {
    ptr_offset_from_unsigned(a, b)
}
