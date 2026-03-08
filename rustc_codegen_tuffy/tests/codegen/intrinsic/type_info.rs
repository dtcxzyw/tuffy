// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn align_of_u32() -> usize {
// CHECK:     let mut _0: usize;
// CHECK:     scope 1 (inlined core::mem::align_of::<u32>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const 4_usize;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @align_of_u32() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 4
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for align_of_u32, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @align_of_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn align_of_u64() -> usize {
// CHECK:     let mut _0: usize;
// CHECK:     scope 1 (inlined core::mem::align_of::<u64>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const 8_usize;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @align_of_u64() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 8
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for align_of_u64, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @align_of_u64] return type: Int type requires annotation
// CHECK:
// CHECK: fn size_of_u32() -> usize {
// CHECK:     let mut _0: usize;
// CHECK:     scope 1 (inlined core::mem::size_of::<u32>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const 4_usize;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @size_of_u32() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 4
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for size_of_u32, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @size_of_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn size_of_u64() -> usize {
// CHECK:     let mut _0: usize;
// CHECK:     scope 1 (inlined core::mem::size_of::<u64>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const 8_usize;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @size_of_u64() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 8
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for size_of_u64, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @size_of_u64] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

use core::mem::{size_of, align_of};

#[no_mangle]
pub fn size_of_u32() -> usize {
    size_of::<u32>()
}

#[no_mangle]
pub fn size_of_u64() -> usize {
    size_of::<u64>()
}

#[no_mangle]
pub fn align_of_u32() -> usize {
    align_of::<u32>()
}

#[no_mangle]
pub fn align_of_u64() -> usize {
    align_of::<u64>()
}
