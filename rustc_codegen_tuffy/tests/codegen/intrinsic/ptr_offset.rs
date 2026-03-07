// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn ptr_offset_array(_1: *const [i32; 4], _2: isize) -> *const [i32; 4] {
// CHECK:     debug ptr => _1;
// CHECK:     debug count => _2;
// CHECK:     let mut _0: *const [i32; 4];
// CHECK:     scope 1 (inlined std::ptr::const_ptr::<impl *const [i32; 4]>::wrapping_offset) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = std::intrinsics::arith_offset::<[i32; 4]>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ptr_offset_array(%ptr: ptr, %count: int:s64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:s64 = param %count
// CHECK:     v3: int = iconst 16
// CHECK:     v4: int = mul v2, v3
// CHECK:     v5: ptr = ptradd v1, v4
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:
// CHECK: fn ptr_offset_u64(_1: *const u64, _2: isize) -> *const u64 {
// CHECK:     debug ptr => _1;
// CHECK:     debug count => _2;
// CHECK:     let mut _0: *const u64;
// CHECK:     scope 1 (inlined std::ptr::const_ptr::<impl *const u64>::wrapping_offset) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = std::intrinsics::arith_offset::<u64>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ptr_offset_u64(%ptr: ptr, %count: int:s64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:s64 = param %count
// CHECK:     v3: int = iconst 8
// CHECK:     v4: int = mul v2, v3
// CHECK:     v5: ptr = ptradd v1, v4
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:
// CHECK: fn ptr_wrapping_offset(_1: *const i32, _2: isize) -> *const i32 {
// CHECK:     debug ptr => _1;
// CHECK:     debug count => _2;
// CHECK:     let mut _0: *const i32;
// CHECK:     scope 1 (inlined std::ptr::const_ptr::<impl *const i32>::wrapping_offset) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = std::intrinsics::arith_offset::<i32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ptr_wrapping_offset(%ptr: ptr, %count: int:s64) -> ptr {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param %ptr
// CHECK:     v2: int:s64 = param %count
// CHECK:     v3: int = iconst 4
// CHECK:     v4: int = mul v2, v3
// CHECK:     v5: ptr = ptradd v1, v4
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     ret v5, v7
// CHECK: }
// CHECK:

#[no_mangle]
pub unsafe fn ptr_wrapping_offset(ptr: *const i32, count: isize) -> *const i32 {
    // BinOp::Offset should use ptradd to preserve provenance
    // Currently uses integer add which loses provenance
    ptr.wrapping_offset(count)
}

#[no_mangle]
pub unsafe fn ptr_offset_u64(ptr: *const u64, count: isize) -> *const u64 {
    // Should emit: ptradd ptr, (count * 8)
    // Currently emits: add (ptrtoaddr ptr), (count * 8)
    ptr.wrapping_offset(count)
}

#[no_mangle]
pub unsafe fn ptr_offset_array(ptr: *const [i32; 4], count: isize) -> *const [i32; 4] {
    // Should use ptradd with correct element size (16 bytes)
    ptr.wrapping_offset(count)
}
