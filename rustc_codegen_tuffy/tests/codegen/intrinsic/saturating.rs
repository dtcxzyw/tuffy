// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn saturating_add_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:     scope 1 (inlined core::num::<impl i32>::saturating_add) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::saturating_add::<i32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @saturating_add_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = ssaturating_add.32 v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn saturating_add_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::saturating_add) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::saturating_add::<u32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @saturating_add_u32(%a: int:u32, %b: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:u32 = param %a
// CHECK:     v2:u32 = param %b
// CHECK:     v3 = saturating_add.32 v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: fn saturating_sub_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:     scope 1 (inlined core::num::<impl i32>::saturating_sub) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::saturating_sub::<i32>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @saturating_sub_i32(%a: int:s32, %b: int:s32) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1:s32 = param %a
// CHECK:     v2:s32 = param %b
// CHECK:     v3 = ssaturating_sub.32 v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn saturating_add_i32(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

#[no_mangle]
pub fn saturating_sub_i32(a: i32, b: i32) -> i32 {
    a.saturating_sub(b)
}

#[no_mangle]
pub fn saturating_add_u32(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
