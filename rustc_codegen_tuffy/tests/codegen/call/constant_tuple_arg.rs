// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn consume_tuple(_1: (i32,)) -> i32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy (_1.0: i32);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @consume_tuple(%x: int) -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %x
// CHECK:     v2 = stack_slot 4
// CHECK:     v3 = store.4 v1, v2, v0
// CHECK:     v4 = load.4 v2, v3
// CHECK:     ret v4, v3
// CHECK: }
// CHECK:
// CHECK: fn test_constant_tuple() -> i32 {
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = consume_tuple(const (42_i32,)) -> [return: bb1, unwind continue];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @test_constant_tuple() -> int:s32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = iconst 42
// CHECK:     v2 = symbol_addr @consume_tuple
// CHECK:     v3, v4 = call v2(v1), v0 -> int
// CHECK:     br bb1(v3)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
#[inline(never)]
pub fn consume_tuple(x: (i32,)) -> i32 {
    x.0
}

#[no_mangle]
pub fn test_constant_tuple() -> i32 {
    consume_tuple((42,))
}
