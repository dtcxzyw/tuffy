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
// CHECK: func @consume_tuple() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:i64 = iconst 0
// CHECK:     v2: ptr = stack_slot 4
// CHECK:     v3: mem = store.4 v1, v2, v0
// CHECK:     v4: int = load.4 v2, v3
// CHECK:     ret v4, v3
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for consume_tuple, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @consume_tuple] return type: Int type requires annotation
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
// CHECK: func @test_constant_tuple() -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = symbol_addr @consume_tuple
// CHECK:     v2: mem, v3: int = call v1(), v0 -> int
// CHECK:     br bb1(v2)
// CHECK:
// CHECK:   bb1(v5: mem):
// CHECK:     ret v3, v5
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for test_constant_tuple, emitting stub
// CHECK:   verification failed with 1 error(s):
// CHECK:   [func @test_constant_tuple] return type: Int type requires annotation
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
