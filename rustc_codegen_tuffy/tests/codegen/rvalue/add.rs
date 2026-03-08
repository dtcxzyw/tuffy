// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off -C opt-level=3
// CHECK: fn add(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @add(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = add v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for add, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @add] param 0: Int type requires annotation
// CHECK:   [func @add] param 1: Int type requires annotation
// CHECK:   [func @add] return type: Int type requires annotation
// CHECK:
// CHECK: fn add128(_1: u128, _2: u128) -> u128 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @add128(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = add v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for add128, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @add128] param 0: Int type requires annotation
// CHECK:   [func @add128] param 1: Int type requires annotation
// CHECK:   [func @add128] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[no_mangle]
pub fn add128(a: u128, b: u128) -> u128 {
    a + b
}
