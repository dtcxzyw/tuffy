// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn mul_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mul_i32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = mul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for mul_i32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @mul_i32] param 0: Int type requires annotation
// CHECK:   [func @mul_i32] param 1: Int type requires annotation
// CHECK:   [func @mul_i32] return type: Int type requires annotation
// CHECK:
// CHECK: fn mul_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @mul_u64(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = mul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for mul_u64, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @mul_u64] param 0: Int type requires annotation
// CHECK:   [func @mul_u64] param 1: Int type requires annotation
// CHECK:   [func @mul_u64] return type: Int type requires annotation
// CHECK:
// CHECK: fn sub_i32(_1: i32, _2: i32) -> i32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: i32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @sub_i32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = sub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for sub_i32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @sub_i32] param 0: Int type requires annotation
// CHECK:   [func @sub_i32] param 1: Int type requires annotation
// CHECK:   [func @sub_i32] return type: Int type requires annotation
// CHECK:
// CHECK: fn sub_u64(_1: u64, _2: u64) -> u64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @sub_u64(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = sub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for sub_u64, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @sub_u64] param 0: Int type requires annotation
// CHECK:   [func @sub_u64] param 1: Int type requires annotation
// CHECK:   [func @sub_u64] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn sub_i32(a: i32, b: i32) -> i32 {
    a - b
}

#[no_mangle]
pub fn mul_i32(a: i32, b: i32) -> i32 {
    a * b
}

#[no_mangle]
pub fn sub_u64(a: u64, b: u64) -> u64 {
    a - b
}

#[no_mangle]
pub fn mul_u64(a: u64, b: u64) -> u64 {
    a * b
}
