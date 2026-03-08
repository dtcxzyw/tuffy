// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn wrapping_add_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_add) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_add_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = add v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for wrapping_add_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @wrapping_add_u32] param 0: Int type requires annotation
// CHECK:   [func @wrapping_add_u32] param 1: Int type requires annotation
// CHECK:   [func @wrapping_add_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn wrapping_mul_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_mul) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_mul_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = mul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for wrapping_mul_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @wrapping_mul_u32] param 0: Int type requires annotation
// CHECK:   [func @wrapping_mul_u32] param 1: Int type requires annotation
// CHECK:   [func @wrapping_mul_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn wrapping_sub_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::wrapping_sub) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @wrapping_sub_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = sub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for wrapping_sub_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @wrapping_sub_u32] param 0: Int type requires annotation
// CHECK:   [func @wrapping_sub_u32] param 1: Int type requires annotation
// CHECK:   [func @wrapping_sub_u32] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn wrapping_add_u32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[no_mangle]
pub fn wrapping_sub_u32(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

#[no_mangle]
pub fn wrapping_mul_u32(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}
