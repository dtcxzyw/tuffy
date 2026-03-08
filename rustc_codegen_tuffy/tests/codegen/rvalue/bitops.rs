// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn bitand_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitAnd(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitand_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = and v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for bitand_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @bitand_u32] param 0: Int type requires annotation
// CHECK:   [func @bitand_u32] param 1: Int type requires annotation
// CHECK:   [func @bitand_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn bitor_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitOr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitor_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = or v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for bitor_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @bitor_u32] param 0: Int type requires annotation
// CHECK:   [func @bitor_u32] param 1: Int type requires annotation
// CHECK:   [func @bitor_u32] return type: Int type requires annotation
// CHECK:
// CHECK: fn bitxor_u32(_1: u32, _2: u32) -> u32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = BitXor(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitxor_u32(%a: int, %b: int) -> int {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int = param %a
// CHECK:     v2: int = param %b
// CHECK:     v3: int:u64 = xor v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: warning: IR verification failed for bitxor_u32, emitting stub
// CHECK:   verification failed with 3 error(s):
// CHECK:   [func @bitxor_u32] param 0: Int type requires annotation
// CHECK:   [func @bitxor_u32] param 1: Int type requires annotation
// CHECK:   [func @bitxor_u32] return type: Int type requires annotation
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn bitand_u32(a: u32, b: u32) -> u32 {
    a & b
}

#[no_mangle]
pub fn bitor_u32(a: u32, b: u32) -> u32 {
    a | b
}

#[no_mangle]
pub fn bitxor_u32(a: u32, b: u32) -> u32 {
    a ^ b
}
