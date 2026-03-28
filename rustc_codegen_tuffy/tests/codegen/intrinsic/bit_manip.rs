// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn bitreverse_u32(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::reverse_bits) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::bitreverse::<u32>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bitreverse_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = bit_reverse.32 v1
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v4: mem):
// CHECK:     ret v2, v4
// CHECK: }
// CHECK:
// CHECK: fn bswap_u32(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::swap_bytes) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::bswap::<u32>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @bswap_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = bswap.4 v1
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v4: mem):
// CHECK:     ret v2, v4
// CHECK: }
// CHECK:
// CHECK: fn ctlz_u32(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::leading_zeros) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::ctlz::<u32>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ctlz_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u32 = count_leading_zeros.32 v1
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v4: mem):
// CHECK:     ret v2, v4
// CHECK: }
// CHECK:
// CHECK: fn ctpop_u32(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::count_ones) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::ctpop::<u32>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @ctpop_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u64 = count_ones v1
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v4: mem):
// CHECK:     ret v2, v4
// CHECK: }
// CHECK:
// CHECK: fn cttz_u32(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:     scope 1 (inlined core::num::<impl u32>::trailing_zeros) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::cttz::<u32>(move _1) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @cttz_u32(int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param 0
// CHECK:     v2: int:u64 = count_trailing_zeros v1
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v4: mem):
// CHECK:     ret v2, v4
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn ctpop_u32(x: u32) -> u32 {
    x.count_ones()
}

#[no_mangle]
pub fn ctlz_u32(x: u32) -> u32 {
    x.leading_zeros()
}

#[no_mangle]
pub fn cttz_u32(x: u32) -> u32 {
    x.trailing_zeros()
}

#[no_mangle]
pub fn bswap_u32(x: u32) -> u32 {
    x.swap_bytes()
}

#[no_mangle]
pub fn bitreverse_u32(x: u32) -> u32 {
    x.reverse_bits()
}
