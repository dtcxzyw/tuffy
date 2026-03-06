// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn maxf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::maxnumf32(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @maxf32(%a: f32, %b: f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %a
// CHECK:     v2 = param %b
// CHECK:     v3 = fcmp.ogt v1, v2
// CHECK:     v4 = select v3, v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
// CHECK: fn maxf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::maxnumf64(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @maxf64(%a: f64, %b: f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %a
// CHECK:     v2 = param %b
// CHECK:     v3 = fcmp.ogt v1, v2
// CHECK:     v4 = select v3, v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
// CHECK: fn minf32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::minnumf32(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @minf32(%a: f32, %b: f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %a
// CHECK:     v2 = param %b
// CHECK:     v3 = fcmp.olt v1, v2
// CHECK:     v4 = select v3, v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:
// CHECK: fn minf64(_1: f64, _2: f64) -> f64 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::minnumf64(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @minf64(%a: f64, %b: f64) -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1 = param %a
// CHECK:     v2 = param %b
// CHECK:     v3 = fcmp.olt v1, v2
// CHECK:     v4 = select v3, v1, v2
// CHECK:     br bb1(v0)
// CHECK:
// CHECK:   bb1(v6: mem):
// CHECK:     ret v4, v6
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::{minnumf32, minnumf64, maxnumf32, maxnumf64};

#[no_mangle]
pub unsafe fn minf32(a: f32, b: f32) -> f32 {
    minnumf32(a, b)
}

#[no_mangle]
pub unsafe fn maxf32(a: f32, b: f32) -> f32 {
    maxnumf32(a, b)
}

#[no_mangle]
pub unsafe fn minf64(a: f64, b: f64) -> f64 {
    minnumf64(a, b)
}

#[no_mangle]
pub unsafe fn maxf64(a: f64, b: f64) -> f64 {
    maxnumf64(a, b)
}
