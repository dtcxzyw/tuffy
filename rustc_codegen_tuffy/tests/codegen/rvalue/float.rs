// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn const_f64() -> f64 {
// CHECK:     let mut _0: f64;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const 1.5f64;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @const_f64() -> f64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = fconst.f64 0x3ff8000000000000
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: fn fadd_f32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Add(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @fadd_f32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fadd v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn fdiv_f32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Div(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @fdiv_f32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fdiv v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn fmul_f32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Mul(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @fmul_f32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fmul v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn fsub_f32(_1: f32, _2: f32) -> f32 {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Sub(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @fsub_f32(f32, f32) -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param 0
// CHECK:     v2: f32 = param 1
// CHECK:     v3: f32 = fsub v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn neg_zero_f32() -> f32 {
// CHECK:     let mut _0: f32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const -0f32;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @neg_zero_f32() -> f32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = fconst.f32 0x80000000
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn fadd_f32(a: f32, b: f32) -> f32 {
    a + b
}

#[no_mangle]
pub fn fsub_f32(a: f32, b: f32) -> f32 {
    a - b
}

#[no_mangle]
pub fn fmul_f32(a: f32, b: f32) -> f32 {
    a * b
}

#[no_mangle]
pub fn fdiv_f32(a: f32, b: f32) -> f32 {
    a / b
}

#[no_mangle]
pub fn const_f64() -> f64 {
    1.5
}

#[no_mangle]
pub fn neg_zero_f32() -> f32 {
    -0.0
}
