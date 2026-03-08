// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn f32_eq(_1: f32, _2: f32) -> bool {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Eq(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f32_eq(%a: f32, %b: f32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param %a
// CHECK:     v2: f32 = param %b
// CHECK:     v3: bool = fcmp.oeq v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn f32_ne(_1: f32, _2: f32) -> bool {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Ne(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f32_ne(%a: f32, %b: f32) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f32 = param %a
// CHECK:     v2: f32 = param %b
// CHECK:     v3: bool = fcmp.une v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:
// CHECK: fn f32_ne_nan() -> bool {
// CHECK:     let mut _0: bool;
// CHECK:     scope 1 (inlined core::f32::<impl f32>::is_nan) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = const true;
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f32_ne_nan() -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: bool = bconst true
// CHECK:     ret v1, v0
// CHECK: }
// CHECK:
// CHECK: fn f64_ne(_1: f64, _2: f64) -> bool {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: bool;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = Ne(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f64_ne(%a: f64, %b: f64) -> bool {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param %a
// CHECK:     v2: f64 = param %b
// CHECK:     v3: bool = fcmp.une v1, v2
// CHECK:     ret v3, v0
// CHECK: }
// CHECK:

#[no_mangle]
pub fn f32_ne(a: f32, b: f32) -> bool {
    // Rust's != should be !(a == b), which is !(OEq)
    // Currently uses UNe which has different NaN semantics
    a != b
}

#[no_mangle]
pub fn f32_eq(a: f32, b: f32) -> bool {
    // Should use OEq (ordered equal)
    a == b
}

#[no_mangle]
pub fn f64_ne(a: f64, b: f64) -> bool {
    // Should be !(OEq), not UNe
    a != b
}

#[no_mangle]
pub fn f32_ne_nan() -> bool {
    // NaN != NaN should be true
    // With OEq: NaN == NaN is false, so !(false) = true ✓
    // With UNe: NaN UNe NaN is true ✓
    // Both give correct result, but semantics differ
    f32::NAN.is_nan()
}
