// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn f64_to_i128(_1: f64) -> i128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i128 (FloatToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f64_to_i128(f64) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i64 = bitcast v1
// CHECK:     v4: int:s64 = fp_to_si v1
// CHECK:     v5: int:i64 = iconst 4890909195324358656
// CHECK:     v6: f64 = bitcast v5
// CHECK:     v7: int:s128 = sext v4, 128
// CHECK:     v8: mem = store.16 v7, v2, v0
// CHECK:     v9: int:s128 = load.16 v2, v8
// CHECK:     ret v9, v8
// CHECK: }
// CHECK:
// CHECK: fn f64_to_u128(_1: f64) -> u128 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as u128 (FloatToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @f64_to_u128(f64) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: f64 = param 0
// CHECK:     v2: ptr = stack_slot 16 align 16
// CHECK:     v3: int:i64 = bitcast v1
// CHECK:     v4: int:u64 = fp_to_ui v1
// CHECK:     v5: int:i64 = iconst 4890909195324358656
// CHECK:     v6: f64 = bitcast v5
// CHECK:     v7: int:u128 = zext v4, 128
// CHECK:     v8: mem = store.16 v7, v2, v0
// CHECK:     v9: int:u128 = load.16 v2, v8
// CHECK:     ret v9, v8
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn f64_to_i128(x: f64) -> i128 {
    x as i128
}

#[no_mangle]
pub fn f64_to_u128(x: f64) -> u128 {
    x as u128
}
