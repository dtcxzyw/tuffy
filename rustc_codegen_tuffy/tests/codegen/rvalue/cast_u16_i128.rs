// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off --crate-type lib
// CHECK: fn u16_to_i128(_1: u16) -> i128 {
// CHECK:     debug a => _1;
// CHECK:     let mut _0: i128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = copy _1 as i128 (IntToInt);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @u16_to_i128(int:u16) -> int:s128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u16 = param 0
// CHECK:     v2: ptr = stack_slot 16
// CHECK:     v3: int:u64 = zext v1, 64
// CHECK:     v4: int:u128 = zext v3, 128
// CHECK:     v5: mem = store.16 v4, v2, v0
// CHECK:     v6: int:s128 = load.16 v2, v5
// CHECK:     ret v6, v5
// CHECK: }
// CHECK:

#[no_mangle]
pub fn u16_to_i128(a: u16) -> i128 {
    a as i128
}
