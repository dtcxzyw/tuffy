// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn switch_three(_1: u32) -> u32 {
// CHECK:     debug x => _1;
// CHECK:     let mut _0: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = const 30_u32;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _0 = const 20_u32;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = const 10_u32;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @switch_three(%x: int:u32) -> int:u32 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u32 = param %x
// CHECK:     v2: ptr = stack_slot 4
// CHECK:     v3: int:i64 = iconst 4294967295
// CHECK:     v4: int:u64 = and v1, v3
// CHECK:     v5: int:i64 = iconst 0
// CHECK:     v6: bool = icmp.eq v4, v5
// CHECK:     brif v6, bb3(v0), bb5(v0)
// CHECK:
// CHECK:   bb1(v8: mem):
// CHECK:     v9: int:i64 = iconst 30
// CHECK:     v10: mem = store.4 v9, v2, v8
// CHECK:     br bb4(v10)
// CHECK:
// CHECK:   bb2(v12: mem):
// CHECK:     v13: int:i64 = iconst 20
// CHECK:     v14: mem = store.4 v13, v2, v12
// CHECK:     br bb4(v14)
// CHECK:
// CHECK:   bb3(v16: mem):
// CHECK:     v17: int:i64 = iconst 10
// CHECK:     v18: mem = store.4 v17, v2, v16
// CHECK:     br bb4(v18)
// CHECK:
// CHECK:   bb4(v20: mem):
// CHECK:     v21: int:u32 = load.4 v2, v20
// CHECK:     ret v21, v20
// CHECK:
// CHECK:   bb5(v23: mem):
// CHECK:     v24: int:i64 = iconst 1
// CHECK:     v25: bool = icmp.eq v4, v24
// CHECK:     brif v25, bb2(v23), bb1(v23)
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn switch_three(x: u32) -> u32 {
    match x {
        0 => 10,
        1 => 20,
        _ => 30,
    }
}
