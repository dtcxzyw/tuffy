// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn range_next_value(_1: &mut core::ops::Range<usize>) -> usize {
// CHECK:     debug range => _1;
// CHECK:     let mut _0: usize;
// CHECK:     let mut _2: core::option::Option<usize>;
// CHECK:     scope 1 {
// CHECK:         debug value => _0;
// CHECK:     }
// CHECK:     scope 2 (inlined core::iter::range::<impl core::iter::Iterator for core::ops::Range<usize>>::next) {
// CHECK:         scope 3 (inlined <core::ops::Range<usize> as core::iter::range::RangeIteratorImpl>::spec_next) {
// CHECK:             let mut _3: bool;
// CHECK:             let _4: usize;
// CHECK:             let mut _5: usize;
// CHECK:             scope 4 {
// CHECK:                 scope 6 (inlined <usize as core::iter::Step>::forward_unchecked) {
// CHECK:                     scope 7 (inlined #[track_caller] core::num::<impl usize>::unchecked_add) {
// CHECK:                         scope 8 (inlined core::ub_checks::check_language_ub) {
// CHECK:                             scope 9 (inlined core::ub_checks::check_language_ub::runtime) {
// CHECK:                             }
// CHECK:                         }
// CHECK:                     }
// CHECK:                 }
// CHECK:             }
// CHECK:             scope 5 (inlined core::cmp::impls::<impl core::cmp::PartialOrd for usize>::lt) {
// CHECK:                 let mut _6: usize;
// CHECK:                 let mut _7: usize;
// CHECK:             }
// CHECK:         }
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _6 = copy ((*_1).0: usize);
// CHECK:         _7 = copy ((*_1).1: usize);
// CHECK:         _3 = Lt(move _6, move _7);
// CHECK:         switchInt(move _3) -> [0: bb3, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         _4 = copy ((*_1).0: usize);
// CHECK:         _5 = AddUnchecked(copy _4, const 1_usize);
// CHECK:         ((*_1).0: usize) = move _5;
// CHECK:         _2 = core::option::Option::<usize>::Some(copy _4);
// CHECK:         _0 = copy ((_2 as Some).0: usize);
// CHECK:         goto -> bb1;
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         _0 = const 0_usize;
// CHECK:         goto -> bb1;
// CHECK:     }
// CHECK: }
// CHECK: func @range_next_value(ptr) -> int:u64 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: ptr = param 0
// CHECK:     v2: ptr = stack_slot 8 align 8
// CHECK:     v3: ptr = stack_slot 16 align 8
// CHECK:     v4: int:u64 = load.8 v1, v0
// CHECK:     v5: int:i64 = iconst 8
// CHECK:     v6: ptr = ptradd v1, v5
// CHECK:     v7: int:u64 = load.8 v6, v0
// CHECK:     v8: bool = icmp.lt v4, v7
// CHECK:     v9: int:u64 = iconst 1
// CHECK:     v10: int:u64 = iconst 0
// CHECK:     v11: int:u64 = select v8, v9, v10
// CHECK:     v12: int:i64 = iconst 255
// CHECK:     v13: int:u64 = and v11, v12
// CHECK:     v14: int:i8 = iconst 0
// CHECK:     v15: bool = icmp.eq v13, v14
// CHECK:     brif v15, bb2(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v17: mem):
// CHECK:     v18: int:u64 = load.8 v1, v17
// CHECK:     v19: int:i64 = iconst 1
// CHECK:     v20: int:u64 = add v18, v19:u64
// CHECK:     v21: mem = store.8 v20, v1, v17
// CHECK:     v22: int:i64 = iconst 0
// CHECK:     v23: mem = store.8 v22, v3, v21
// CHECK:     v24: int:i64 = iconst 8
// CHECK:     v25: ptr = ptradd v3, v24
// CHECK:     v26: mem = store.8 v22, v25, v23
// CHECK:     v27: int:i64 = iconst 8
// CHECK:     v28: ptr = ptradd v3, v27
// CHECK:     v29: mem = store.8 v18, v28, v26
// CHECK:     v30: int:i64 = iconst 1
// CHECK:     v31: mem = store.8 v30, v3, v29
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v3, v32
// CHECK:     v34: int:u64 = load.8 v33, v31
// CHECK:     v35: mem = store.8 v34, v2, v31
// CHECK:     br bb3(v35)
// CHECK:
// CHECK:   bb2(v37: mem):
// CHECK:     v38: int:i64 = iconst 0
// CHECK:     v39: mem = store.8 v38, v2, v37
// CHECK:     br bb3(v39)
// CHECK:
// CHECK:   bb3(v41: mem):
// CHECK:     v42: int:u64 = load.8 v2, v41
// CHECK:     ret v42, v41
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn range_next_value(range: &mut core::ops::Range<usize>) -> usize {
    match range.next() {
        Some(value) => value,
        None => 0,
    }
}
