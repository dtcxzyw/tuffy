// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off
// CHECK: fn core::intrinsics::rotate_left(_1: T, _2: u32) -> T {
// CHECK:     debug x => _1;
// CHECK:     debug shift => _2;
// CHECK:     let mut _0: T;
// CHECK:     let mut _3: u32;
// CHECK:     let mut _4: u32;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::mem::size_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const <T as core::mem::SizedTypeProperties>::SIZE as u32 (IntToInt);
// CHECK:         _4 = Mul(move _5, const 8_u32);
// CHECK:         StorageDead(_5);
// CHECK:         _6 = Eq(copy _4, const 0_u32);
// CHECK:         assert(!move _6, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _2) -> [success: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = Rem(copy _2, move _4);
// CHECK:         StorageDead(_4);
// CHECK:         _0 = core::intrinsics::unchecked_funnel_shl::<T>(copy _1, move _1, move _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: data @.Lloc_file.0 = "$SYSROOT/library/core/src/intrinsics/mod.rs"
// CHECK: data @.Lloc.1 = "..." relocs [0: @.Lloc_file.0]
// CHECK: func @_RINvNtC$HASH_4core10intrinsics11rotate_leftoEC$HASH_11rotate_u128(int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: int:u64 = iconst 4294967295
// CHECK:     v6: int:u32 = and v4, v5
// CHECK:     v7: int:i32 = iconst 8
// CHECK:     v8: int:i32 = mul v6, v7:u32
// CHECK:     v9: int:u32 = zext v8, 32
// CHECK:     v10: int:i32 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10:u32
// CHECK:     v12: int:u64 = iconst 1
// CHECK:     v13: int:u64 = iconst 0
// CHECK:     v14: int:u64 = select v11, v12, v13
// CHECK:     v15: int:i64 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: int:u32 = rem v2, v9
// CHECK:     v20: int:i64 = iconst 128
// CHECK:     v21: int:u64 = sub v20, v19
// CHECK:     v22: int:u64 = iconst 0
// CHECK:     v23: int:u128 = shl v1, v19
// CHECK:     v24: int:u128 = shr v1, v21
// CHECK:     v25: bool = icmp.eq v19, v22
// CHECK:     v26: int:u128 = select v25, v22, v24
// CHECK:     v27: int:u128 = or v23, v26
// CHECK:     v28: ptr = stack_slot 16
// CHECK:     v29: mem = store.16 v27, v28, v18
// CHECK:     v30: int:i64 = load.8 v28, v29
// CHECK:     v31: mem = store.8 v30, v3, v29
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v28, v32
// CHECK:     v34: int:i64 = load.8 v33, v31
// CHECK:     v35: int:i64 = iconst 8
// CHECK:     v36: ptr = ptradd v3, v35
// CHECK:     v37: mem = store.8 v34, v36, v31
// CHECK:     br bb2(v37)
// CHECK:
// CHECK:   bb2(v39: mem):
// CHECK:     v40: int:u128 = load.16 v3, v39
// CHECK:     ret v40, v39
// CHECK:
// CHECK:   bb3(v42: mem):
// CHECK:     v43: ptr = symbol_addr @.Lloc.1
// CHECK:     v44: ptr = symbol_addr @_RNvNtNtC$HASH_4core9panicking11panic_const23panic_const_rem_by_zero
// CHECK:     v45: mem = call v44(v43), v42
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::rotate_right(_1: T, _2: u32) -> T {
// CHECK:     debug x => _1;
// CHECK:     debug shift => _2;
// CHECK:     let mut _0: T;
// CHECK:     let mut _3: u32;
// CHECK:     let mut _4: u32;
// CHECK:     let mut _5: u32;
// CHECK:     let mut _6: bool;
// CHECK:     scope 1 (inlined core::mem::size_of::<T>) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         StorageLive(_5);
// CHECK:         _5 = const <T as core::mem::SizedTypeProperties>::SIZE as u32 (IntToInt);
// CHECK:         _4 = Mul(move _5, const 8_u32);
// CHECK:         StorageDead(_5);
// CHECK:         _6 = Eq(copy _4, const 0_u32);
// CHECK:         assert(!move _6, "attempt to calculate the remainder of `{}` with a divisor of zero", copy _2) -> [success: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _3 = Rem(copy _2, move _4);
// CHECK:         StorageDead(_4);
// CHECK:         _0 = core::intrinsics::unchecked_funnel_shr::<T>(copy _1, move _1, move _3) -> [return: bb2, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageDead(_3);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: data @.Lloc_file.2 = "$SYSROOT/library/core/src/intrinsics/mod.rs"
// CHECK: data @.Lloc.3 = "..." relocs [0: @.Lloc_file.2]
// CHECK: func @_RINvNtC$HASH_4core10intrinsics12rotate_rightoEC$HASH_11rotate_u128(int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i64 = iconst 16
// CHECK:     v5: int:u64 = iconst 4294967295
// CHECK:     v6: int:u32 = and v4, v5
// CHECK:     v7: int:i32 = iconst 8
// CHECK:     v8: int:i32 = mul v6, v7:u32
// CHECK:     v9: int:u32 = zext v8, 32
// CHECK:     v10: int:i32 = iconst 0
// CHECK:     v11: bool = icmp.eq v9, v10:u32
// CHECK:     v12: int:u64 = iconst 1
// CHECK:     v13: int:u64 = iconst 0
// CHECK:     v14: int:u64 = select v11, v12, v13
// CHECK:     v15: int:i64 = iconst 0
// CHECK:     v16: bool = icmp.eq v14, v15
// CHECK:     brif v16, bb1(v0), bb3(v0)
// CHECK:
// CHECK:   bb1(v18: mem):
// CHECK:     v19: int:u32 = rem v2, v9
// CHECK:     v20: int:i64 = iconst 128
// CHECK:     v21: int:u64 = sub v20, v19
// CHECK:     v22: int:u64 = iconst 0
// CHECK:     v23: int:u128 = shl v1, v21
// CHECK:     v24: int:u128 = shr v1, v19
// CHECK:     v25: bool = icmp.eq v19, v22
// CHECK:     v26: int:u128 = select v25, v22, v23
// CHECK:     v27: int:u128 = or v26, v24
// CHECK:     v28: ptr = stack_slot 16
// CHECK:     v29: mem = store.16 v27, v28, v18
// CHECK:     v30: int:i64 = load.8 v28, v29
// CHECK:     v31: mem = store.8 v30, v3, v29
// CHECK:     v32: int:i64 = iconst 8
// CHECK:     v33: ptr = ptradd v28, v32
// CHECK:     v34: int:i64 = load.8 v33, v31
// CHECK:     v35: int:i64 = iconst 8
// CHECK:     v36: ptr = ptradd v3, v35
// CHECK:     v37: mem = store.8 v34, v36, v31
// CHECK:     br bb2(v37)
// CHECK:
// CHECK:   bb2(v39: mem):
// CHECK:     v40: int:u128 = load.16 v3, v39
// CHECK:     ret v40, v39
// CHECK:
// CHECK:   bb3(v42: mem):
// CHECK:     v43: ptr = symbol_addr @.Lloc.3
// CHECK:     v44: ptr = symbol_addr @_RNvNtNtC$HASH_4core9panicking11panic_const23panic_const_rem_by_zero
// CHECK:     v45: mem = call v44(v43), v42
// CHECK:     trap
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::disjoint_bitor(_1: T, _2: T) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::DisjointBitOr>::disjoint_bitor(move _1, move _2) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics14disjoint_bitoroEC$HASH_11rotate_u128(int:u128, int:u128, ptr) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: ptr = param 2
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: ptr = symbol_addr @_RNvXsf_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_13DisjointBitOr14disjoint_bitorC$HASH_11rotate_u128
// CHECK:     v6: mem, v7: int:u128 = call v5(v1, v2), v0 -> int:u128
// CHECK:     v8: mem = store.16 v7, v4, v6
// CHECK:     br bb1(v8)
// CHECK:
// CHECK:   bb1(v10: mem):
// CHECK:     v11: int:u128 = load.16 v4, v10
// CHECK:     ret v11, v10
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::unchecked_funnel_shl(_1: T, _2: T, _3: u32) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shl(move _1, move _2, move _3) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics20unchecked_funnel_shloEC$HASH_11rotate_u128(int:u128, int:u128, int:u32, ptr) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = param 3
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: ptr = symbol_addr @_RNvXsr_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_11FunnelShift20unchecked_funnel_shlC$HASH_11rotate_u128
// CHECK:     v7: mem, v8: int:u128 = call v6(v1, v2, v3), v0 -> int:u128
// CHECK:     v9: mem = store.16 v8, v5, v7
// CHECK:     br bb1(v9)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u128 = load.16 v5, v11
// CHECK:     ret v12, v11
// CHECK: }
// CHECK:
// CHECK: fn core::intrinsics::unchecked_funnel_shr(_1: T, _2: T, _3: u32) -> T {
// CHECK:     debug a => _1;
// CHECK:     debug b => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: T;
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = <T as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shr(move _1, move _2, move _3) -> [return: bb1, unwind terminate(abi)];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RINvNtC$HASH_4core10intrinsics20unchecked_funnel_shroEC$HASH_11rotate_u128(int:u128, int:u128, int:u32, ptr) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = param 3
// CHECK:     v5: ptr = stack_slot 16 align 16
// CHECK:     v6: ptr = symbol_addr @_RNvXsr_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_11FunnelShift20unchecked_funnel_shrC$HASH_11rotate_u128
// CHECK:     v7: mem, v8: int:u128 = call v6(v1, v2, v3), v0 -> int:u128
// CHECK:     v9: mem = store.16 v8, v5, v7
// CHECK:     br bb1(v9)
// CHECK:
// CHECK:   bb1(v11: mem):
// CHECK:     v12: int:u128 = load.16 v5, v11
// CHECK:     ret v12, v11
// CHECK: }
// CHECK:
// CHECK: fn <u128 as core::intrinsics::fallback::DisjointBitOr>::disjoint_bitor(_1: u128, _2: u128) -> u128 {
// CHECK:     debug self => _1;
// CHECK:     debug other => _2;
// CHECK:     let mut _0: u128;
// CHECK:     let mut _3: bool;
// CHECK:     let mut _4: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_3);
// CHECK:         StorageLive(_4);
// CHECK:         _4 = BitAnd(copy _1, copy _2);
// CHECK:         _3 = Eq(move _4, const 0_u128);
// CHECK:         StorageDead(_4);
// CHECK:         assume(move _3);
// CHECK:         StorageDead(_3);
// CHECK:         _0 = BitOr(copy _1, copy _2);
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsf_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_13DisjointBitOr14disjoint_bitorC$HASH_11rotate_u128(int:u128, int:u128) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:i128 = and v1, v2
// CHECK:     v5: int:i128 = iconst 0
// CHECK:     v6: bool = icmp.eq v4:u128, v5:u128
// CHECK:     v7: int:i128 = or v1, v2
// CHECK:     v8: mem = store.16 v7, v3, v0
// CHECK:     v9: int:u128 = load.16 v3, v8
// CHECK:     ret v9, v8
// CHECK: }
// CHECK:
// CHECK: fn <u128 as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shl(_1: u128, _2: u128, _3: u32) -> u128 {
// CHECK:     debug self => _1;
// CHECK:     debug rhs => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: u128;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: u128;
// CHECK:     let mut _6: u128;
// CHECK:     let mut _7: u32;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _3, const 128_u32);
// CHECK:         assume(move _4);
// CHECK:         StorageDead(_4);
// CHECK:         switchInt(copy _3) -> [0: bb1, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _1;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_5);
// CHECK:         _5 = ShlUnchecked(copy _1, copy _3);
// CHECK:         StorageLive(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = Sub(const 128_u32, copy _3);
// CHECK:         _6 = ShrUnchecked(copy _2, move _7);
// CHECK:         StorageDead(_7);
// CHECK:         _0 = core::intrinsics::disjoint_bitor::<u128>(move _5, move _6) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageDead(_6);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsr_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_11FunnelShift20unchecked_funnel_shlC$HASH_11rotate_u128(int:u128, int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:i32 = iconst 128
// CHECK:     v6: bool = icmp.lt v3, v5:u32
// CHECK:     v7: int:i64 = iconst 4294967295
// CHECK:     v8: int:u64 = and v3, v7
// CHECK:     v9: int:i32 = iconst 0
// CHECK:     v10: bool = icmp.eq v8, v9
// CHECK:     brif v10, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     v13: int:i64 = iconst 127
// CHECK:     v14: int:i64 = and v3, v13
// CHECK:     v15: int:i128 = shl v1, v14
// CHECK:     v16: int:i32 = iconst 128
// CHECK:     v17: int:i32 = sub v16:u32, v3
// CHECK:     v18: int:u32 = zext v17, 32
// CHECK:     v19: int:i64 = iconst 127
// CHECK:     v20: int:i64 = and v18, v19
// CHECK:     v21: int:u128 = shr v2, v20
// CHECK:     v22: int:u128 = or v15, v21
// CHECK:     v23: mem = store.16 v22, v4, v12
// CHECK:     br bb2(v23)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     br bb4(v25)
// CHECK:
// CHECK:   bb3(v27: mem):
// CHECK:     v28: mem = store.16 v1, v4, v27
// CHECK:     br bb4(v28)
// CHECK:
// CHECK:   bb4(v30: mem):
// CHECK:     v31: int:u128 = load.16 v4, v30
// CHECK:     ret v31, v30
// CHECK: }
// CHECK:
// CHECK: fn <u128 as core::intrinsics::fallback::FunnelShift>::unchecked_funnel_shr(_1: u128, _2: u128, _3: u32) -> u128 {
// CHECK:     debug self => _1;
// CHECK:     debug rhs => _2;
// CHECK:     debug shift => _3;
// CHECK:     let mut _0: u128;
// CHECK:     let mut _4: bool;
// CHECK:     let mut _5: u128;
// CHECK:     let mut _6: u32;
// CHECK:     let mut _7: u128;
// CHECK:
// CHECK:     bb0: {
// CHECK:         StorageLive(_4);
// CHECK:         _4 = Lt(copy _3, const 128_u32);
// CHECK:         assume(move _4);
// CHECK:         StorageDead(_4);
// CHECK:         switchInt(copy _3) -> [0: bb1, otherwise: bb2];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         _0 = copy _2;
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb2: {
// CHECK:         StorageLive(_5);
// CHECK:         StorageLive(_6);
// CHECK:         _6 = Sub(const 128_u32, copy _3);
// CHECK:         _5 = ShlUnchecked(copy _1, move _6);
// CHECK:         StorageDead(_6);
// CHECK:         StorageLive(_7);
// CHECK:         _7 = ShrUnchecked(copy _2, copy _3);
// CHECK:         _0 = core::intrinsics::disjoint_bitor::<u128>(move _5, move _7) -> [return: bb3, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb3: {
// CHECK:         StorageDead(_7);
// CHECK:         StorageDead(_5);
// CHECK:         goto -> bb4;
// CHECK:     }
// CHECK:
// CHECK:     bb4: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @_RNvXsr_NtNtC$HASH_4core10intrinsics8fallbackoNtB5_11FunnelShift20unchecked_funnel_shrC$HASH_11rotate_u128(int:u128, int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u128 = param 1
// CHECK:     v3: int:u32 = param 2
// CHECK:     v4: ptr = stack_slot 16 align 16
// CHECK:     v5: int:i32 = iconst 128
// CHECK:     v6: bool = icmp.lt v3, v5:u32
// CHECK:     v7: int:i64 = iconst 4294967295
// CHECK:     v8: int:u64 = and v3, v7
// CHECK:     v9: int:i32 = iconst 0
// CHECK:     v10: bool = icmp.eq v8, v9
// CHECK:     brif v10, bb3(v0), bb1(v0)
// CHECK:
// CHECK:   bb1(v12: mem):
// CHECK:     v13: int:i32 = iconst 128
// CHECK:     v14: int:i32 = sub v13:u32, v3
// CHECK:     v15: int:u32 = zext v14, 32
// CHECK:     v16: int:i64 = iconst 127
// CHECK:     v17: int:i64 = and v15, v16
// CHECK:     v18: int:i128 = shl v1, v17
// CHECK:     v19: int:i64 = iconst 127
// CHECK:     v20: int:i64 = and v3, v19
// CHECK:     v21: int:u128 = shr v2, v20
// CHECK:     v22: int:u128 = or v18, v21
// CHECK:     v23: mem = store.16 v22, v4, v12
// CHECK:     br bb2(v23)
// CHECK:
// CHECK:   bb2(v25: mem):
// CHECK:     br bb4(v25)
// CHECK:
// CHECK:   bb3(v27: mem):
// CHECK:     v28: mem = store.16 v2, v4, v27
// CHECK:     br bb4(v28)
// CHECK:
// CHECK:   bb4(v30: mem):
// CHECK:     v31: int:u128 = load.16 v4, v30
// CHECK:     ret v31, v30
// CHECK: }
// CHECK:
// CHECK: fn rotate_left_u128(_1: u128, _2: u32) -> u128 {
// CHECK:     debug x => _1;
// CHECK:     debug n => _2;
// CHECK:     let mut _0: u128;
// CHECK:     scope 1 (inlined core::num::<impl u128>::rotate_left) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::rotate_left::<u128>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rotate_left_u128(int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:u128 = rotate_left.128 v1, v2
// CHECK:     v5: mem = store.16 v4, v3, v0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     v8: int:u128 = load.16 v3, v7
// CHECK:     ret v8, v7
// CHECK: }
// CHECK:
// CHECK: fn rotate_right_u128(_1: u128, _2: u32) -> u128 {
// CHECK:     debug x => _1;
// CHECK:     debug n => _2;
// CHECK:     let mut _0: u128;
// CHECK:     scope 1 (inlined core::num::<impl u128>::rotate_right) {
// CHECK:     }
// CHECK:
// CHECK:     bb0: {
// CHECK:         _0 = core::intrinsics::rotate_right::<u128>(move _1, move _2) -> [return: bb1, unwind unreachable];
// CHECK:     }
// CHECK:
// CHECK:     bb1: {
// CHECK:         return;
// CHECK:     }
// CHECK: }
// CHECK: func @rotate_right_u128(int:u128, int:u32) -> int:u128 {
// CHECK:   bb0(v0: mem):
// CHECK:     v1: int:u128 = param 0
// CHECK:     v2: int:u32 = param 1
// CHECK:     v3: ptr = stack_slot 16 align 16
// CHECK:     v4: int:u128 = rotate_right.128 v1, v2
// CHECK:     v5: mem = store.16 v4, v3, v0
// CHECK:     br bb1(v5)
// CHECK:
// CHECK:   bb1(v7: mem):
// CHECK:     v8: int:u128 = load.16 v3, v7
// CHECK:     ret v8, v7
// CHECK: }
// CHECK:

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn rotate_left_u128(x: u128, n: u32) -> u128 {
    x.rotate_left(n)
}

#[no_mangle]
pub fn rotate_right_u128(x: u128, n: u32) -> u128 {
    x.rotate_right(n)
}
