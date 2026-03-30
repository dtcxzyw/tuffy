// Regression test for seed 158297: 64-bit unsigned multiply overflow detection.
// The overflow flag of `u64::overflowing_mul` must be `true` when the
// mathematical product exceeds u64::MAX.

fn main() {
    // Large operands whose product overflows u64.
    let (result, overflow) = 4810135260100336559_u64.overflowing_mul(9589940975249020400_u64);
    assert_eq!(result, 15390668357513842448);
    assert!(overflow, "expected overflow for large u64 multiply");

    // Small operands: no overflow.
    let (result2, overflow2) = 3_u64.overflowing_mul(7_u64);
    assert_eq!(result2, 21);
    assert!(!overflow2, "unexpected overflow for small u64 multiply");

    println!("ok");
}
