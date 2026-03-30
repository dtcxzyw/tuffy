// Regression test for seed 26780: 128-bit signed multiply overflow detection.
// The overflow flag of `i128::overflowing_mul` must be `true` when the
// mathematical product falls outside the range of i128.

fn main() {
    // Large positive operands whose product overflows i128 (from seed 26780).
    let a: i128 = 82651840253265077576806853779406465630;
    let b: i128 = 55120713690567994015539452803646006624;
    let (result, overflow) = a.overflowing_mul(b);
    assert_eq!(result, -122989185482621004698549239146577757888);
    assert!(overflow, "expected overflow for large i128 multiply");

    // i128::MAX * 2 should overflow.
    let (result2, overflow2) = i128::MAX.overflowing_mul(2);
    assert_eq!(result2, -2);
    assert!(overflow2, "expected overflow for i128::MAX * 2");

    // Small operands: no overflow.
    let (result3, overflow3) = 100_i128.overflowing_mul(200_i128);
    assert_eq!(result3, 20000);
    assert!(!overflow3, "unexpected overflow for small i128 multiply");

    // Unsigned 128-bit multiply overflow.
    let (result4, overflow4) = u128::MAX.overflowing_mul(2);
    assert_eq!(result4, u128::MAX - 1);
    assert!(overflow4, "expected overflow for u128::MAX * 2");

    // Unsigned 128-bit no overflow.
    let (result5, overflow5) = 50_u128.overflowing_mul(60_u128);
    assert_eq!(result5, 3000);
    assert!(!overflow5, "unexpected overflow for small u128 multiply");

    println!("ok");
}
