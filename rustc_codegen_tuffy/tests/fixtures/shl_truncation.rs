// Regression test for seed 800590: sub-word shift left must truncate the
// result to the operand's bit width.

fn main() {
    // u8: 189 << 5 = 6048, truncated to u8 = 160
    let a: u8 = std::hint::black_box(189);
    let shifted = a.wrapping_shl(std::hint::black_box(5));
    assert_eq!(shifted, 160_u8, "u8 shl must truncate to 8 bits");
    let divided = shifted / a;
    assert_eq!(divided, 0_u8, "160 / 189 == 0");

    // u16: 50000 << 4 = 800000, truncated to u16 = 14464
    let b: u16 = std::hint::black_box(50000);
    let s16 = b.wrapping_shl(std::hint::black_box(4));
    assert_eq!(s16, 800000_u32 as u16, "u16 shl must truncate to 16 bits");

    // i8: 100 << 2 = 400, truncated to i8 = -112 (wrapping)
    let c: i8 = std::hint::black_box(100);
    let s8 = c.wrapping_shl(std::hint::black_box(2));
    assert_eq!(s8, 400_i16 as i8, "i8 shl must truncate and wrap");

    println!("ok");
}
