#![feature(funnel_shifts)]

fn main() {
    let a8 = std::hint::black_box(44_u8);
    let b8 = std::hint::black_box(11_u8);
    let a32 = std::hint::black_box(44_u32);
    let b32 = std::hint::black_box(11_u32);

    assert_eq!(u8::funnel_shl(a8, b8, 0), a8);
    assert_eq!(u8::funnel_shr(a8, b8, 0), b8);
    assert_eq!(u32::funnel_shl(a32, b32, 0), a32);
    assert_eq!(u32::funnel_shr(a32, b32, 0), b32);

    println!("ok");
}
