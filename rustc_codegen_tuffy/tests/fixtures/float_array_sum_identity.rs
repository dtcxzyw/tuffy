// compile-flags: --edition=2024

fn check_f32(x: f32) {
    let next = IntoIterator::into_iter([x]).next().unwrap();
    let fold = IntoIterator::into_iter([x]).fold(-0.0f32, |a, b| a + b);
    let sum: f32 = IntoIterator::into_iter([x]).sum();
    assert_eq!(next.to_bits(), x.to_bits());
    assert_eq!(fold.to_bits(), x.to_bits());
    assert_eq!(sum.to_bits(), x.to_bits());
}

fn check_f64(x: f64) {
    let next = IntoIterator::into_iter([x]).next().unwrap();
    let fold = IntoIterator::into_iter([x]).fold(-0.0f64, |a, b| a + b);
    let sum: f64 = IntoIterator::into_iter([x]).sum();
    assert_eq!(next.to_bits(), x.to_bits());
    assert_eq!(fold.to_bits(), x.to_bits());
    assert_eq!(sum.to_bits(), x.to_bits());
}

fn main() {
    check_f32(-0.0);
    check_f32(-0.801_193_2);
    check_f64(-0.0);
    check_f64(f64::INFINITY);
    println!("ok");
}
