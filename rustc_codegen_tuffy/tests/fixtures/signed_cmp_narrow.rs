fn main() {
    let lhs = std::hint::black_box(-10_i32);
    let rhs = std::hint::black_box(10_i32);

    assert!(lhs < rhs);
    assert_eq!(lhs.cmp(&rhs), std::cmp::Ordering::Less);
    assert!(!(lhs..rhs).is_empty());

    println!("ok");
}
