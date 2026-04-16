// compile-flags: --edition 2024

#![feature(never_type)]

fn main() {
    let x: Result<u32, !> = Ok(123);

    let Ok(y) = x;
    assert_eq!(y, 123);

    match x {
        Ok(z) => assert_eq!(z, 123),
        Err(e) => match e {},
    }

    println!("ok");
}
