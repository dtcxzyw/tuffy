fn main() {
    let mut value = (1, "a");
    value.1 = "b";
    println!("{}", value.1);
}
