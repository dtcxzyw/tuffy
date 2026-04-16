use std::thread;

fn main() {
    let message = String::from("ok");
    let handle = thread::spawn(move || message);
    println!("{}", handle.join().unwrap());
}
