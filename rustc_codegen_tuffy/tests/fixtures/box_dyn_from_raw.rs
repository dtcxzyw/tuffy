fn main() {
    let closure: Box<dyn FnOnce() -> String + Send> = Box::new(|| String::from("ok"));
    let closure_raw = Box::into_raw(closure);
    let closure_box = unsafe { Box::from_raw(closure_raw) };
    println!("{}", closure_box());
}
