trait Typed {
    fn possible(&self) -> Option<&'static [&'static str]> {
        None
    }
}

trait AnyP {
    fn possible(&self) -> Option<&'static [&'static str]>;
}

impl<T: Typed + 'static> AnyP for T {
    fn possible(&self) -> Option<&'static [&'static str]> {
        T::possible(self)
    }
}

struct BoolP;
struct StringP;

impl Typed for BoolP {
    fn possible(&self) -> Option<&'static [&'static str]> {
        Some(&["true", "false"])
    }
}

impl Typed for StringP {}

enum Inner {
    Bool,
    String,
}

struct ValueParser(Inner);

impl ValueParser {
    fn string() -> Self {
        Self(Inner::String)
    }

    fn possible(&self) -> Option<&'static [&'static str]> {
        let parser: &dyn AnyP = match &self.0 {
            Inner::Bool => &BoolP,
            Inner::String => &StringP,
        };
        parser.possible()
    }
}

fn main() {
    let parser = ValueParser::string();
    assert_eq!(parser.possible(), None);
    println!("ok");
}
