#[derive(Clone, Copy)]
struct Big([u64; 4]);

struct Counter(u64);

trait BigWrite {
    fn emit_big(&mut self) -> Big;
}

impl BigWrite for Counter {
    fn emit_big(&mut self) -> Big {
        self.0 += 1;
        Big([self.0, self.0 + 1, self.0 + 2, self.0 + 3])
    }
}

impl<W: BigWrite + ?Sized> BigWrite for &mut W {
    fn emit_big(&mut self) -> Big {
        (**self).emit_big()
    }
}

fn call_through_ref(mut counter: Counter) -> Big {
    let mut inner = &mut counter;
    BigWrite::emit_big(&mut inner)
}

fn main() {
    let big = call_through_ref(Counter(10));
    println!("{}", big.0[3]);
}
