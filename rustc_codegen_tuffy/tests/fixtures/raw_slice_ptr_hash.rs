use std::hash::{Hash, Hasher};

#[derive(Default)]
struct SumHasher {
    hash: u64,
}

impl Hasher for SumHasher {
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.hash += u64::from(*byte);
        }
    }

    fn finish(&self) -> u64 {
        self.hash
    }
}

fn hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = SumHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

fn main() {
    let bytes: &mut [u8] = &mut [1, 2, 3];
    let ptr = bytes.as_ptr();

    let slice_ptr = bytes as *const [u8];
    assert_eq!(hash(&slice_ptr), hash(&ptr) + bytes.len() as u64);

    let slice_ptr = bytes as *mut [u8];
    assert_eq!(hash(&slice_ptr), hash(&ptr) + bytes.len() as u64);

    println!("ok");
}
