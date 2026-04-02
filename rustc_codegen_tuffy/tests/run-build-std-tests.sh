#!/bin/bash
# Build the Rust standard library (core, alloc, std) from source with the tuffy
# codegen backend and run a comprehensive test suite covering collections,
# formatting, iterators, I/O, threading, panic unwinding, and more.
#
# Usage:
#   # Local (auto-discovers backend):
#   bash rustc_codegen_tuffy/tests/run-build-std-tests.sh
#
#   # CI (explicit backend):
#   BACKEND=path/to/librustc_codegen_tuffy.so \
#     bash rustc_codegen_tuffy/tests/run-build-std-tests.sh
#
# Requirements: rust-src component (rustup component add rust-src)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# ── Find backend .so ──────────────────────────────────────────────────────────

if [ -n "${BACKEND:-}" ]; then
    # Convert to absolute path so it works when cargo runs in WORK_DIR
    BACKEND="$(realpath "$BACKEND")"
elif [ -f "$CRATE_ROOT/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
elif [ -f "$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
else
    echo "ERROR: Backend not found."
    echo "Run: cd rustc_codegen_tuffy && cargo build"
    exit 1
fi

# ── Verify rust-src component ─────────────────────────────────────────────────

TOOLCHAIN="nightly-2026-03-28"
if ! rustup +$TOOLCHAIN component list --installed 2>/dev/null | grep -q rust-src; then
    echo "Installing rust-src component..."
    rustup +$TOOLCHAIN component add rust-src
fi

# ── Set up temporary project ──────────────────────────────────────────────────

WORK_DIR="${OUT_DIR:-/tmp/tuffy_build_std_test}"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR/src" "$WORK_DIR/.cargo"

cat > "$WORK_DIR/Cargo.toml" <<'TOML'
[package]
name = "tuffy-build-std-tests"
version = "0.0.0"
edition = "2024"

[profile.dev]
panic = "abort"

[profile.test]
panic = "unwind"
TOML

cat > "$WORK_DIR/.cargo/config.toml" <<CFGEOF
[build]
target = "x86_64-unknown-linux-gnu"

[unstable]
build-std = ["core", "alloc", "std", "panic_unwind", "panic_abort"]
CFGEOF

# ── Write the test source ────────────────────────────────────────────────────

cat > "$WORK_DIR/src/main.rs" <<'RUSTEOF'
fn main() {}

#[cfg(test)]
mod collections {
    use std::collections::{HashMap, BTreeMap, HashSet, BTreeSet, VecDeque, BinaryHeap};

    #[test]
    fn vec_push_pop() {
        let mut v = vec![1, 2, 3];
        v.push(4);
        assert_eq!(v.len(), 4);
        assert_eq!(v.pop(), Some(4));
    }

    #[test]
    fn vec_sort() {
        let mut v = vec![5, 3, 1, 4, 2];
        v.sort();
        assert_eq!(v, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn vec_dedup() {
        let mut v = vec![1, 1, 2, 3, 3, 3, 4];
        v.dedup();
        assert_eq!(v, [1, 2, 3, 4]);
    }

    #[test]
    fn slice_binary_search() {
        let v = vec![1, 3, 5, 7, 9];
        assert_eq!(v.binary_search(&5), Ok(2));
        assert_eq!(v.binary_search(&4), Err(2));
    }

    #[test]
    fn slice_windows_chunks() {
        let v = vec![1, 2, 3, 4, 5];
        assert_eq!(v.windows(3).count(), 3);
        assert_eq!(v.chunks(2).count(), 3);
    }

    #[test]
    fn hashmap_crud() {
        let mut m = HashMap::new();
        m.insert("a", 1);
        m.insert("b", 2);
        m.insert("c", 3);
        assert_eq!(m.get("b"), Some(&2));
        m.remove("b");
        assert_eq!(m.get("b"), None);
        assert_eq!(m.len(), 2);
    }

    #[test]
    fn hashmap_entry() {
        let mut m = HashMap::new();
        *m.entry("k").or_insert(0) += 1;
        *m.entry("k").or_insert(0) += 1;
        assert_eq!(m["k"], 2);
    }

    #[test]
    fn hashmap_collect() {
        let m: HashMap<i32, i32> = (0..10).map(|i| (i, i * i)).collect();
        assert_eq!(m.values().sum::<i32>(), 285);
    }

    #[test]
    fn btreemap_order() {
        let mut m = BTreeMap::new();
        m.insert(3, "c");
        m.insert(1, "a");
        m.insert(2, "b");
        let keys: Vec<_> = m.keys().collect();
        assert_eq!(keys, [&1, &2, &3]);
    }

    #[test]
    fn hashset_ops() {
        let a: HashSet<i32> = [1, 2, 3].into();
        let b: HashSet<i32> = [2, 3, 4].into();
        assert_eq!(a.intersection(&b).count(), 2);
        assert_eq!(a.union(&b).count(), 4);
    }

    #[test]
    fn btreeset_order() {
        let s: BTreeSet<i32> = [5, 1, 3].into();
        let v: Vec<_> = s.iter().collect();
        assert_eq!(v, [&1, &3, &5]);
    }

    #[test]
    fn vecdeque_push_pop() {
        let mut d = VecDeque::new();
        d.push_back(1);
        d.push_back(2);
        d.push_front(0);
        assert_eq!(d.pop_front(), Some(0));
        assert_eq!(d.pop_back(), Some(2));
    }

    #[test]
    fn binary_heap() {
        let mut h = BinaryHeap::from([3, 1, 4, 1, 5]);
        assert_eq!(h.pop(), Some(5));
        assert_eq!(h.pop(), Some(4));
        assert_eq!(h.pop(), Some(3));
    }
}

#[cfg(test)]
mod strings {
    #[test]
    fn basic_ops() {
        let mut s = String::from("Hello");
        s.push_str(", World!");
        assert_eq!(s, "Hello, World!");
    }

    #[test]
    fn split_join() {
        let parts: Vec<&str> = "a,b,c".split(',').collect();
        assert_eq!(parts, ["a", "b", "c"]);
        assert_eq!(parts.join("-"), "a-b-c");
    }

    #[test]
    fn replace_trim() {
        assert_eq!("hello world hello".replace("hello", "hi"), "hi world hi");
        assert_eq!("  hi  ".trim(), "hi");
    }

    #[test]
    fn case_conversion() {
        assert_eq!("hello".to_uppercase(), "HELLO");
        assert_eq!("WORLD".to_lowercase(), "world");
    }

    #[test]
    fn search() {
        let s = "The quick brown fox";
        assert!(s.contains("quick"));
        assert!(s.starts_with("The"));
        assert!(s.ends_with("fox"));
    }

    #[test]
    fn unicode() {
        let s = "Héllo 你好 🎉";
        assert_eq!(s.chars().count(), 10);
        assert!(s.contains("你好"));
        assert!(s.contains("🎉"));
    }

    #[test]
    fn parse_display() {
        assert_eq!("42".parse::<i32>(), Ok(42));
        assert_eq!("3.14".parse::<f64>(), Ok(3.14));
        assert_eq!(42.to_string(), "42");
        assert_eq!(true.to_string(), "true");
    }
}

#[cfg(test)]
mod formatting {
    #[test]
    fn integers() {
        assert_eq!(format!("{}", 42), "42");
        assert_eq!(format!("{:05}", 42), "00042");
        assert_eq!(format!("{:x}", 255), "ff");
        assert_eq!(format!("{:o}", 8), "10");
        assert_eq!(format!("{:b}", 10), "1010");
        assert_eq!(format!("{:+}", 42), "+42");
    }

    #[test]
    fn floats() {
        assert_eq!(format!("{:.2}", 3.14159), "3.14");
        assert_eq!(format!("{:e}", 1000.0f64), "1e3");
        assert_eq!(format!("{:.0}", 1.5f64), "2");
    }

    #[test]
    fn padding() {
        assert_eq!(format!("{:>10}", "hi"), "        hi");
        assert_eq!(format!("{:<10}", "hi"), "hi        ");
        assert_eq!(format!("{:^10}", "hi"), "    hi    ");
        assert_eq!(format!("{:*^10}", "hi"), "****hi****");
    }

    #[test]
    fn debug_format() {
        assert_eq!(format!("{:?}", vec![1, 2, 3]), "[1, 2, 3]");
        assert_eq!(format!("{:?}", Some(42)), "Some(42)");
        assert_eq!(format!("{:?}", None::<i32>), "None");
    }
}

#[cfg(test)]
mod iterators {
    #[test]
    fn sum_collect() {
        let sum: i32 = (1..=100).sum();
        assert_eq!(sum, 5050);
    }

    #[test]
    fn filter_map() {
        let v: Vec<i32> = (1..=10).filter(|x| x % 2 == 0).map(|x| x * x).collect();
        assert_eq!(v, [4, 16, 36, 64, 100]);
    }

    #[test]
    fn fold() {
        let factorial = (1..=10).fold(1u64, |acc, x| acc * x);
        assert_eq!(factorial, 3628800);
    }

    #[test]
    fn zip_enumerate() {
        let zipped: Vec<_> = [1, 2].iter().zip(["a", "b"]).collect();
        assert_eq!(zipped, [(&1, "a"), (&2, "b")]);
        let enumd: Vec<_> = ["x", "y"].iter().enumerate().collect();
        assert_eq!(enumd, [(0, &"x"), (1, &"y")]);
    }

    #[test]
    fn chain_flat_map() {
        let chained: Vec<_> = [1, 2].iter().chain([3, 4].iter()).collect();
        assert_eq!(chained, [&1, &2, &3, &4]);
        let flat: Vec<_> = vec![vec![1, 2], vec![3]].into_iter().flatten().collect();
        assert_eq!(flat, [1, 2, 3]);
    }

    #[test]
    fn take_skip() {
        let v: Vec<i32> = (1..=10).skip(3).take(4).collect();
        assert_eq!(v, [4, 5, 6, 7]);
    }

    #[test]
    fn predicates() {
        let v = [2, 4, 6, 8];
        assert!(v.iter().all(|x| x % 2 == 0));
        assert!(v.iter().any(|x| *x > 5));
        assert!(!v.iter().any(|x| *x > 10));
    }

    #[test]
    fn min_max() {
        let v = [3, 1, 4, 1, 5, 9];
        assert_eq!(v.iter().min(), Some(&1));
        assert_eq!(v.iter().max(), Some(&9));
    }
}

#[cfg(test)]
mod option_result {
    #[test]
    fn option_combinators() {
        let x: Option<i32> = Some(42);
        assert_eq!(x.map(|v| v * 2), Some(84));
        assert_eq!(x.filter(|v| *v > 50), None);
        assert_eq!(x.and_then(|v| if v > 0 { Some(v) } else { None }), Some(42));
        assert_eq!(None::<i32>.unwrap_or(0), 0);
    }

    #[test]
    fn result_combinators() {
        let x: Result<i32, &str> = Ok(42);
        assert_eq!(x.map(|v| v * 2), Ok(84));
        assert_eq!(Err::<i32, _>("bad").unwrap_or(0), 0);
        assert_eq!(Err::<i32, _>("bad").err(), Some("bad"));
    }
}

#[cfg(test)]
mod smart_pointers {
    use std::sync::{Arc, Mutex, RwLock};
    use std::rc::Rc;
    use std::cell::{Cell, RefCell};

    #[test]
    fn box_basic() {
        let b = Box::new(42);
        assert_eq!(*b, 42);
        let v: Box<[i32]> = vec![1, 2, 3].into_boxed_slice();
        assert_eq!(&*v, &[1, 2, 3]);
    }

    #[test]
    fn rc_counting() {
        let a = Rc::new(42);
        let b = Rc::clone(&a);
        assert_eq!(Rc::strong_count(&a), 2);
        drop(b);
        assert_eq!(Rc::strong_count(&a), 1);
    }

    #[test]
    fn arc_mutex() {
        let data = Arc::new(Mutex::new(vec![1, 2, 3]));
        data.lock().unwrap().push(4);
        assert_eq!(*data.lock().unwrap(), [1, 2, 3, 4]);
    }

    #[test]
    fn rwlock() {
        let lock = RwLock::new(5);
        assert_eq!(*lock.read().unwrap(), 5);
        *lock.write().unwrap() = 10;
        assert_eq!(*lock.read().unwrap(), 10);
    }

    #[test]
    fn cell_refcell() {
        let c = Cell::new(5);
        c.set(10);
        assert_eq!(c.get(), 10);
        let r = RefCell::new(vec![1, 2]);
        r.borrow_mut().push(3);
        assert_eq!(r.borrow().len(), 3);
    }

    #[test]
    fn cow() {
        use std::borrow::Cow;
        let borrowed: Cow<str> = Cow::Borrowed("hello");
        assert_eq!(borrowed, "hello");
        let owned: Cow<str> = Cow::Owned("world".to_string());
        assert_eq!(owned, "world");
    }
}

#[cfg(test)]
mod concurrency {
    use std::sync::{Arc, Mutex, mpsc};

    #[test]
    fn thread_spawn_join() {
        let h = std::thread::spawn(|| 42);
        assert_eq!(h.join().unwrap(), 42);
    }

    #[test]
    fn thread_concurrent_counter() {
        let counter = Arc::new(Mutex::new(0i32));
        let handles: Vec<_> = (0..4).map(|_| {
            let c = Arc::clone(&counter);
            std::thread::spawn(move || {
                for _ in 0..250 {
                    *c.lock().unwrap() += 1;
                }
            })
        }).collect();
        for h in handles { h.join().unwrap(); }
        assert_eq!(*counter.lock().unwrap(), 1000);
    }

    #[test]
    fn mpsc_channel() {
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            for i in 0..10 { tx.send(i).unwrap(); }
        });
        let received: Vec<i32> = rx.iter().collect();
        assert_eq!(received, (0..10).collect::<Vec<_>>());
    }

    #[test]
    fn mpsc_sync_channel() {
        let (tx, rx) = mpsc::sync_channel(5);
        std::thread::spawn(move || {
            for i in 0..5 { tx.send(i).unwrap(); }
        });
        assert_eq!(rx.iter().sum::<i32>(), 10);
    }
}

#[cfg(test)]
mod io_fs {
    use std::io::{Read, Write, Cursor, BufRead, BufReader, BufWriter};
    use std::fs;

    #[test]
    fn cursor_read_write() {
        let mut buf = Cursor::new(Vec::new());
        buf.write_all(b"hello").unwrap();
        buf.set_position(0);
        let mut s = String::new();
        buf.read_to_string(&mut s).unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn file_read_write() {
        let path = "/tmp/tuffy_build_std_test_file.txt";
        fs::write(path, "hello from tuffy").unwrap();
        assert_eq!(fs::read_to_string(path).unwrap(), "hello from tuffy");
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn buffered_io() {
        let path = "/tmp/tuffy_build_std_test_buf.txt";
        {
            let f = fs::File::create(path).unwrap();
            let mut w = BufWriter::new(f);
            for i in 0..50 { writeln!(w, "line {i}").unwrap(); }
        }
        {
            let f = fs::File::open(path).unwrap();
            let lines: Vec<_> = BufReader::new(f).lines().map(|l| l.unwrap()).collect();
            assert_eq!(lines.len(), 50);
            assert_eq!(lines[25], "line 25");
        }
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn dir_operations() {
        let dir = "/tmp/tuffy_build_std_test_dir";
        fs::create_dir_all(dir).unwrap();
        fs::write(format!("{dir}/a.txt"), "a").unwrap();
        fs::write(format!("{dir}/b.txt"), "b").unwrap();
        assert_eq!(fs::read_dir(dir).unwrap().count(), 2);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn process_command() {
        use std::process::Command;
        let out = Command::new("echo").arg("hello").output().unwrap();
        assert!(out.status.success());
        assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "hello");
    }
}

#[cfg(test)]
mod panic_unwind {
    #[test]
    fn catch_unwind_ok() {
        let result = std::panic::catch_unwind(|| 42);
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn catch_unwind_panic() {
        let result = std::panic::catch_unwind(|| {
            panic!("intentional");
        });
        assert!(result.is_err());
    }
}

#[cfg(test)]
mod numerics {
    #[test]
    fn integer_ops() {
        assert_eq!(2i32.pow(10), 1024);
        assert_eq!(100i32.checked_add(i32::MAX), None);
        assert_eq!(255u8.saturating_add(10), 255);
        assert_eq!(10u32.checked_div(0), None);
    }

    #[test]
    fn float_math() {
        assert!((2.0f64.sqrt() - std::f64::consts::SQRT_2).abs() < 1e-10);
        assert!((std::f64::consts::PI.sin()).abs() < 1e-10);
        assert_eq!((-3.5f64).abs(), 3.5);
        assert_eq!(2.5f64.floor(), 2.0);
        assert_eq!(2.5f64.ceil(), 3.0);
    }

    #[test]
    fn float_special() {
        assert!(f64::NAN.is_nan());
        assert!(f64::INFINITY.is_infinite());
        assert!(!f64::INFINITY.is_nan());
    }
}

#[cfg(test)]
mod misc {
    use std::path::Path;
    use std::time::{Duration, Instant};

    #[test]
    fn path_ops() {
        let p = Path::new("/usr/local/bin/prog");
        assert_eq!(p.file_name().unwrap(), "prog");
        assert_eq!(p.parent().unwrap(), Path::new("/usr/local/bin"));
        let p2 = Path::new("file.txt");
        assert_eq!(p2.extension().unwrap(), "txt");
        assert_eq!(p2.file_stem().unwrap(), "file");
    }

    #[test]
    fn time_basics() {
        let d = Duration::from_millis(100);
        assert_eq!(d.as_millis(), 100);
        let now = Instant::now();
        std::thread::sleep(Duration::from_millis(10));
        assert!(now.elapsed() >= Duration::from_millis(5));
    }

    #[test]
    fn ranges() {
        assert!((0..5).contains(&3));
        assert!(!(0..5).contains(&5));
        assert!((0..=5).contains(&5));
    }

    #[test]
    fn trait_objects() {
        trait Speak { fn speak(&self) -> &str; }
        struct Dog;
        struct Cat;
        impl Speak for Dog { fn speak(&self) -> &str { "woof" } }
        impl Speak for Cat { fn speak(&self) -> &str { "meow" } }
        let animals: Vec<Box<dyn Speak>> = vec![Box::new(Dog), Box::new(Cat)];
        assert_eq!(animals[0].speak(), "woof");
        assert_eq!(animals[1].speak(), "meow");
    }

    #[test]
    fn closures_as_trait_objects() {
        let fns: Vec<Box<dyn Fn(i32) -> i32>> = vec![
            Box::new(|x| x + 1),
            Box::new(|x| x * 2),
        ];
        assert_eq!(fns[0](5), 6);
        assert_eq!(fns[1](5), 10);
    }

    #[test]
    fn from_into_conversions() {
        let v: Vec<u8> = String::from("hello").into_bytes();
        assert_eq!(v, b"hello");
        assert_eq!(String::from_utf8(v).unwrap(), "hello");
    }
}
RUSTEOF

# ── Run tests ─────────────────────────────────────────────────────────────────

echo "=== Build-Std Tests ==="
echo "Backend: $BACKEND"
echo "Work dir: $WORK_DIR"
echo ""

echo "Building std from source and running tests..."
set +e
test_output=$(
    RUSTFLAGS="-Z codegen-backend=$BACKEND -C opt-level=0" \
    cargo +$TOOLCHAIN test \
        --manifest-path "$WORK_DIR/Cargo.toml" \
        --target x86_64-unknown-linux-gnu \
        2>&1
)
test_rc=$?
set -e

echo "$test_output"
echo ""

# Parse results from cargo test output.
if [ $test_rc -ne 0 ]; then
    echo "=== Build-Std Tests: FAILED (exit code $test_rc) ==="
    exit 1
fi

# Extract the summary line (e.g., "test result: ok. 68 passed; 0 failed; ...")
result_line=$(echo "$test_output" | grep '^test result:' | tail -1)
if [ -z "$result_line" ]; then
    echo "=== Build-Std Tests: FAILED (no test result found) ==="
    exit 1
fi

echo "=== Build-Std Tests: $result_line ==="
