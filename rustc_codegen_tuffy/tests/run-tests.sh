#!/bin/bash
# Compile and run hello world with the tuffy codegen backend.
# Verifies that println!("Hello, world!") produces correct output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Find backend .so
if [ -n "${BACKEND:-}" ]; then
    :
elif [ -f "$CRATE_ROOT/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
elif [ -f "$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
else
    echo "ERROR: Backend not found."
    echo "Run: cd rustc_codegen_tuffy && cargo build"
    exit 1
fi

FIXTURE_DIR="$CRATE_ROOT/tests/fixtures"
OUT_DIR="/tmp/tuffy_hello_test"
mkdir -p "$OUT_DIR"

pass=0
fail=0

run_test() {
    local name="$1"
    local src="$2"
    local expected="$3"

    echo -n "  $name ... "

    # Compile
    if ! rustc +nightly -Z codegen-backend="$BACKEND" \
        -o "$OUT_DIR/$name" "$src" 2>"$OUT_DIR/$name.compile.log"; then
        echo "FAIL (compile)"
        echo "    $(cat "$OUT_DIR/$name.compile.log")"
        fail=$((fail + 1))
        return
    fi

    # Run
    set +e
    actual=$(timeout 10 "$OUT_DIR/$name" 2>&1)
    exit_code=$?
    set -e

    if [ $exit_code -ne 0 ]; then
        echo "FAIL (exit code $exit_code)"
        fail=$((fail + 1))
        return
    fi

    if [ "$actual" != "$expected" ]; then
        echo "FAIL (output mismatch)"
        echo "    expected: $expected"
        echo "    actual:   $actual"
        fail=$((fail + 1))
        return
    fi

    echo "ok"
    pass=$((pass + 1))
}

echo "=== Run Tests ==="
echo "Backend: $BACKEND"
echo ""

run_test "hello" "$FIXTURE_DIR/hello.rs" "Hello, world!"

echo ""
echo "=== Results: $pass passed, $fail failed ==="

if [ $fail -gt 0 ]; then
    exit 1
fi
