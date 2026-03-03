#!/bin/bash
# Run codegen tests with CHECK annotations.
# Verifies that generated tuffy IR matches expected patterns.

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

CODEGEN_DIR="$CRATE_ROOT/tests/codegen"
OUT_DIR="/tmp/tuffy_codegen_test"
mkdir -p "$OUT_DIR"

pass=0
fail=0

run_codegen_test() {
    local src="$1"
    local name=$(basename "$src" .rs)

    echo -n "  $name ... "

    # Parse compile-flags
    local compile_flags=""
    if grep -q "^// compile-flags:" "$src"; then
        compile_flags=$(grep "^// compile-flags:" "$src" | head -1 | sed 's|^// compile-flags:||')
    fi

    # Extract CHECK lines
    local check_lines=()
    while IFS= read -r line; do
        check_lines+=("$line")
    done < <(grep "^// CHECK:" "$src" | sed 's|^// CHECK: ||')

    if [ ${#check_lines[@]} -eq 0 ]; then
        echo "SKIP (no CHECK lines)"
        return
    fi

    # Compile and capture IR
    local ir_output="$OUT_DIR/$name.ir"
    if ! rustc +nightly -Z codegen-backend="$BACKEND" \
        -C llvm-args=dump-ir $compile_flags \
        --crate-name "$name" \
        "$src" 2>"$ir_output"; then
        echo "FAIL (compile error)"
        cat "$ir_output"
        fail=$((fail + 1))
        return
    fi

    # Verify CHECK lines (exact string match)
    for check_pattern in "${check_lines[@]}"; do
        if ! grep -qF "$check_pattern" "$ir_output"; then
            echo "FAIL (missing pattern)"
            echo "    expected: $check_pattern"
            echo "    IR output:"
            cat "$ir_output" | head -20
            fail=$((fail + 1))
            return
        fi
    done

    echo "ok"
    pass=$((pass + 1))
}

echo "=== Codegen Tests ==="
echo "Backend: $BACKEND"
echo ""

# Run all tests in codegen directory (recursive)
while IFS= read -r test_file; do
    run_codegen_test "$test_file"
done < <(find "$CODEGEN_DIR" -name "*.rs" -type f | sort)

echo ""
echo "=== Results: $pass passed, $fail failed ==="

if [ $fail -gt 0 ]; then
    exit 1
fi
