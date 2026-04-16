#!/bin/bash
# Compile and run hello world with the tuffy codegen backend.
# Verifies that println!("Hello, world!") produces correct output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TOOLCHAIN="${TOOLCHAIN:-nightly-2026-03-28}"
export RUSTUP_TOOLCHAIN="$TOOLCHAIN"

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
OUT_DIR="${OUT_DIR:-/tmp/tuffy_hello_test}"
mkdir -p "$OUT_DIR"

pass=0
fail=0

run_test() {
    local name="$1"
    local src="$2"
    local expected="$3"

    echo -n "  $name ... "

    local compile_flags=""
    if grep -q "^// compile-flags:" "$src"; then
        compile_flags=$(grep "^// compile-flags:" "$src" | head -1 | sed 's|^// compile-flags:||')
    fi

    # Compile
    if ! rustc -Z codegen-backend="$BACKEND" \
        $compile_flags \
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
run_test "umul_overflow_64" "$FIXTURE_DIR/umul_overflow_64.rs" "ok"
run_test "smul_overflow_128" "$FIXTURE_DIR/smul_overflow_128.rs" "ok"
run_test "shl_truncation" "$FIXTURE_DIR/shl_truncation.rs" "ok"
run_test "signed_cmp_narrow" "$FIXTURE_DIR/signed_cmp_narrow.rs" "ok"
run_test "funnel_shift_narrow" "$FIXTURE_DIR/funnel_shift_narrow.rs" "ok"
run_test "const_generic_repeat" "$FIXTURE_DIR/const_generic_repeat.rs" "ok"
run_test "fat_ptr_field_assign" "$FIXTURE_DIR/fat_ptr_field_assign.rs" "b"
run_test "stack_thin_to_slice_unsize" "$FIXTURE_DIR/stack_thin_to_slice_unsize.rs" "ok"
run_test "const_slice_of_str_refs" "$FIXTURE_DIR/const_slice_of_str_refs.rs" "ok"
run_test "trait_object_branch_vtable" "$FIXTURE_DIR/trait_object_branch_vtable.rs" "ok"
run_test "aggregate_eq_cfg" "$FIXTURE_DIR/aggregate_eq_cfg.rs" "ok"
run_test "array_iter_enumerate" "$FIXTURE_DIR/array_iter_enumerate.rs" "ok"
run_test "catch_unwind_call_cleanup" "$FIXTURE_DIR/catch_unwind_call_cleanup.rs" "ok"
run_test "alloc_result_fat_ptr" "$FIXTURE_DIR/alloc_result_fat_ptr.rs" "ok"
run_test "const_fn_unsize" "$FIXTURE_DIR/const_fn_unsize.rs" "ok"
run_test "never_result" "$FIXTURE_DIR/never_result.rs" "ok"
run_test "raw_slice_ptr_hash" "$FIXTURE_DIR/raw_slice_ptr_hash.rs" "ok"
run_test "thread_spawn" "$FIXTURE_DIR/thread_spawn.rs" "ok"
run_test "box_dyn_from_raw" "$FIXTURE_DIR/box_dyn_from_raw.rs" "ok"
run_test "generic_fat_field" "$FIXTURE_DIR/generic_fat_field.rs" "9"
run_test "zst_closure_rust_call" "$FIXTURE_DIR/zst_closure_rust_call.rs" "foobar"

echo ""
echo "=== Results: $pass passed, $fail failed ==="

if [ $fail -gt 0 ]; then
    exit 1
fi
