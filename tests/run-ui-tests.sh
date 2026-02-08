#!/bin/bash
# Run rustc UI tests against tuffy codegen backend.
# Usage: ./tests/run-ui-tests.sh [rust-src-dir]
#
# Requires: scratch/rust/tests/ui/ (shallow clone of rust-lang/rust)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Find backend .so: env var > crate-local target > workspace target
# rustc_codegen_tuffy is excluded from the workspace, so prefer its own target dir.
if [ -n "${BACKEND:-}" ]; then
    :
elif [ -f "$REPO_ROOT/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$REPO_ROOT/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
elif [ -f "$REPO_ROOT/rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$REPO_ROOT/rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so"
else
    BACKEND="$REPO_ROOT/rustc_codegen_tuffy/target/debug/librustc_codegen_tuffy.so"
fi
UI_DIR="${1:-$REPO_ROOT/scratch/rust/tests/ui}"
EXCLUDE_FILE="$REPO_ROOT/tests/ui-exclude.txt"
OUT_DIR="/tmp/tuffy_ui_test"

mkdir -p "$OUT_DIR"

if [ ! -d "$UI_DIR" ]; then
    echo "ERROR: UI test directory not found: $UI_DIR"
    echo "Run: git clone --depth 1 --filter=blob:none --sparse https://github.com/rust-lang/rust.git scratch/rust"
    echo "     cd scratch/rust && git sparse-checkout set tests/ui"
    exit 1
fi

if [ ! -f "$BACKEND" ]; then
    echo "ERROR: Backend not found: $BACKEND"
    echo "Run: cd rustc_codegen_tuffy && cargo build"
    exit 1
fi

# Load exclusion list (strip comments and blank lines)
declare -A excluded
if [ -f "$EXCLUDE_FILE" ]; then
    while IFS= read -r line; do
        line="${line%%#*}"
        line="${line// /}"
        [ -z "$line" ] && continue
        excluded["$line"]=1
    done < "$EXCLUDE_FILE"
fi

pass=0; fail=0; skip=0; total=0
failures=""

# Find tests: no auxiliary dirs, sorted for determinism
mapfile -t tests < <(find "$UI_DIR" -name '*.rs' -not -path '*/auxiliary/*' | sort)

for test_file in "${tests[@]}"; do
    total=$((total + 1))
    rel_path="${test_file#$UI_DIR/}"

    # Check exclusion list
    if [ "${excluded[$rel_path]+_}" ]; then
        skip=$((skip + 1))
        continue
    fi

    # Skip tests with error annotations (expected-error tests)
    if grep -q '//~' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    # Skip tests needing features we can't handle
    if grep -qE '//@ (build-fail|run-fail|should-fail|ignore-|needs-asm|needs-llvm|needs-profiler|needs-sanitizer|only-windows|only-macos|only-aarch64|only-arm|only-32bit|revisions|compile-flags|aux-build|aux-crate)' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    # Try to compile with tuffy backend (disable errexit to capture exit code)
    set +e
    output=$(timeout 10 rustc --edition 2021 \
        -Z codegen-backend="$BACKEND" \
        --crate-type lib \
        -o "$OUT_DIR/test_out.rlib" \
        "$test_file" 2>&1)
    exit_code=$?
    set -e

    if [ $exit_code -eq 0 ]; then
        pass=$((pass + 1))
    else
        fail=$((fail + 1))
        failures="$failures\n  FAIL: $rel_path"
    fi

    if [ $((total % 500)) -eq 0 ]; then
        echo "[$total] pass=$pass fail=$fail skip=$skip"
    fi
done

echo ""
echo "=== UI Test Results ==="
echo "Total:   $total"
echo "Pass:    $pass"
echo "Fail:    $fail"
echo "Skip:    $skip"

if [ $fail -gt 0 ]; then
    echo ""
    echo "Failures:"
    echo -e "$failures"
    exit 1
fi
