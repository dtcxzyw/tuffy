#!/bin/bash
# Run rustc UI tests against tuffy codegen backend.
# Usage: ./rustc_codegen_tuffy/tests/run-ui-tests.sh [options] [rust-src-dir]
#
# Options:
#   --fail-fast       Stop at first failure
#   --shuffle         Randomize test order (default: sorted for determinism)
#
# Requires: scratch/rust/tests/ui/ (shallow clone of rust-lang/rust)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_ROOT/.." && pwd)"

# Options
FAIL_FAST="${FAIL_FAST:-0}"
SHUFFLE=0
UI_DIR_ARG=""
for arg in "$@"; do
    case "$arg" in
        --fail-fast) FAIL_FAST=1 ;;
        --shuffle)   SHUFFLE=1 ;;
        *)           UI_DIR_ARG="$arg" ;;
    esac
done

# Find backend .so: env var > crate-local target > workspace target
# rustc_codegen_tuffy is excluded from the workspace, so prefer its own target dir.
if [ -n "${BACKEND:-}" ]; then
    :
elif [ -f "$CRATE_ROOT/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
elif [ -f "$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
else
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
fi
UI_DIR="${UI_DIR_ARG:-$REPO_ROOT/scratch/rust/tests/ui}"
EXCLUDE_FILE="$CRATE_ROOT/tests/ui-exclude.txt"
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
panic_count=0
failures=""
panics=""

# Find tests: no auxiliary dirs
if [ "$SHUFFLE" -eq 1 ]; then
    mapfile -t tests < <(find "$UI_DIR" -name '*.rs' -not -path '*/auxiliary/*' | shuf)
else
    mapfile -t tests < <(find "$UI_DIR" -name '*.rs' -not -path '*/auxiliary/*' | sort)
fi

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
    if grep -qE '//@ (build-fail|run-fail|should-fail|ignore-|needs-asm|needs-llvm|needs-profiler|needs-sanitizer|needs-threads|needs-unwind|needs-run-enabled|only-windows|only-macos|only-apple|only-aarch64|only-arm|only-32bit|only-wasm|only-nvptx|only-dist|only-riscv|only-loongarch|only-mips|only-cdb|only-gdb|revisions|aux-build|aux-crate|aux-bin|proc-macro|add-minicore|known-bug|check-run-results)' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    # Skip tests whose compile-flags conflict with --crate-type lib or
    # require infrastructure the runner doesn't provide.
    if grep -qE '//@ compile-flags:.*(\-\-test|--error-format|--json|--emit=metadata|--env-set|--extern|\{\{|-lstatic|-lrust)' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    # Parse //@ edition: directive (default: 2021)
    edition="2021"
    edition_line=$(grep -m1 '^//@ edition:' "$test_file" 2>/dev/null || true)
    if [ -n "$edition_line" ]; then
        edition=$(echo "$edition_line" | sed 's|^//@ edition: *||' | tr -d '[:space:]')
        # Handle edition ranges like "2015.." or "2018.." — use the base edition.
        edition="${edition%%\.\.*}"
    fi

    # Parse //@ compile-flags: directive
    compile_flags=""
    while IFS= read -r flag_line; do
        flags=$(echo "$flag_line" | sed 's|^//@ compile-flags: *||')
        compile_flags="$compile_flags $flags"
    done < <(grep '^//@ compile-flags:' "$test_file" 2>/dev/null || true)

    # Try to compile with tuffy backend (disable errexit to capture exit code)
    set +e
    output=$(timeout 120 rustc --edition "$edition" \
        -Z codegen-backend="$BACKEND" \
        --crate-type lib \
        -o "$OUT_DIR/test_out.rlib" \
        $compile_flags \
        "$test_file" 2>&1)
    exit_code=$?
    set -e

    if [ $exit_code -eq 0 ]; then
        pass=$((pass + 1))
    else
        # Classify failure: tuffy panic vs expected compilation error
        if echo "$output" | grep -q 'thread.*panicked\|internal compiler error\|SIGABRT\|SIGSEGV'; then
            panic_count=$((panic_count + 1))
            panics="$panics\n  PANIC: $rel_path"
        fi
        fail=$((fail + 1))
        failures="$failures\n  FAIL: $rel_path"
        if [ "$FAIL_FAST" -eq 1 ]; then
            echo "FAIL: $rel_path"
            echo "$output"
            echo ""
            echo "Stopping at first failure (--fail-fast)."
            exit 1
        fi
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
echo "  Panics:  $panic_count"
echo "  Other:   $((fail - panic_count))"
echo "Skip:    $skip"

if [ $panic_count -gt 0 ]; then
    echo ""
    echo "Tuffy panics (bugs):"
    echo -e "$panics"
fi

if [ $fail -gt 0 ]; then
    echo ""
    echo "All failures:"
    echo -e "$failures"
    exit 1
fi
