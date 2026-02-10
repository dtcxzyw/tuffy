#!/bin/bash
# Run-pass tests: compile as binary, link, and execute.
# Usage: ./rustc_codegen_tuffy/tests/run-pass-tests.sh [rust-src-dir]
#
# Tests must have `fn main()`, no error annotations, and no special directives.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_ROOT/.." && pwd)"

# Options
FAIL_FAST="${FAIL_FAST:-0}"
UI_DIR_ARG=""
for arg in "$@"; do
    if [ "$arg" = "--fail-fast" ]; then
        FAIL_FAST=1
    else
        UI_DIR_ARG="$arg"
    fi
done

# Find backend .so
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
EXCLUDE_FILE="$CRATE_ROOT/tests/run-pass-exclude.txt"
OUT_DIR="/tmp/tuffy_run_pass"
LOG_DIR="$OUT_DIR/logs"

mkdir -p "$OUT_DIR" "$LOG_DIR"

if [ ! -d "$UI_DIR" ]; then
    echo "ERROR: UI test directory not found: $UI_DIR"
    exit 1
fi

if [ ! -f "$BACKEND" ]; then
    echo "ERROR: Backend not found: $BACKEND"
    echo "Run: cd rustc_codegen_tuffy && cargo build --release"
    exit 1
fi

# Load exclusion list
declare -A excluded
if [ -f "$EXCLUDE_FILE" ]; then
    while IFS= read -r line; do
        line="${line%%#*}"
        line="${line// /}"
        [ -z "$line" ] && continue
        excluded["$line"]=1
    done < "$EXCLUDE_FILE"
fi

pass=0; fail_compile=0; fail_link=0; fail_run=0; skip=0; total=0
compile_failures=""
link_failures=""
run_failures=""

# Find tests with fn main(), no auxiliary dirs, sorted
mapfile -t tests < <(find "$UI_DIR" -name '*.rs' -not -path '*/auxiliary/*' \
    -exec grep -l 'fn main()' {} + 2>/dev/null | sort)

for test_file in "${tests[@]}"; do
    total=$((total + 1))
    rel_path="${test_file#$UI_DIR/}"

    # Check exclusion list
    if [ "${excluded[$rel_path]+_}" ]; then
        skip=$((skip + 1))
        continue
    fi

    # Skip tests with error annotations
    if grep -q '//~' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    # Skip tests needing features we can't handle
    if grep -qE '//@ (build-fail|run-fail|should-fail|ignore-|needs-asm|needs-llvm|needs-profiler|needs-sanitizer|only-windows|only-macos|only-aarch64|only-arm|only-32bit|revisions|compile-flags|aux-build|aux-crate)' "$test_file" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi

    bin_path="$OUT_DIR/test_bin"
    rm -f "$bin_path"

    # Step 1: Compile and link as binary
    set +e
    compile_out=$(timeout 30 rustc --edition 2021 \
        -Z codegen-backend="$BACKEND" \
        -o "$bin_path" \
        "$test_file" 2>&1)
    compile_rc=$?
    set -e

    if [ $compile_rc -ne 0 ]; then
        # Distinguish compile vs link failures
        if echo "$compile_out" | grep -q 'linking with.*failed'; then
            fail_link=$((fail_link + 1))
            link_failures="$link_failures\n  LINK: $rel_path"
            echo "$compile_out" > "$LOG_DIR/${rel_path//\//__}.link.log"
        else
            fail_compile=$((fail_compile + 1))
            compile_failures="$compile_failures\n  COMPILE: $rel_path"
            echo "$compile_out" > "$LOG_DIR/${rel_path//\//__}.compile.log"
        fi
        if [ "$FAIL_FAST" -eq 1 ]; then
            echo "FAIL: $rel_path"
            echo "$compile_out"
            exit 1
        fi
        continue
    fi

    # Step 2: Execute the binary
    set +e
    run_out=$(timeout 10 "$bin_path" 2>&1)
    run_rc=$?
    set -e

    if [ $run_rc -ne 0 ]; then
        fail_run=$((fail_run + 1))
        run_failures="$run_failures\n  RUN($run_rc): $rel_path"
        echo "$run_out" > "$LOG_DIR/${rel_path//\//__}.run.log"
        if [ "$FAIL_FAST" -eq 1 ]; then
            echo "FAIL (run, exit=$run_rc): $rel_path"
            echo "$run_out"
            exit 1
        fi
    else
        pass=$((pass + 1))
    fi

    tested=$((pass + fail_compile + fail_link + fail_run))
    if [ $((tested % 100)) -eq 0 ]; then
        echo "[$total] pass=$pass compile_fail=$fail_compile link_fail=$fail_link run_fail=$fail_run skip=$skip"
    fi
done

echo ""
echo "=== Run-Pass Test Results ==="
echo "Total:        $total"
echo "Pass:         $pass"
echo "Compile fail: $fail_compile"
echo "Link fail:    $fail_link"
echo "Run fail:     $fail_run"
echo "Skip:         $skip"

if [ $fail_compile -gt 0 ]; then
    echo ""
    echo "Compile failures:"
    echo -e "$compile_failures"
fi

if [ $fail_link -gt 0 ]; then
    echo ""
    echo "Link failures:"
    echo -e "$link_failures"
fi

if [ $fail_run -gt 0 ]; then
    echo ""
    echo "Run failures:"
    echo -e "$run_failures"
fi
