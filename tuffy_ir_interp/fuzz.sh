#!/usr/bin/env bash
# Rustlantis fuzz script: generate seeds, compile with LLVM and tuffy,
# run through IR interpreter, and compare hash output.
#
# Usage: ./fuzz.sh [start] [end]
#   start: first seed (default 0)
#   end:   last seed inclusive (default 999)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
GENERATE="/tmp/rustlantis/target/release/generate"
TUFFY_SO="$REPO_ROOT/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
INTERP="$REPO_ROOT/target/release/tuffy-interp"
WORKDIR="/tmp/tuffy_fuzz"

START="${1:-0}"
END="${2:-999}"

mkdir -p "$WORKDIR"

pass=0
fail=0
skip=0
errors=""

for seed in $(seq "$START" "$END"); do
    src="$WORKDIR/seed${seed}.rs"
    ir="$WORKDIR/seed${seed}.tuffy"
    llvm_bin="$WORKDIR/seed${seed}_llvm"

    # Generate source (must run from rustlantis dir for config.toml)
    (cd /tmp/rustlantis && "$GENERATE" "$seed") > "$src" 2>/dev/null

    # Compile with LLVM and run to get expected output
    if ! rustc +nightly "$src" -o "$llvm_bin" 2>/dev/null; then
        skip=$((skip + 1))
        continue
    fi
    expected=$(timeout 10 "$llvm_bin" 2>/dev/null || true)

    # Compile with tuffy backend + dump-module
    if ! rustc +nightly "$src" -Z "codegen-backend=$TUFFY_SO" -C "llvm-args=dump-module=$ir" -o "$WORKDIR/seed${seed}_tuffy" 2>/dev/null; then
        skip=$((skip + 1))
        rm -f "$src" "$llvm_bin"
        continue
    fi
    rm -f "$WORKDIR/seed${seed}_tuffy"

    # Run through interpreter
    actual=$(timeout 30 "$INTERP" "$ir" 2>/dev/null || true)

    if [ "$expected" = "$actual" ]; then
        pass=$((pass + 1))
        # Clean up successful runs
        rm -f "$src" "$ir" "$llvm_bin"
    else
        fail=$((fail + 1))
        errors="${errors}SEED $seed: expected='$expected' actual='$actual'\n"
        echo "FAIL seed $seed: expected='$expected' actual='$actual'"
    fi

    # Progress every 50 seeds
    total=$((pass + fail + skip))
    if [ $((total % 50)) -eq 0 ]; then
        echo "[progress] seed $seed: $pass pass, $fail fail, $skip skip"
    fi
done

echo ""
echo "=== Results ==="
echo "Pass: $pass"
echo "Fail: $fail"
echo "Skip: $skip"
if [ -n "$errors" ]; then
    echo ""
    echo "Failures:"
    echo -e "$errors"
fi

exit $fail
