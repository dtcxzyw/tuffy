#!/bin/bash
# Batch rustlantis differential test script with parallel execution
# Usage: ./fuzz.sh <start_seed> <end_seed> [jobs]
set -euo pipefail

CODEGEN="/tuffy/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
START=${1:-1}
END=${2:-50}
JOBS=${3:-$(nproc)}

test_seed() {
    local seed=$1
    local src="/tmp/rl_fuzz_${seed}.rs"

    cd /tmp/rustlantis
    cargo run --release --bin generate -- "$seed" > "$src" 2>/dev/null

    # Compile with LLVM
    if ! rustc +nightly -Zmir-opt-level=3 -C debug-assertions=off -C opt-level=3 -o "/tmp/rl_llvm_${seed}" "$src" 2>/dev/null; then
        echo "SKIP:$seed"
        rm -f "$src"
        return
    fi

    # Compile with tuffy
    if ! rustc +nightly -Zmir-opt-level=3 -C debug-assertions=off -C opt-level=3 -Zcodegen-backend="$CODEGEN" -o "/tmp/rl_tuffy_${seed}" "$src" 2>/dev/null; then
        echo "CRASH:$seed"
        rm -f "$src" "/tmp/rl_llvm_${seed}"
        return
    fi

    # Run both
    llvm_out=$(timeout 5 /tmp/rl_llvm_${seed} 2>&1 || true)
    tuffy_out=$(timeout 5 /tmp/rl_tuffy_${seed} 2>&1 || true)

    if [ "$llvm_out" = "$tuffy_out" ]; then
        echo "PASS:$seed"
    else
        echo "MISMATCH:$seed:$llvm_out:$tuffy_out"
    fi

    # Cleanup
    rm -f "$src" "/tmp/rl_llvm_${seed}" "/tmp/rl_tuffy_${seed}"
}

export -f test_seed
export CODEGEN

# Run tests in parallel
results=$(seq $START $END | xargs -P "$JOBS" -I {} bash -c 'test_seed {}')

# Aggregate results
PASS=$(echo "$results" | grep -c "^PASS:" || true)
FAIL=$(echo "$results" | grep -c "^MISMATCH:" || true)
CRASH=$(echo "$results" | grep -c "^CRASH:" || true)

# Print mismatches
echo "$results" | grep "^MISMATCH:" | while IFS=: read -r status seed llvm tuffy; do
    echo "MISMATCH($seed):"
    echo "  LLVM:  $llvm"
    echo "  TUFFY: $tuffy"
done

echo ""
echo "Results: PASS=$PASS FAIL=$FAIL CRASH=$CRASH (seeds $START..$END, $JOBS jobs)"
