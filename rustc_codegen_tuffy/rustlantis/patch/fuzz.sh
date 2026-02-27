#!/bin/bash
# Batch rustlantis differential test script
# Usage: ./fuzz.sh <start_seed> <end_seed>
set -euo pipefail

CODEGEN="/tuffy/rustc_codegen_tuffy/target/release/librustc_codegen_tuffy.so"
START=${1:-1}
END=${2:-50}
PASS=0
FAIL=0
CRASH=0

for seed in $(seq $START $END); do
    src="/tmp/rl_fuzz_${seed}.rs"
    cd /tmp/rustlantis
    cargo run --release --bin generate -- "$seed" > "$src" 2>/dev/null

    # Compile with LLVM
    if ! rustc +nightly -Zmir-opt-level=0 -o "/tmp/rl_llvm_${seed}" "$src" 2>/dev/null; then
        echo "SKIP($seed): LLVM compile failed"
        continue
    fi

    # Compile with tuffy
    if ! rustc +nightly -Zmir-opt-level=0 -Zcodegen-backend="$CODEGEN" -o "/tmp/rl_tuffy_${seed}" "$src" 2>/dev/null; then
        echo "CRASH($seed): tuffy compile failed"
        CRASH=$((CRASH + 1))
        continue
    fi

    # Run both
    llvm_out=$(timeout 5 /tmp/rl_llvm_${seed} 2>&1 || true)
    tuffy_out=$(timeout 5 /tmp/rl_tuffy_${seed} 2>&1 || true)

    if [ "$llvm_out" = "$tuffy_out" ]; then
        PASS=$((PASS + 1))
    else
        echo "MISMATCH($seed):"
        echo "  LLVM:  $llvm_out"
        echo "  TUFFY: $tuffy_out"
        FAIL=$((FAIL + 1))
    fi

    # Cleanup
    rm -f "$src" "/tmp/rl_llvm_${seed}" "/tmp/rl_tuffy_${seed}"
done

echo ""
echo "Results: PASS=$PASS FAIL=$FAIL CRASH=$CRASH (seeds $START..$END)"
