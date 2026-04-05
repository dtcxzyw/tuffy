#!/bin/bash
# Unified quick build-and-test script for rustc_codegen_tuffy.
# Runs: smoke tests (hello world + fixture programs) and codegen CHECK tests.
# Third-party crate tests (bitflags, syn) are in run-crate-tests.sh.
#
# Temporary output: scratch/rustc_codegen_tuffy_test/ (cleared before each run).
# Abort on unset variables; propagate pipeline failures.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_ROOT/.." && pwd)"
TEMP_DIR="$REPO_ROOT/scratch/rustc_codegen_tuffy_test"

# Clear and recreate temp directory for a clean run.
rm -rf "$TEMP_DIR"
mkdir -p "$TEMP_DIR"

overall_pass=0
overall_fail=0

# ── Build ─────────────────────────────────────────────────────────────────────

if [ -n "${BACKEND:-}" ]; then
    echo "=== Using pre-built backend ==="
else
    echo "=== Build ==="
    cargo build --manifest-path "$CRATE_ROOT/Cargo.toml"
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
fi

if [ ! -f "$BACKEND" ]; then
    echo "ERROR: Backend not found at $BACKEND"
    exit 1
fi

echo "Backend: $BACKEND"
echo ""

# ── Smoke tests (hello world + fixture programs) ──────────────────────────────

echo "=== Smoke Tests ==="
mkdir -p "$TEMP_DIR/run-tests"
if BACKEND="$BACKEND" OUT_DIR="$TEMP_DIR/run-tests" bash "$SCRIPT_DIR/run-tests.sh"; then
    overall_pass=$((overall_pass + 1))
else
    overall_fail=$((overall_fail + 1))
fi
echo ""

# ── Codegen CHECK tests ───────────────────────────────────────────────────────

echo "=== Codegen CHECK Tests ==="
mkdir -p "$TEMP_DIR/codegen"
if BACKEND="$BACKEND" OUT_DIR="$TEMP_DIR/codegen" bash "$SCRIPT_DIR/run-codegen-tests.sh"; then
    overall_pass=$((overall_pass + 1))
else
    overall_fail=$((overall_fail + 1))
fi
echo ""

# ── Summary ───────────────────────────────────────────────────────────────────

echo "=== Quick Tests Summary: $overall_pass sections passed, $overall_fail sections failed ==="
if [ $overall_fail -gt 0 ]; then
    exit 1
fi
