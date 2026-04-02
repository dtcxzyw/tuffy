#!/bin/bash
# Unified quick build-and-test script for rustc_codegen_tuffy.
# Runs: smoke tests (hello world + fixture programs), codegen CHECK tests,
# bitflags cargo test, and syn cargo test (building each with the tuffy backend).
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

echo "=== Build ==="
cargo build --manifest-path "$CRATE_ROOT/Cargo.toml"

BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
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

# ── Bitflags cargo test ───────────────────────────────────────────────────────
# Uses global RUSTFLAGS so that ALL crates — target crates, build scripts, and
# proc-macros — are compiled with the tuffy backend.  Only the pre-built std
# library (from the sysroot) uses LLVM.

BITFLAGS_DIR="$REPO_ROOT/scratch/bitflags"
if [ -d "$BITFLAGS_DIR" ]; then
    echo "=== Bitflags cargo test ==="

    mkdir -p "$BITFLAGS_DIR/.cargo"
    cat > "$BITFLAGS_DIR/.cargo/config.toml" <<CFGEOF
[build]
rustflags = ["-Z", "codegen-backend=$BACKEND"]
CFGEOF

    if cargo +nightly-2026-03-28 test --manifest-path "$BITFLAGS_DIR/Cargo.toml"; then
        overall_pass=$((overall_pass + 1))
    else
        overall_fail=$((overall_fail + 1))
    fi
    echo ""
else
    echo "=== Bitflags cargo test: SKIP (scratch/bitflags not found) ==="
    echo ""
fi

# ── Syn cargo test ────────────────────────────────────────────────────────────
# syn is a widely-used parser crate. Because many proc-macros depend on syn
# from crates.io, TUFFY_SRC_DIR restricts the tuffy backend to the workspace
# copy of syn (prevents applying tuffy to the registry copy used by proc-macros).

SYN_DIR="$REPO_ROOT/scratch/syn"
if [ -d "$SYN_DIR" ]; then
    echo "=== Syn cargo test ==="

    WRAPPER_EXEC="$TEMP_DIR/rustc-wrapper-tuffy"
    if [ ! -f "$WRAPPER_EXEC" ]; then
        cp "$SCRIPT_DIR/rustc-wrapper-tuffy.sh" "$WRAPPER_EXEC"
        python3 -c "import os; os.chmod('$WRAPPER_EXEC', 0o755)"
    fi

    if RUSTC_WRAPPER="$WRAPPER_EXEC" \
       TUFFY_BACKEND="$BACKEND" \
       TUFFY_CRATE="syn" \
       TUFFY_SRC_DIR="$SYN_DIR" \
       cargo test --manifest-path "$SYN_DIR/Cargo.toml" --all-features; then
        overall_pass=$((overall_pass + 1))
    else
        overall_fail=$((overall_fail + 1))
    fi
    echo ""
else
    echo "=== Syn cargo test: SKIP (scratch/syn not found) ==="
    echo ""
fi

# ── Summary ───────────────────────────────────────────────────────────────────

echo "=== Quick Tests Summary: $overall_pass sections passed, $overall_fail sections failed ==="
if [ $overall_fail -gt 0 ]; then
    exit 1
fi
