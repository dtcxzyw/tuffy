#!/bin/bash
# Run the Rust standard library unit tests (coretests, alloctests) compiled
# with the tuffy codegen backend.  Tests are sourced from the rustc nightly
# toolchain's rust-src component.
#
# Usage:
#   # Local (auto-discovers backend):
#   bash rustc_codegen_tuffy/tests/run-stdlib-tests.sh
#
#   # CI (explicit backend):
#   BACKEND=path/to/librustc_codegen_tuffy.so \
#     bash rustc_codegen_tuffy/tests/run-stdlib-tests.sh
#
# Requirements: rust-src component (rustup component add rust-src)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# ── Find backend .so ──────────────────────────────────────────────────────────

if [ -n "${BACKEND:-}" ]; then
    BACKEND="$(realpath "$BACKEND")"
elif [ -f "$CRATE_ROOT/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
elif [ -f "$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
else
    echo "ERROR: Backend not found."
    echo "Run: cd rustc_codegen_tuffy && cargo build --release"
    exit 1
fi

# ── Verify rust-src component ─────────────────────────────────────────────────

TOOLCHAIN="nightly-2026-03-28"
if ! rustup "+$TOOLCHAIN" component list --installed 2>/dev/null | grep -q rust-src; then
    echo "Installing rust-src component..."
    rustup "+$TOOLCHAIN" component add rust-src
fi

RUST_SYSROOT="$(rustc "+$TOOLCHAIN" --print sysroot)"
LIBRARY_DIR="$RUST_SYSROOT/lib/rustlib/src/rust/library"

if [ ! -d "$LIBRARY_DIR/coretests" ]; then
    echo "ERROR: coretests not found at $LIBRARY_DIR/coretests"
    echo "Ensure rust-src is installed: rustup +$TOOLCHAIN component add rust-src"
    exit 1
fi

# ── Clean previous build artifacts ────────────────────────────────────────────
# The library/target directory caches builds; remove it to pick up backend changes.

rm -rf "$LIBRARY_DIR/target"

echo "=== Stdlib Tests ==="
echo "Backend: $BACKEND"
echo "Library: $LIBRARY_DIR"
echo ""

export RUSTFLAGS="-Z codegen-backend=$BACKEND"

overall_rc=0

# ── Known slow tests to skip (hang with unoptimized builds) ───────────────────
# These tests operate on [(); usize::MAX] and take forever without optimizations,
# even with LLVM.  They are not tuffy-specific failures.
SKIP_SLOW="--skip split_off_first_empty --skip split_off_last_empty \
--skip split_off_first_mut_empty --skip split_off_last_mut_empty \
--skip split_off_oob_max --skip split_off_in_bounds_max \
--skip split_off_mut_oob_max --skip split_off_mut_in_bounds_max"

# ── Run coretests ─────────────────────────────────────────────────────────────

echo "--- coretests ---"
set +e
# shellcheck disable=SC2086
core_output=$(
    cargo "+$TOOLCHAIN" test \
        --manifest-path "$LIBRARY_DIR/coretests/Cargo.toml" \
        --test coretests \
        -- $SKIP_SLOW \
        2>&1
)
core_rc=$?
set -e

core_result=$(echo "$core_output" | grep '^test result:' | tail -1)
if [ $core_rc -ne 0 ]; then
    echo "$core_output" | tail -30
    echo ""
    echo "coretests: FAILED (exit code $core_rc)"
    overall_rc=1
else
    echo "$core_result"
fi
echo ""

# ── Run alloctests (lib) ──────────────────────────────────────────────────────

echo "--- alloctests (lib) ---"
set +e
alloclib_output=$(
    cargo "+$TOOLCHAIN" test \
        --manifest-path "$LIBRARY_DIR/alloctests/Cargo.toml" \
        --lib \
        2>&1
)
alloclib_rc=$?
set -e

alloclib_result=$(echo "$alloclib_output" | grep '^test result:' | tail -1)
if [ $alloclib_rc -ne 0 ]; then
    echo "$alloclib_output" | tail -30
    echo ""
    echo "alloctests (lib): FAILED (exit code $alloclib_rc)"
    overall_rc=1
else
    echo "$alloclib_result"
fi
echo ""

# ── Run alloctests (integration) ──────────────────────────────────────────────

echo "--- alloctests (integration) ---"
set +e
alloc_output=$(
    cargo "+$TOOLCHAIN" test \
        --manifest-path "$LIBRARY_DIR/alloctests/Cargo.toml" \
        --test alloctests \
        2>&1
)
alloc_rc=$?
set -e

alloc_result=$(echo "$alloc_output" | grep '^test result:' | tail -1)
if [ $alloc_rc -ne 0 ]; then
    echo "$alloc_output" | tail -30
    echo ""
    echo "alloctests (integration): FAILED (exit code $alloc_rc)"
    overall_rc=1
fi
echo ""

# ── Summary ───────────────────────────────────────────────────────────────────

echo "=== Stdlib Tests Summary ==="
echo "  coretests:               ${core_result:-FAILED}"
echo "  alloctests (lib):        ${alloclib_result:-FAILED}"
echo "  alloctests (integration):${alloc_result:-FAILED}"

if [ $overall_rc -ne 0 ]; then
    echo ""
    echo "=== Stdlib Tests: FAILED ==="
    exit 1
fi

echo ""
echo "=== Stdlib Tests: PASSED ==="
