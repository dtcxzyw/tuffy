#!/bin/bash
# Third-party crate tests for rustc_codegen_tuffy.
# Runs: bitflags cargo test, syn cargo test, and hashbrown release-focused tests
# (building each with the tuffy backend).
# These are separated from run-quick-tests.sh because they are slow.
#
# Temporary output: scratch/rustc_codegen_tuffy_test/ (cleared before each run).
# Abort on unset variables; propagate pipeline failures.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$CRATE_ROOT/.." && pwd)"
TEMP_DIR="$REPO_ROOT/scratch/rustc_codegen_tuffy_test"

mkdir -p "$TEMP_DIR"

overall_pass=0
overall_fail=0
RUST_NIGHTLY="${TUFFY_CRATE_TEST_TOOLCHAIN:-nightly-2026-03-28}"

# ── Build ─────────────────────────────────────────────────────────────────────

if [ -n "${BACKEND:-}" ]; then
    echo "=== Using pre-built backend ==="
else
    echo "=== Build ==="
    cargo +"$RUST_NIGHTLY" build --manifest-path "$CRATE_ROOT/Cargo.toml" --release
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
fi

if [ ! -f "$BACKEND" ]; then
    echo "ERROR: Backend not found at $BACKEND"
    exit 1
fi

BACKEND="$(realpath "$BACKEND")"

echo "Backend: $BACKEND"
echo ""

# ── Bitflags cargo test ───────────────────────────────────────────────────────
# Uses global RUSTFLAGS so that ALL crates — target crates, build scripts, and
# proc-macros — are compiled with the tuffy backend.  Only the pre-built std
# library (from the sysroot) uses LLVM.

BITFLAGS_DIR="$REPO_ROOT/scratch/bitflags"
if [ ! -d "$BITFLAGS_DIR" ]; then
    echo "=== Cloning bitflags ==="
    git clone --filter=blob:none https://github.com/bitflags/bitflags.git "$BITFLAGS_DIR"
fi
# Ensure the package has its own [workspace] so Cargo doesn't try to join
# the parent tuffy workspace (upstream bitflags doesn't define one).
if ! grep -q '^\[workspace\]' "$BITFLAGS_DIR/Cargo.toml"; then
    printf '\n[workspace]\n' >> "$BITFLAGS_DIR/Cargo.toml"
fi
echo "=== Bitflags cargo test ==="

mkdir -p "$BITFLAGS_DIR/.cargo"
cat > "$BITFLAGS_DIR/.cargo/config.toml" <<CFGEOF
[build]
rustflags = ["-Z", "codegen-backend=$BACKEND"]
CFGEOF

if cargo +"$RUST_NIGHTLY" test --manifest-path "$BITFLAGS_DIR/Cargo.toml"; then
    overall_pass=$((overall_pass + 1))
else
    overall_fail=$((overall_fail + 1))
fi
echo ""

# ── Syn cargo test ────────────────────────────────────────────────────────────
# syn is a widely-used parser crate. Because many proc-macros depend on syn
# from crates.io, TUFFY_SRC_DIR restricts the tuffy backend to the workspace
# copy of syn (prevents applying tuffy to the registry copy used by proc-macros).
# The checkout is pinned and patched because nightly-2026-03-28 changed
# rustc_ast::UseTree in a way that breaks syn's floating test-suite snapshots.

SYN_DIR="$REPO_ROOT/scratch/syn"
SYN_REV="ae257c4e05a338f73655aa1fa3d144e047daccf1"
SYN_PATCH="$SCRIPT_DIR/patches/syn-nightly-2026-03-28.patch"
if [ ! -d "$SYN_DIR" ]; then
    echo "=== Cloning syn ==="
    git clone --filter=blob:none https://github.com/dtolnay/syn.git "$SYN_DIR"
fi
if ! git -C "$SYN_DIR" cat-file -e "$SYN_REV^{commit}" 2>/dev/null; then
    git -C "$SYN_DIR" fetch --filter=blob:none origin "$SYN_REV"
fi
git -C "$SYN_DIR" checkout --force "$SYN_REV"
git -C "$SYN_DIR" apply "$SYN_PATCH"
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
   cargo +"$RUST_NIGHTLY" test --manifest-path "$SYN_DIR/Cargo.toml" --all-features; then
    overall_pass=$((overall_pass + 1))
else
    overall_fail=$((overall_fail + 1))
fi
echo ""

# ── Hashbrown release-focused tests ───────────────────────────────────────────
# Use an isolated working copy under TEMP_DIR and give it its own [workspace]
# so Cargo doesn't try to inherit the parent tuffy workspace.

HASHBROWN_SRC="$REPO_ROOT/scratch/hashbrown"
if [ ! -d "$HASHBROWN_SRC" ]; then
    echo "=== Cloning hashbrown ==="
    git clone --filter=blob:none https://github.com/rust-lang/hashbrown.git "$HASHBROWN_SRC"
fi
HASHBROWN_DIR="$TEMP_DIR/hashbrown-tuffy-work"
HASHBROWN_TARGET_DIR="$TEMP_DIR/hashbrown-tuffy-target"
rm -rf "$HASHBROWN_DIR" "$HASHBROWN_TARGET_DIR"
cp -a "$HASHBROWN_SRC" "$HASHBROWN_DIR"
# Ensure the working copy has its own [workspace] so Cargo doesn't try to join
# the parent tuffy workspace.
if ! grep -q '^\[workspace\]' "$HASHBROWN_DIR/Cargo.toml"; then
    printf '\n[workspace]\n' >> "$HASHBROWN_DIR/Cargo.toml"
fi

echo "=== Hashbrown release-focused tests ==="
if CARGO_TARGET_DIR="$HASHBROWN_TARGET_DIR" \
   RUSTFLAGS="-Zcodegen-backend=$BACKEND" \
   RUSTDOCFLAGS="-Zcodegen-backend=$BACKEND" \
   cargo +"$RUST_NIGHTLY" build --manifest-path "$HASHBROWN_DIR/Cargo.toml" --target x86_64-unknown-linux-gnu --no-default-features \
   && CARGO_TARGET_DIR="$HASHBROWN_TARGET_DIR" \
      RUSTFLAGS="-Zcodegen-backend=$BACKEND" \
      RUSTDOCFLAGS="-Zcodegen-backend=$BACKEND" \
      cargo +"$RUST_NIGHTLY" build --manifest-path "$HASHBROWN_DIR/Cargo.toml" --target x86_64-unknown-linux-gnu --release --no-default-features \
   && CARGO_TARGET_DIR="$HASHBROWN_TARGET_DIR" \
      RUSTFLAGS="-Zcodegen-backend=$BACKEND" \
      RUSTDOCFLAGS="-Zcodegen-backend=$BACKEND" \
      cargo +"$RUST_NIGHTLY" test --manifest-path "$HASHBROWN_DIR/Cargo.toml" --target x86_64-unknown-linux-gnu --release --no-fail-fast \
   && CARGO_TARGET_DIR="$HASHBROWN_TARGET_DIR" \
      RUSTFLAGS="-Zcodegen-backend=$BACKEND" \
      RUSTDOCFLAGS="-Zcodegen-backend=$BACKEND" \
      cargo +"$RUST_NIGHTLY" test --manifest-path "$HASHBROWN_DIR/Cargo.toml" --target x86_64-unknown-linux-gnu --release --features rustc-internal-api,serde,rayon,nightly --no-fail-fast; then
    overall_pass=$((overall_pass + 1))
else
    overall_fail=$((overall_fail + 1))
fi
echo ""

# ── Summary ───────────────────────────────────────────────────────────────────

echo "=== Crate Tests Summary: $overall_pass sections passed, $overall_fail sections failed ==="
if [ $overall_fail -gt 0 ]; then
    exit 1
fi
