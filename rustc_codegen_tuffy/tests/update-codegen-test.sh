#!/bin/bash
# Update CHECK lines in codegen test files based on actual IR output.

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: $0 <test.rs>"
    exit 1
fi

TEST_FILE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

if [ ! -f "$TEST_FILE" ]; then
    echo "ERROR: File not found: $TEST_FILE"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TOOLCHAIN="${TOOLCHAIN:-nightly-2026-03-28}"
export RUSTUP_TOOLCHAIN="$TOOLCHAIN"

# Find backend .so
if [ -n "${BACKEND:-}" ]; then
    :
elif [ -f "$CRATE_ROOT/target/release/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/release/librustc_codegen_tuffy.so"
elif [ -f "$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so" ]; then
    BACKEND="$CRATE_ROOT/target/debug/librustc_codegen_tuffy.so"
else
    echo "ERROR: Backend not found."
    echo "Run: cd rustc_codegen_tuffy && cargo build"
    exit 1
fi

# Parse compile-flags
compile_flags=""
if grep -q "^// compile-flags:" "$TEST_FILE"; then
    compile_flags=$(grep "^// compile-flags:" "$TEST_FILE" | head -1 | sed 's|^// compile-flags:||')
fi

# Compile and capture IR
name=$(basename "$TEST_FILE" .rs)
ir_output=$(mktemp)
out_file=$(mktemp)
trap "rm -f $ir_output $out_file" EXIT

rustc -Z codegen-backend="$BACKEND" \
    -D warnings \
    -C llvm-args=dump-ir $compile_flags \
    --crate-name "$name" \
    -o "$out_file" \
    "$TEST_FILE" 2>"$ir_output" || true

# Check if IR was actually generated (ignore rustc exit code)
if [ ! -s "$ir_output" ]; then
    echo "ERROR: No IR output generated"
    exit 1
fi

# Generate CHECK lines from IR output (preserving empty lines)
# Filter out panic messages - stop at "thread 'rustc' panicked"
# Normalize environment-specific paths before generating CHECK lines.
source "$CRATE_ROOT/tests/normalize-ir.sh"

ir_normalized=$(mktemp)
check_lines=$(mktemp)
trap "rm -f $ir_output $ir_normalized $check_lines" EXIT

normalize_ir < "$ir_output" > "$ir_normalized"

while IFS= read -r line; do
    # Stop if we hit a panic message
    if [[ "$line" =~ ^thread\ \'rustc\' ]]; then
        break
    fi
    # Add CHECK prefix, preserving empty lines and indentation
    # Strip trailing whitespace from non-empty lines
    if [ -z "$line" ]; then
        echo "// CHECK:"
    else
        echo "// CHECK: $line" | sed 's/[[:space:]]*$//'
    fi
done < "$ir_normalized" > "$check_lines"

# Create updated test file
updated_file=$(mktemp)
trap "rm -f $ir_output $ir_normalized $check_lines $updated_file" EXIT

# Copy only leading comment lines (compile-flags, etc.), skip CHECK lines
awk '/^\/\/ CHECK:/ {next} /^\/\// {print; next} {exit}' "$TEST_FILE" > "$updated_file"

# Add generated CHECK lines
cat "$check_lines" >> "$updated_file"

# Add code section (non-comment, non-CHECK lines)
awk '/^\/\/ CHECK:/ {next} /^\/\// {next} {print}' "$TEST_FILE" >> "$updated_file"

# Replace original file
mv "$updated_file" "$TEST_FILE"

echo "Updated CHECK lines in $TEST_FILE"
