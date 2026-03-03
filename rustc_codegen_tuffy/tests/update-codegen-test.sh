#!/bin/bash
# Update CHECK lines in codegen test files based on actual IR output.

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: $0 <test.rs>"
    exit 1
fi

TEST_FILE="$1"

if [ ! -f "$TEST_FILE" ]; then
    echo "ERROR: File not found: $TEST_FILE"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

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

if ! rustc +nightly -Z codegen-backend="$BACKEND" \
    -C llvm-args=dump-ir $compile_flags \
    --crate-name "$name" \
    -o "$out_file" \
    "$TEST_FILE" 2>"$ir_output"; then
    echo "ERROR: Compilation failed"
    cat "$ir_output"
    exit 1
fi

# Generate CHECK lines from IR output
check_lines=$(mktemp)
trap "rm -f $ir_output $check_lines" EXIT

while IFS= read -r line; do
    # Preserve indentation and add CHECK prefix (including empty lines)
    echo "// CHECK: $line"
done < "$ir_output" > "$check_lines"

# Create updated test file
updated_file=$(mktemp)
trap "rm -f $ir_output $check_lines $updated_file" EXIT

# Copy lines before first CHECK or all lines if no CHECK exists
awk '/^\/\/ CHECK:/ {exit} {print}' "$TEST_FILE" > "$updated_file"

# Add generated CHECK lines
cat "$check_lines" >> "$updated_file"

# Add code section (after last CHECK line or compile-flags)
awk '
    /^\/\/ CHECK:/ {in_check=1; next}
    in_check && !/^\/\/ CHECK:/ {in_check=0}
    !in_check && !/^\/\/ CHECK:/ && !/^\/\/ compile-flags:/ {print}
' "$TEST_FILE" >> "$updated_file"

# Replace original file
mv "$updated_file" "$TEST_FILE"

echo "Updated CHECK lines in $TEST_FILE"
