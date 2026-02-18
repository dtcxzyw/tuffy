#!/usr/bin/env bash
# Extract and compile Rust stdlib doctests using the tuffy codegen backend.
# Usage: ./run-doctest.sh [library-dir] [--run]
#   library-dir: path to scratch/rust/library (default: ../../scratch/rust/library)
#   --run: also execute compiled binaries (default: compile-only)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Resolve backend .so
if [[ -n "${BACKEND:-}" ]]; then
    :
elif [[ -f "$CRATE_DIR/target/release/librustc_codegen_tuffy.so" ]]; then
    BACKEND="$CRATE_DIR/target/release/librustc_codegen_tuffy.so"
else
    BACKEND="$CRATE_DIR/target/debug/librustc_codegen_tuffy.so"
fi

LIBRARY_DIR="${1:-$CRATE_DIR/../../scratch/rust/library}"
LIBRARY_DIR="$(cd "$LIBRARY_DIR" && pwd)"
RUN_MODE=0
for arg in "$@"; do
    [[ "$arg" == "--run" ]] && RUN_MODE=1
done

OUTDIR="/tmp/tuffy_doctest"
rm -rf "$OUTDIR"
mkdir -p "$OUTDIR/src" "$OUTDIR/bin" "$OUTDIR/logs" "$OUTDIR/tmp"

EXTRACT_SCRIPT="$OUTDIR/extract.py"
cat > "$EXTRACT_SCRIPT" << 'PYEOF'
#!/usr/bin/env python3
"""Extract runnable doctests from Rust source files."""
import sys, os, json

def extract_doctests(filepath):
    with open(filepath) as f:
        lines = f.readlines()

    blocks = []
    current = []
    in_code = False
    skip = False

    for line in lines:
        stripped = line.strip()
        # Match doc comment lines
        doc_content = None
        if stripped.startswith('///'):
            doc_content = stripped[3:]
        elif stripped.startswith('//!'):
            doc_content = stripped[3:]

        if doc_content is not None:
            trimmed = doc_content.strip()
            if trimmed.startswith('```'):
                if in_code:
                    if not skip:
                        blocks.append('\n'.join(current))
                    current = []
                    in_code = False
                    skip = False
                else:
                    in_code = True
                    attrs = trimmed[3:].strip().lower().replace(',', ' ')
                    tokens = attrs.split()
                    skip_kws = {'ignore', 'compile_fail', 'no_run', 'text',
                                'should_panic', 'no_test', 'custom', 'c', 'cpp',
                                'python', 'json', 'toml', 'yaml', 'html', 'xml',
                                'sh', 'bash', 'console', 'plain', 'asm', 'assembly',
                                'nasm', 'masm', 'gas', 'markdown', 'md', 'svg',
                                'css', 'js', 'javascript', 'sql', 'diff'}
                    if any(t in skip_kws for t in tokens):
                        skip = True
            elif in_code and not skip:
                # Strip leading space from doc content
                c = doc_content[1:] if doc_content.startswith(' ') else doc_content
                # Hidden lines: strip '# ' prefix at any indentation
                stripped_c = c.lstrip()
                if stripped_c.startswith('# ') or stripped_c == '#':
                    indent = c[:len(c) - len(stripped_c)]
                    stripped_c = stripped_c[2:] if stripped_c.startswith('# ') else ''
                    c = indent + stripped_c
                current.append(c)
        else:
            if in_code:
                in_code = False
                current = []
                skip = False

    return blocks

def is_likely_rust(code):
    """Heuristic: reject blocks that look like prose or assembly."""
    lines = [l.strip() for l in code.strip().split('\n') if l.strip()]
    if not lines:
        return False
    # Prose: most lines don't end with ; { } ) , or start with keywords
    rust_indicators = 0
    for l in lines:
        if any(l.endswith(c) for c in [';', '{', '}', ')', ',', ']']):
            rust_indicators += 1
        elif any(l.startswith(k) for k in ['let ', 'fn ', 'use ', 'struct ', 'enum ',
                'impl ', 'trait ', 'pub ', 'mod ', 'const ', 'static ', 'type ',
                'match ', 'if ', 'for ', 'while ', 'loop ', 'return ', 'assert',
                '#[', '#!', 'extern ', 'unsafe ', 'async ', 'println!', 'eprintln!']):
            rust_indicators += 1
    return rust_indicators > 0

def needs_main_wrap(code):
    """Check if doctest needs fn main() wrapper."""
    for line in code.split('\n'):
        stripped = line.strip()
        if stripped.startswith('fn main'):
            return False
    return True

def wrap_doctest(code):
    """Wrap doctest in fn main() if needed."""
    if needs_main_wrap(code):
        indented = '\n'.join('    ' + l if l.strip() else '' for l in code.split('\n'))
        return f'fn main() {{\n{indented}\n}}'
    return code

if __name__ == '__main__':
    src_dir = sys.argv[1]
    out_dir = sys.argv[2]

    results = []
    idx = 0
    for root, dirs, files in os.walk(src_dir):
        for fname in sorted(files):
            if not fname.endswith('.rs'):
                continue
            fpath = os.path.join(root, fname)
            rel = os.path.relpath(fpath, src_dir)
            blocks = extract_doctests(fpath)
            for i, block in enumerate(blocks):
                if not is_likely_rust(block):
                    continue
                code = wrap_doctest(block)
                name = rel.replace('/', '_').replace('.rs', '') + f'_{i}'
                out_path = os.path.join(out_dir, f'{name}.rs')
                with open(out_path, 'w') as f:
                    f.write(code + '\n')
                results.append({'name': name, 'source': rel, 'index': i})
                idx += 1

    manifest = os.path.join(out_dir, 'manifest.json')
    with open(manifest, 'w') as f:
        json.dump(results, f)
    print(f'Extracted {len(results)} doctests')
PYEOF

echo "=== Extracting doctests from $LIBRARY_DIR ==="
python3 "$EXTRACT_SCRIPT" "$LIBRARY_DIR" "$OUTDIR/src"

TOTAL=$(python3 -c "import json; d=json.load(open('$OUTDIR/src/manifest.json')); print(len(d))")
echo "Total doctests: $TOTAL"

PASS=0
FAIL=0
SKIP=0
EXCLUDED=0
ERRORS=""

# Load exclusion list
EXCLUDE_FILE="$SCRIPT_DIR/doctest-exclude.txt"
declare -A doctest_excluded
if [[ -f "$EXCLUDE_FILE" ]]; then
    while IFS= read -r line; do
        line="${line%%#*}"
        line="${line// /}"
        [[ -z "$line" ]] && continue
        doctest_excluded["$line"]=1
    done < "$EXCLUDE_FILE"
fi

echo "=== Compiling doctests with tuffy ==="
for src in "$OUTDIR/src/"*.rs; do
    [[ "$(basename "$src")" == "manifest.json" ]] && continue
    name="$(basename "$src" .rs)"

    if [[ "${doctest_excluded[$name]+_}" ]]; then
        EXCLUDED=$((EXCLUDED + 1))
        continue
    fi
    bin="$OUTDIR/bin/$name"
    log="$OUTDIR/logs/$name.log"

    tmpdir="$OUTDIR/tmp/$name"
    mkdir -p "$tmpdir"
    if rustc +nightly -Z codegen-backend="$BACKEND" \
        --edition 2021 -o "$tmpdir/$name" "$src" \
        > "$log" 2>&1; then
        mv "$tmpdir/$name" "$bin"
        if [[ $RUN_MODE -eq 1 ]]; then
            if timeout 10 "$bin" >> "$log" 2>&1; then
                PASS=$((PASS + 1))
            else
                FAIL=$((FAIL + 1))
                ERRORS="$ERRORS  FAIL(run): $name\n"
            fi
        else
            PASS=$((PASS + 1))
        fi
    else
        # Check if it's a compile error from rustc (not tuffy)
        if grep -q "error\[E" "$log" 2>/dev/null; then
            SKIP=$((SKIP + 1))
        else
            FAIL=$((FAIL + 1))
            ERRORS="$ERRORS  FAIL(compile): $name\n"
        fi
    fi
    rm -rf "$tmpdir"
done

echo ""
echo "=== Results ==="
echo "Pass:  $PASS"
echo "Fail:  $FAIL"
echo "Skip:  $SKIP (rustc compile errors, not tuffy)"
echo "Excluded: $EXCLUDED (known non-tuffy failures)"
echo "Total: $TOTAL"
if [[ -n "$ERRORS" ]]; then
    echo ""
    echo "Failures:"
    echo -e "$ERRORS"
fi
