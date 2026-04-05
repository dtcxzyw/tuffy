#!/bin/bash
# Normalize environment-specific content in IR output.
# Replaces sysroot paths and path-length-dependent binary data
# so codegen tests are portable across machines.
#
# Usage: normalize_ir <input >output  (as a filter)
#    or: source normalize-ir.sh; normalize_ir < file

# Canonical repo root for path normalization.
_TUFFY_REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." 2>/dev/null && pwd)"

normalize_ir() {
    sed \
        -e "s|${_TUFFY_REPO_ROOT}|/tuffy|g" \
        -e 's|/rustc/[0-9a-f]\{40\}/library/|\$SYSROOT/library/|g' \
        -e 's|/.*/lib/rustlib/src/rust/library/|\$SYSROOT/library/|g' \
        -e 's|^\(data @\.Lloc\.[0-9]* = \)"[^"]*"\( relocs .*\)|\1"..."\2|' \
        -e 's|C[a-zA-Z0-9]\{1,\}_\([0-9]\)|C\$HASH_\1|g'
}

# When executed directly, act as a filter.
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    normalize_ir
fi
