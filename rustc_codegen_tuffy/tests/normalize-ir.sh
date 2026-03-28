#!/bin/bash
# Normalize environment-specific content in IR output.
# Replaces sysroot paths and path-length-dependent binary data
# so codegen tests are portable across machines.
#
# Usage: normalize_ir <input >output  (as a filter)
#    or: source normalize-ir.sh; normalize_ir < file

normalize_ir() {
    sed \
        -e 's|/rustc/[0-9a-f]\{40\}/library/|\$SYSROOT/library/|g' \
        -e 's|/.*/lib/rustlib/src/rust/library/|\$SYSROOT/library/|g' \
        -e 's|^\(data @\.Lloc\.[0-9]* = \)"[^"]*"\( relocs .*\)|\1"..."\2|'
}

# When executed directly, act as a filter.
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    normalize_ir
fi
