# SOP: Updating Documentation

- Created: 2026-02-09
- Status: Active

## Overview

This document describes the checks required whenever documentation files under `docs/`
are added or modified. Skipping these checks can cause broken links, missing pages on
the published site, or stale content that contradicts the source of truth.

## Checklist

### 1. SUMMARY.md

Every Markdown file that should appear on the published site **must** be listed in
`docs/SUMMARY.md`. mdBook only builds pages present in the summary — unlisted files
will result in 404 errors.

When adding a new page:

- Add an entry to `docs/SUMMARY.md` in the correct section and nesting level.
- If the page belongs to an existing group (e.g., `spec/`), add it as a nested entry
  under the group's parent.

### 2. Spec Index

If the change adds or removes a page under `docs/spec/`, update the Table of Contents
in `docs/spec/index.md` to match.

### 3. Source of Truth Conformance

The spec documents (`docs/spec/`) describe the IR but are **not** authoritative. The
Lean 4 definitions (`lean/TuffyLean/IR/`) are the source of truth.

When updating spec docs, verify that:

- Descriptions match the current Lean definitions.
- Semantics formulas reference the correct `eval*` function names from
  `TuffyLean.IR.Semantics`.
- Type names and instruction opcodes match the Rust implementation in `tuffy_ir/`.

### 4. Internal Links

Check that all cross-references between documentation pages are valid:

- Relative links (e.g., `[types](types.md)`) point to files that exist.
- Anchor links (e.g., `instructions.md#comparison`) reference headings that exist in
  the target file.

### 5. Build Verification

After making changes, build the documentation locally and verify:

```bash
mdbook build
```

The build must complete without errors. Optionally preview with:

```bash
mdbook serve
```

### 6. Commit

Documentation-only changes use the `docs` commit type:

```
docs: <description>
docs(spec): <description>    # for spec-specific changes
```

If the documentation change accompanies a code change (e.g., adding a new instruction),
the docs update should be a separate commit from the code change, per the project's
commit convention.
