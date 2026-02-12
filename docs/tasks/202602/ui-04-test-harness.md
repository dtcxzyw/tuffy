# Improve Test Runner to Reduce False Failures

- Status: Completed
- Created: 2026-02-08
- Completed: 2026-02-12
- Parent: docs/tasks/202602/ui-tests.md

## Description

~36% of UI test failures are not caused by tuffy code but by the test runner setup: wrong edition, missing `#![feature(...)]` gates, tests requiring specific compile flags, or tests that are expected to fail.

Key deliverables:
- Parse `//@ edition:` directives and pass the correct `--edition` flag
- Parse `//@ compile-flags:` and apply them (currently these tests are skipped entirely)
- Expand skip filters: detect `#![feature(...)]` attributes and pass `-Z allow-features`
- Separate "tuffy panic" failures from "expected compilation errors" in reporting
- Add a deterministic mode (no `shuf`) for reproducible runs

## Affected Modules

- `scratch/run_ui_tests.sh`
