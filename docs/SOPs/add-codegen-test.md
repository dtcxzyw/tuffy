# SOP: Adding rustc_codegen_tuffy Codegen Tests

## Purpose

This SOP defines the standard procedure for adding new codegen tests to `rustc_codegen_tuffy/tests/codegen/`. These tests verify MIR-to-IR translation correctness.

## When to Use

- After fixing a bug in `rustc_codegen_tuffy/mir_to_ir/` (regression test)
- When adding new translation logic for MIR constructs
- When modifying existing translation behavior

## Prerequisites

- Backend must be built: `cd rustc_codegen_tuffy && cargo build`
- Understand which `mir_to_ir/` module your test targets

## Procedure

### 1. Determine Test Location

Organize tests by the `mir_to_ir/` module being tested:

| Module | Test Directory |
|--------|----------------|
| `rvalue.rs` | `tests/codegen/rvalue/` |
| `intrinsic.rs` | `tests/codegen/intrinsic/` |
| `terminator.rs` | `tests/codegen/terminator/` |
| `call.rs` | `tests/codegen/call/` |
| Other modules | Create corresponding subdirectory |

### 2. Create Test File

Create a new `.rs` file in the appropriate directory with a descriptive name:

```
tests/codegen/rvalue/my_feature.rs
```

### 3. Write Test Structure

Use this template:

```rust
// compile-flags: -Zmir-opt-level=3 -C debug-assertions=off

#![crate_type = "lib"]
#![no_std]

#[no_mangle]
pub fn test_function(a: i32) -> i32 {
    // Minimal code that exercises the feature
    a + 1
}
```

**Key requirements:**
- Use standard compile flags: `-Zmir-opt-level=3 -C debug-assertions=off`
- Include `#![crate_type = "lib"]` and `#![no_std]`
- Use `#[no_mangle]` on test functions
- Keep code minimal and focused
- Use meaningful identifier names

### 4. Generate CHECK Lines

Run the update script to automatically generate CHECK annotations:

```bash
cd rustc_codegen_tuffy
./tests/update-codegen-test.sh tests/codegen/rvalue/my_feature.rs
```

This will:
- Compile the test with the tuffy backend
- Capture MIR and IR output
- Insert CHECK lines into the test file

**CRITICAL:** Never write CHECK lines manually. Always use `update-codegen-test.sh`.

### 5. Verify Test Passes

Run the codegen test suite:

```bash
cd rustc_codegen_tuffy
./tests/run-codegen-tests.sh
```

Verify your new test passes.

### 6. Review Generated Output

Open the test file and review:
- CHECK lines match expected IR structure
- MIR output is as expected
- Test exercises the intended code path

### 7. Commit

Commit the test file with an appropriate message:

```
test(rustc-codegen): add codegen test for <feature>

Add regression test for <bug> or test coverage for <feature>.
Verifies that <specific behavior> translates correctly to IR.
```

## Notes

- CHECK lines use exact string matching (not regex)
- Indentation in CHECK lines must match IR output exactly
- Each CHECK line must appear in order in the generated output
- Empty CHECK lines (`// CHECK:`) preserve blank lines in output
- The script automatically filters out panic messages from IR output

## Common Patterns

### Testing Multiple Functions

```rust
#[no_mangle]
pub fn func1(a: i32) -> i32 { a + 1 }

#[no_mangle]
pub fn func2(a: u64) -> u64 { a * 2 }
```

Each function will have separate MIR and IR CHECK blocks.

### Testing with Specific Compile Flags

```rust
// compile-flags: -Zmir-opt-level=0 -C opt-level=0
```

Only use non-standard flags when testing specific behaviors (e.g., debug assertions, unoptimized codegen).

### Testing Intrinsics

```rust
#[no_mangle]
pub fn test_rotate(x: u32, n: u32) -> u32 {
    x.rotate_left(n)
}
```

The test will capture both the high-level intrinsic call and its lowered implementation.

## References

- `rustc_codegen_tuffy/README.md` — Component architecture and testing conventions
- `rustc_codegen_tuffy/tests/update-codegen-test.sh` — CHECK line generation script
- `rustc_codegen_tuffy/tests/run-codegen-tests.sh` — Test runner
