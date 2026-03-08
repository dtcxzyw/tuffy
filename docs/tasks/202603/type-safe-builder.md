# Type-Safe Builder API

- Status: Completed
- Created: 2026-03-08
- Completed: 2026-03-08
- Parent: N/A

## Description

Currently `tuffy_ir/src/builder.rs` uses untyped `Operand` and `ValueRef`, making it easy to pass wrong-typed operands at compile time. This task introduces type-safe wrapper types with runtime type checking during construction, providing compile-time type safety guarantees.

### Goals

1. Create typed operand wrappers: `IntOperand`, `FloatOperand`, `BoolOperand`, etc.
2. Create typed value wrappers: `IntValue`, `FloatValue`, `BoolValue`, etc.
3. Use `assert!` to check type matching when constructing typed wrappers from `Operand`/`ValueRef`
4. Update builder method signatures to use typed parameters and return values

### Design Principles

- Typed wrappers are zero-cost abstractions (newtype pattern)
- Type checking happens at construction time, then safe to use
- Maintain compatibility with existing IR structure
- Incremental migration without breaking existing code

## Implementation Plan

### Phase 1: Create Typed Wrapper Types

Create new module `tuffy_ir/src/typed.rs` defining:

**Typed Values (return value wrappers):**

```rust
pub struct IntValue(ValueRef);
pub struct FloatValue(ValueRef);
pub struct BoolValue(ValueRef);
pub struct ByteValue(ValueRef);
pub struct PtrValue(ValueRef);
pub struct UnitValue(ValueRef);
pub struct VectorValue(ValueRef);
```

Each provides:
- `fn new(value: ValueRef, func: &Function) -> Self` - constructs with type assertion
- `fn as_value_ref(&self) -> ValueRef` - extracts underlying ValueRef
- `fn into_value_ref(self) -> ValueRef` - consumes and returns ValueRef

**Typed Operands (parameter wrappers):**

```rust
pub struct IntOperand(Operand);
pub struct FloatOperand(Operand);
pub struct BoolOperand(Operand);
pub struct ByteOperand(Operand);
pub struct PtrOperand(Operand);
pub struct UnitOperand(Operand);
pub struct VectorOperand(Operand);
```

Each provides:
- `fn new(operand: Operand, func: &Function) -> Self` - constructs with type assertion
- `fn as_operand(&self) -> &Operand` - borrows underlying Operand
- `fn into_operand(self) -> Operand` - consumes and returns Operand

### Phase 2: Implement Type Checking

Add helper method to `Function`:

```rust
impl Function {
    pub fn value_type(&self, value: ValueRef) -> &Type {
        if value.is_block_arg() {
            &self.block_args[value.index() as usize].ty
        } else {
            &self.instructions[value.inst_index() as usize].ty
        }
    }
}
```

Type checking in wrapper constructors:

```rust
impl IntValue {
    pub fn new(value: ValueRef, func: &Function) -> Self {
        assert!(matches!(func.value_type(value), Type::Int),
                "Expected Int type, got {:?}", func.value_type(value));
        Self(value)
    }
}
```

### Phase 3: Update Builder Methods

Update builder methods incrementally, starting with integer operations:

**Before:**
```rust
pub fn iadd(&mut self, lhs: impl Into<Operand>, rhs: impl Into<Operand>, origin: Origin) -> ValueRef
```

**After:**
```rust
pub fn iadd(&mut self, lhs: IntOperand, rhs: IntOperand, origin: Origin) -> IntValue
```

Priority order for migration:
1. Integer arithmetic (iadd, isub, imul, etc.)
2. Boolean operations (and, or, xor, not)
3. Comparisons (icmp, fcmp)
4. Float operations (fadd, fsub, fmul, etc.)
5. Memory operations (load, store)
6. Control flow (br, condbr, ret)

### Phase 4: Convenience Conversions

Add `From` implementations for ergonomic usage:

```rust
impl From<IntValue> for ValueRef {
    fn from(v: IntValue) -> Self { v.0 }
}

impl IntOperand {
    pub fn from_value(value: IntValue) -> Self {
        Self(Operand::new(value.0))
    }
}
```

### Phase 5: Testing and Validation

- Add unit tests for type checking assertions
- Update existing builder tests to use typed API
- Verify all type mismatches are caught at construction time
- Ensure zero runtime overhead (check generated assembly)

## Subtasks

1. Create `tuffy_ir/src/typed.rs` with typed wrapper definitions
2. Add `Function::value_type()` helper method
3. Implement type checking in wrapper constructors
4. Update integer operation builder methods
5. Update boolean operation builder methods
6. Update comparison operation builder methods
7. Update float operation builder methods
8. Update memory operation builder methods
9. Update control flow builder methods
10. Add unit tests for type safety
11. Update existing tests to use typed API

## Affected Modules

- `tuffy_ir/src/typed.rs` - new module for typed wrappers
- `tuffy_ir/src/builder.rs` - update method signatures to use typed parameters/returns
- `tuffy_ir/src/function.rs` - add `value_type()` helper method
- `tuffy_ir/src/lib.rs` - export new typed module
- `rustc_codegen_tuffy/src/mir_to_ir.rs` - update to use typed builder API
- All test files using builder API

## Notes

- Type checking is runtime (assert), not compile-time, but provides better error messages
- Typed wrappers prevent accidental type mismatches at API boundaries
- Migration can be gradual - old untyped methods can coexist during transition
- Consider adding `try_new()` variants that return `Result` instead of panicking
