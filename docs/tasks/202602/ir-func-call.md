# Introduce Module layer and redesign IR function call representation

- Status: In Progress
- Created: 2026-02-10
- Completed: N/A
- Parent: N/A

## Description

The current `Op::Call(Operand, Vec<Operand>)` design has a fundamental problem:
the callee operand is always a dummy `iconst(0)`, with the real symbol name stored
in a side-channel `call_targets: HashMap<u32, String>` outside the IR. Similarly,
static data references use `static_refs: HashMap<u32, String>`. This breaks IR
self-containedness and complicates every pass that touches calls.

### Problems with current design

1. **IR is not self-contained.** The callee field carries no useful information;
   the actual target lives in an external map.
2. **Side-channel maps thread through every layer.** `TranslationResult`,
   `isel()`, and `select_inst()` all pass `call_targets` and `static_refs`.
3. **IR display is lossy.** `call v0(...)` shows a meaningless `v0 = iconst 0`
   instead of the real symbol name.
4. **Optimization is blocked.** Any future pass that wants to reason about call
   targets (inlining, devirtualization) must carry the side-channel maps.
5. **Two maps for the same concept.** `call_targets` and `static_refs` both map
   instruction index to symbol name, but are separate.

### Design decisions

1. **Introduce `Module` as the top-level IR container.** Currently `Function` is
   the top-level structure with no module concept. A `Module` owns the symbol
   table, all functions, and static data. This replaces the ad-hoc
   `TranslationResult` aggregation in the codegen layer.

2. **Unified `SymbolAddr` Op** (not split into `FuncAddr`/`DataAddr`). On x86
   both lower to the same LEA rip-relative. If distinction is needed later, it
   can be expressed via the type system or annotations.

3. **Interned symbol table** with `SymbolId(u32)`. Avoids repeated String
   allocation and enables O(1) equality comparison. The symbol table lives in
   `Module`, shared across all functions.

4. **Function name uses `SymbolId`.** `Function.name` changes from `String` to
   `SymbolId`. Functions are themselves entries in the module's symbol table.

5. **Static data migrates into `Module`.** Currently `static_data: Vec<(String,
   Vec<u8>)>` lives in `TranslationResult` (codegen layer). It belongs in the IR
   module alongside functions. Static data entries are also referenced via
   `SymbolId`.

6. **Callee is always indirect.** `Op::Call(Operand, Vec<Operand>)` where the
   first operand is a value produced by `SymbolAddr` (or any other pointer).
   This naturally supports both direct and indirect calls.

7. **Struct parameters in signatures, scalar extraction in body.** Function
   signatures allow struct-typed parameters, but the body never has a "struct
   SSA value". Fields are extracted via `Op::Param(param_idx, field_idx)`.
   Nested structs are recursively flattened in the signature.

8. **Call-site `{}` grouping.** At call sites, scalar values are grouped with
   `{}` to form struct arguments: `call @foo({%a, %b, %c}, %d)`. The grouping
   matches the callee's signature structure.

9. **Named parameters.** Scalar params use named form (`%y = param`), struct
   field extraction uses dotted form (`%s.1 = param`). This is display syntax;
   the internal representation is `Op::Param(param_idx, field_idx)`.

10. **Large structs (>16B) lowered to pointer at translation time.** When the
    ABI requires indirect passing, `mir_to_ir` converts the struct parameter to
    a pointer parameter plus explicit `Load` ops. Large structs do not appear
    as struct types in the IR signature.

### Target IR

#### Symbol address and basic call

```
%addr = symbol_addr @malloc
%ptr  = call %addr(%size)
```

#### Struct parameter: fn add_point(p: Point{x: i64, y: i64}) -> i64

```
func @add_point(p: {i64, i64}) -> i64 {
bb0:
  %p.0 = param 0, 0          // p.x : i64
  %p.1 = param 0, 1          // p.y : i64
  %sum = add %p.0, %p.1
  ret %sum
}
```

#### Call site with {} grouping

```
%f    = symbol_addr @add_point
%res  = call %f({%x, %y})    // {%x, %y} maps to param 0's {i64, i64}
```

#### Nested struct (recursively flattened)

```
// struct Inner { a: i64, b: i64 }
// struct Outer { inner: Inner, x: i64 }
// fn process(s: Outer, scale: i64) -> i64

func @process(s: {i64, i64, i64}, scale: i64) -> i64 {
bb0:
  %s.0    = param 0, 0       // s.inner.a
  %s.1    = param 0, 1       // s.inner.b
  %s.2    = param 0, 2       // s.x
  %scale  = param 1, 0       // scale (scalar, field 0 = self)
  ...
}

// call site
%r = call %f({%a, %b, %c}, %d)
```

#### Large struct (>16B, lowered to pointer by mir_to_ir)

```
// struct Big { fields: [i64; 4] }  — 32 bytes, indirect passing
// mir_to_ir lowers to pointer + explicit loads:

func @use_big(p: i64) -> i64 {    // p is a pointer to Big
bb0:
  %p    = param 0, 0
  %f0   = load %p, 8              // fields[0]
  %next = ptr_add %p, 8
  %f1   = load %next, 8           // fields[1]
  ...
}
```

### Module design

```rust
pub struct Module {
    pub name: String,
    pub symbols: SymbolTable,
    pub functions: Vec<Function>,
    pub static_data: Vec<StaticData>,
}

pub struct StaticData {
    pub name: SymbolId,
    pub data: Vec<u8>,
}
```

`Function.name` changes from `String` to `SymbolId`:

```rust
pub struct Function {
    pub name: SymbolId,  // was: String
    // ... rest unchanged
}
```

### Symbol table design

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

pub struct SymbolTable {
    names: Vec<String>,
    lookup: HashMap<String, SymbolId>,
}

impl SymbolTable {
    pub fn intern(&mut self, name: &str) -> SymbolId { ... }
    pub fn resolve(&self, id: SymbolId) -> &str { ... }
}
```

## Subtasks

### Phase 1: Introduce Module and SymbolTable

- [ ] Add `SymbolId` and `SymbolTable` to `tuffy_ir`
- [ ] Add `StaticData` struct to `tuffy_ir`
- [ ] Add `Module` struct to `tuffy_ir`
- [ ] Change `Function.name` from `String` to `SymbolId`
- [ ] Update `Function::new()` to accept `SymbolId`
- [ ] Update `Display for Function` to resolve name via symbol table (requires `Module` context)
- [ ] Update builder to work with `Module` context

### Phase 2: SymbolAddr Op

- [ ] Add `Op::SymbolAddr(SymbolId)` to instruction set
- [ ] Add builder method `symbol_addr(&mut self, name: &str) -> ValueRef`
- [ ] Update display to print `symbol_addr @name`

### Phase 3: Migrate codegen layer

- [ ] Update `mir_to_ir.rs`: build `Module` instead of `TranslationResult`
- [ ] Emit `SymbolAddr` instead of populating `call_targets`/`static_refs`
- [ ] Migrate `static_data` from `TranslationResult` into `Module`
- [ ] Remove `call_targets`, `static_refs`, `static_data` from `TranslationResult`
- [ ] Update `lib.rs` codegen driver to consume `Module`

### Phase 4: Update x86 backend

- [ ] Handle `Op::SymbolAddr` in `select_inst` (emit `LeaSymbol`)
- [ ] Remove `call_targets` and `static_refs` parameters from `isel()`
- [ ] Simplify `Op::Const` handling (no more `rdx_captures`/`static_refs` checks)

### Phase 5: Lean and spec

- [ ] Update Lean IR definition (source of truth)
- [ ] Update spec documentation

## Affected Modules

- `tuffy_ir/src/instruction.rs` — add `Op::SymbolAddr(SymbolId)`
- `tuffy_ir/src/types.rs` or new file — add `SymbolId`, `SymbolTable`
- `tuffy_ir/src/function.rs` — add `symbol_table` field to `Function`
- `tuffy_ir/src/builder.rs` — add `symbol_addr()` builder method
- `tuffy_ir/src/display.rs` — display `symbol_addr @name`
- `tuffy_ir/src/tests.rs` — update/add tests
- `lean/TuffyLean/IR/` — update Lean IR definition
- `rustc_codegen_tuffy/src/mir_to_ir.rs` — replace side-channel maps with `SymbolAddr`
- `tuffy_target_x86/src/isel.rs` — handle `SymbolAddr`, simplify `isel()` signature
- `docs/spec.md` — document `symbol_addr` instruction
