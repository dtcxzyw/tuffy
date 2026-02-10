# Functions

A function is the top-level unit of compilation. It has a name, typed parameters,
an optional return type, and a body organized as a hierarchical CFG.

```
func @name(param_types...) -> ret_type {
  ...
}
```

- **Name**: prefixed with `@` in text format.
- **Parameters**: a list of types. Parameter values are created via `param` instructions.
  Parameters may optionally carry source-level names for readability (see below).
- **Return type**: optional. Functions with no return type return `void`.
- **Body**: blocks and nested regions directly inside the function braces. The implicit
  top-level `function` region is not written in the text format.

## Named Parameters

When source-level parameter names are available (e.g., extracted from MIR debug info),
they are displayed in the function signature and `param` instructions:

```
func @add(%a: int, %b: int) -> int {
  bb0:
    v0 = param %a
    v1 = param %b
    v2 = add v0, v1
    ret v2
}
```

Parameter names are prefixed with `%` in text format. When no name is available,
the numeric ABI index is used as a fallback:

```
func @add(int, int) -> int {
  bb0:
    v0 = param 0
    v1 = param 1
```

Named parameters are display-only — the internal representation uses numeric ABI
indices (`Op::Param(u32)`) for code generation.
