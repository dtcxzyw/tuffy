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
- **Return type**: optional. Functions with no return type return `void`.
- **Body**: blocks and nested regions directly inside the function braces. The implicit
  top-level `function` region is not written in the text format.
