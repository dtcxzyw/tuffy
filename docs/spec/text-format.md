# Text Format

Tuffy IR uses a Cranelift-inspired text format for human-readable output.

## Naming Conventions

| Entity | Format | Example |
|--------|--------|---------|
| Functions | `@name` | `@add`, `@factorial` |
| Values | `vN` | `v0`, `v1`, `v2` |
| Blocks | `bbN` | `bb0`, `bb1` |
| Regions | `region <kind>` | `region loop`, `region plain` |

Values are numbered sequentially (v0, v1, v2, ...) in region tree order. Within each
block, block arguments are numbered before instruction results.

## Grammar

```
function     ::= 'func' '@' name '(' param_list ')' ('->' type annotation)? '{' body '}'
param_list   ::= (type annotation (',' type annotation)*)?
body         ::= (block | region)*
region       ::= 'region' region_kind '{' region_body '}'
region_kind  ::= 'loop' | 'plain'
region_body  ::= (block | region)*
block        ::= block_header instruction*
block_header ::= 'bb' N block_args? ':'
block_args   ::= '(' block_arg (',' block_arg)* ')'
block_arg    ::= value ':' type
instruction  ::= (value annotation '=')? opcode operands
operand      ::= value annotation
annotation   ::= (':' range_ann)*
range_ann    ::= 's' N | 'u' N | 'known' '(' ternary ')'
ternary      ::= [01?x_]+
value        ::= 'v' N
type         ::= 'int' | 'byte' | 'ptr'
```

## Complete Example

A factorial function demonstrating nested regions, block arguments, and control flow:

```
func @factorial(int:s32) -> int:s32 {
  bb0:
    v0:s32 = param 0
    v1 = iconst 1
    v2 = iconst 1
    br bb1(v2, v1)

  region loop {
    bb1(v4: int, v5: int):
      v6 = icmp.le v5:s32, v0:s32
      brif v6, bb2, bb3

    bb2:
      v8 = mul v4, v5
      v9 = sub v5, v1
      continue v8, v9
  }

  bb3:
    ret v4:s32
}
```
