# Regions

The CFG is organized as a tree of SESE (Single Entry, Single Exit) regions. Each
region contains an ordered sequence of basic blocks and child regions.

## Region Kinds

| Kind | Description |
|------|-------------|
| `function` | Top-level function region. Every function has exactly one. |
| `loop` | Loop region. The entry block is the loop header. Backedges use `continue`. |
| `plain` | Generic SESE region for structured control flow. |

## Nesting and Implicit Capture

Regions nest to form a tree. Values defined in an outer region are visible in inner
regions via implicit capture (VPlan style). There is no explicit capture list — the
live-in set is computed on demand.

```
func @example(int) -> int {
  bb0:
    v0 = iconst 10       // v0 defined in function body

  region loop {
    bb1(v1: int):
      v2 = add v1, v0    // v0 captured implicitly from outer scope
      ...
  }
}
```

## Loop Regions

A loop region's entry block is the loop header. The `continue` terminator transfers
control back to the loop header, passing new values for the header's block arguments.
Exiting a loop is done by branching to a block outside the loop region.
