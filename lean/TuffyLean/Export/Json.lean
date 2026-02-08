-- TuffyLean/Export/Json.lean
-- Export verified rewrite rules as JSON for codegen generator

import TuffyLean.Rewrites.Basic

namespace TuffyLean.Export

/-- Placeholder: export framework for generating declarative
    transform descriptions from verified Lean definitions.
    The codegen generator reads these to produce Rust code. -/
def exportRules : IO Unit := do
  IO.println "TODO: export verified rewrite rules as JSON"

end TuffyLean.Export
