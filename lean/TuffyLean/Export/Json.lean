-- TuffyLean/Export/Json.lean
-- Export instruction selection rules JSON for the Rust code generator.
-- Target-specific encoding lives under TuffyLean/Target/*.

import TuffyLean.Target.X86.Export

namespace TuffyLean.Export

/-- Main entry point: print JSON to stdout. -/
def main : IO Unit := do
  IO.println TuffyLean.Target.X86.Export.exportIselSpec

end TuffyLean.Export

/-- Entry point for `lean --run`. -/
def main : IO Unit := TuffyLean.Export.main
