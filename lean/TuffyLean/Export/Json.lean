-- TuffyLean/Export/Json.lean
-- Export instruction selection rules JSON for the Rust code generator.
-- Target-specific encoding lives under TuffyLean/Target/*.

import TuffyLean.Target.X86.Export

namespace TuffyLean.Export

private def usage : String :=
  "Usage: lean --run TuffyLean/Export/Json.lean [<target>|--target <target>]"

private def exportForTarget? (target : String) : Option String :=
  match target with
  | "x86" => some TuffyLean.Target.X86.Export.exportIselSpec
  | _ => none

private def parseTarget (args : List String) : Except String String :=
  match args with
  | [] => .ok "x86"
  | [target] => .ok target
  | ["--target", target] => .ok target
  | _ => .error usage

/-- Main entry point: print JSON to stdout. -/
def main (args : List String) : IO Unit := do
  let target ←
    match parseTarget args with
    | .ok target => pure target
    | .error msg => throw <| IO.userError msg

  match exportForTarget? target with
  | some json => IO.println json
  | none => throw <| IO.userError s!"unknown target: {target}"

end TuffyLean.Export

/-- Entry point for `lean --run`. -/
def main (args : List String) : IO Unit := TuffyLean.Export.main args
