-- TuffyLean/Rewrites/PassManifest.lean
-- Lean-owned manifest for the current tuffy_opt cleanup pipeline.

namespace TuffyLean.Rewrites

/-- Cleanup pass staging used by the generated optimizer dispatcher. -/
inductive CleanupPassStage where
  | local
  | module
  deriving DecidableEq, Repr

/-- Verification state for a cleanup pass family. -/
inductive CleanupPassVerification where
  | verified
  | legacy
  deriving DecidableEq, Repr

/-- Lean-owned manifest entry for one cleanup pass family. -/
structure CleanupPassFamily where
  name : String
  stage : CleanupPassStage
  runner : String
  verification : CleanupPassVerification
  leanSource : Option String := none
  deriving Repr

/-- Current non-inline cleanup families in optimizer execution order. -/
def allCleanupPassFamilies : List CleanupPassFamily :=
  [
    {
      name := "promote"
      stage := .local
      runner := "promote"
      verification := .legacy
    },
    {
      name := "peephole"
      stage := .local
      runner := "peephole"
      verification := .verified
      leanSource := some "TuffyLean.Rewrites.Basic"
    },
    {
      name := "cfg_cleanup"
      stage := .local
      runner := "cfg_cleanup"
      verification := .legacy
    },
    {
      name := "bulk_memory"
      stage := .module
      runner := "bulk_memory"
      verification := .legacy
    },
    {
      name := "scalar_swap"
      stage := .module
      runner := "scalar_swap"
      verification := .legacy
    }
  ]

end TuffyLean.Rewrites
