-- TuffyLean/Target/X86/Defs.lean
-- Core DSL types for x86 instruction selection rules.

namespace TuffyLean.Target.X86

/-- x86 operand size. -/
inductive OpSize where
  | s8 | s16 | s32 | s64
  deriving Repr, BEq, Hashable

/-- x86 condition codes for Jcc/CMOVcc/SETcc. -/
inductive CondCode where
  | e | ne | l | le | g | ge | b | be | a | ae
  deriving Repr, BEq, Hashable

/-- Named physical registers that require fixed allocation. -/
inductive FixedReg where
  | rax | rcx | rdx | rbp
  deriving Repr, BEq, Hashable

/-- Reference to a virtual register in emitted instructions. -/
inductive RegRef where
  /-- A register bound from the pattern (input operand). -/
  | named (name : String)
  /-- Allocate a fresh unconstrained virtual register. -/
  | fresh (name : String)
  /-- Allocate a fresh virtual register constrained to a physical register. -/
  | freshFixed (name : String) (reg : FixedReg)
  deriving Repr, BEq, Hashable

/-- Annotation guard: constrains which annotation variant a rule matches. -/
inductive AnnGuard where
  | any
  | signed
  | unsigned
  deriving Repr, BEq, Hashable

/-- A single x86 machine instruction to emit. -/
inductive EmitInst where
  | movRR (size : OpSize) (dst src : RegRef)
  | addRR (size : OpSize) (dst src : RegRef)
  | subRR (size : OpSize) (dst src : RegRef)
  | imulRR (size : OpSize) (dst src : RegRef)
  | orRR  (size : OpSize) (dst src : RegRef)
  | andRR (size : OpSize) (dst src : RegRef)
  | xorRR (size : OpSize) (dst src : RegRef)
  | shlRCL (size : OpSize) (dst : RegRef)
  | shrRCL (size : OpSize) (dst : RegRef)
  | sarRCL (size : OpSize) (dst : RegRef)
  | cmpRR (size : OpSize) (src1 src2 : RegRef)
  | cmovCC (size : OpSize) (cc : CondCode) (dst src : RegRef)
  | popcnt (dst src : RegRef)
  | lzcnt (dst src : RegRef)
  | tzcnt (dst src : RegRef)
  deriving Repr, BEq, Hashable

end TuffyLean.Target.X86
