-- TuffyLean/IR/Semantics.lean
-- Operational semantics of tuffy IR instructions

import TuffyLean.IR.Types
import Mathlib.Data.Int.Bitwise

namespace TuffyLean.IR

-- DontCare(N) annotation semantics:
-- - Definition-side: only the lower N bits are authoritative; bits ≥ N may hold any value
-- - Use-side: consumer promises to only inspect lower N bits
-- - Violating the annotation produces poison

/-- Integer arithmetic semantics (infinite precision) -/
def evalAdd (a b : Int) : Int := a + b
def evalSub (a b : Int) : Int := a - b
def evalMul (a b : Int) : Int := a * b

/-- Integer division produces poison on division by zero.
    Signedness is a property of operand annotations, not the operation. -/
def evalDiv (a b : Int) : Value :=
  if b = 0 then .poison else .int (a / b)

/-- Integer remainder produces poison on division by zero.
    Signedness is a property of operand annotations, not the operation. -/
def evalRem (a b : Int) : Value :=
  if b = 0 then .poison else .int (a % b)

/-- Bitwise AND (two's complement, infinite width) -/
def evalAnd (a b : Int) : Int := Int.land a b

/-- Bitwise OR (two's complement, infinite width) -/
def evalOr (a b : Int) : Int := Int.lor a b

/-- Bitwise XOR (two's complement, infinite width) -/
def evalXor (a b : Int) : Int := Int.xor a b

/-- Boolean AND (logical conjunction) -/
def evalBAnd (a b : Bool) : Bool := a && b

/-- Boolean OR (logical disjunction) -/
def evalBOr (a b : Bool) : Bool := a || b

/-- Boolean XOR (logical exclusive or) -/
def evalBXor (a b : Bool) : Bool := xor a b

/-- Population count: number of set bits in a natural number. -/
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

/-- Population count: number of set bits in the binary representation.
    Defined for non-negative integers; negative values produce poison. -/
def evalCountOnes (a : Int) : Value :=
  if a < 0 then .poison
  else .int (popcount a.toNat)

/-- Count trailing zeros: number of zero bits after the least significant set bit.
    Helper on natural numbers. Returns 0 for 0 (though IR-level CTZ of 0 is poison). -/
def ctz : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else 1 + ctz ((n + 1) / 2)

/-- Count leading zeros in an n-bit representation.
    For val in [0, 2^n), returns n - floor(log2(val)) - 1 when val > 0,
    and n when val = 0. -/
def clzN (n : Nat) (val : Nat) : Nat :=
  if val = 0 then n
  else n - Nat.log2 val - 1

/-- Count leading zeros after truncating to n bits.
    n = 0 produces poison. The value is reduced modulo 2^n (extracting
    the low n bits in two's complement) before counting. -/
def evalCountLeadingZeros (a : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else .int (clzN n ((a % (2 ^ n : Int)).toNat))

/-- Count trailing zeros. Defined for non-negative integers; negative values
    and zero produce poison. -/
def evalCountTrailingZeros (a : Int) : Value :=
  if a ≤ 0 then .poison
  else .int (ctz a.toNat)

/-- Byte-swap an n-byte integer. n = 0 produces poison.
    Reverses the byte order of the low n bytes (value mod 2^(8n)). -/
def evalBswap (a : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let mask := (2 : Int) ^ (8 * n) - 1
    let v := (a % ((2 : Int) ^ (8 * n))).toNat
    let rec go (i : Nat) (acc : Nat) : Nat :=
      if i >= n then acc
      else go (i + 1) (acc + ((v >>> (i * 8)) % 256) <<< ((n - 1 - i) * 8))
    .int (go 0 0 &&& mask.toNat)

/-- Bit-reverse an n-bit integer. n = 0 produces poison.
    Reverses the bit order of the low n bits (value mod 2^n). -/
def evalBitReverse (a : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let v := (a % ((2 : Int) ^ n)).toNat
    let rec go (i : Nat) (acc : Nat) : Nat :=
      if i >= n then acc
      else go (i + 1) (acc + ((v >>> i) % 2) <<< (n - 1 - i))
    .int (go 0 0)

/-- Rotate left by `amt` positions in an n-bit field. n = 0 produces poison. -/
def evalRotateLeft (a amt : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let mask := (2 : Int) ^ n - 1
    let v := (a % ((2 : Int) ^ n)).toNat
    let s := (amt % n).toNat
    .int (((v <<< s) ||| (v >>> (n - s))) &&& mask.toNat)

/-- Rotate right by `amt` positions in an n-bit field. n = 0 produces poison. -/
def evalRotateRight (a amt : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let mask := (2 : Int) ^ n - 1
    let v := (a % ((2 : Int) ^ n)).toNat
    let s := (amt % n).toNat
    .int (((v >>> s) ||| (v <<< (n - s))) &&& mask.toNat)

/-- Unsigned saturating addition in n bits. n = 0 produces poison. -/
def evalSaturatingAdd (a b : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let maxVal := (2 : Int) ^ n - 1
    let sum := a + b
    if sum > maxVal then .int maxVal else .int sum

/-- Unsigned saturating subtraction in n bits. n = 0 produces poison. -/
def evalSaturatingSub (a b : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let diff := a - b
    if diff < 0 then .int 0 else .int diff

/-- Signed saturating addition in n bits. n = 0 produces poison.
    Result is clamped to [-(2^(n-1)), 2^(n-1)-1]. -/
def evalSignedSaturatingAdd (a b : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let minVal := -(2 : Int) ^ (n - 1)
    let maxVal := (2 : Int) ^ (n - 1) - 1
    let sum := a + b
    if sum > maxVal then .int maxVal
    else if sum < minVal then .int minVal
    else .int sum

/-- Signed saturating subtraction in n bits. n = 0 produces poison.
    Result is clamped to [-(2^(n-1)), 2^(n-1)-1]. -/
def evalSignedSaturatingSub (a b : Int) (n : Nat) : Value :=
  if n = 0 then .poison
  else
    let minVal := -(2 : Int) ^ (n - 1)
    let maxVal := (2 : Int) ^ (n - 1) - 1
    let diff := a - b
    if diff > maxVal then .int maxVal
    else if diff < minVal then .int minVal
    else .int diff

/-- Signed addition with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping sum (low n bits, sign-extended). Secondary: overflow Bool. -/
def evalSAddOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let sum := a + b
    let minVal := -(2 : Int) ^ (n - 1)
    let maxVal := (2 : Int) ^ (n - 1) - 1
    let overflowed := sum > maxVal ∨ sum < minVal
    -- Wrap: extract low n bits, then sign-extend
    let wrapped := sum % (2 ^ n : Int)
    let wrapped := if wrapped > maxVal then wrapped - (2 ^ n : Int) else wrapped
    (.int wrapped, .bool overflowed)

/-- Unsigned addition with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping sum (low n bits). Secondary: overflow Bool. -/
def evalUAddOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let sum := a + b
    let maxVal := (2 : Int) ^ n - 1
    let overflowed := sum > maxVal
    let wrapped := sum % (2 ^ n : Int)
    (.int wrapped, .bool overflowed)

/-- Signed subtraction with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping difference. Secondary: overflow Bool. -/
def evalSSubOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let diff := a - b
    let minVal := -(2 : Int) ^ (n - 1)
    let maxVal := (2 : Int) ^ (n - 1) - 1
    let overflowed := diff > maxVal ∨ diff < minVal
    let wrapped := diff % (2 ^ n : Int)
    let wrapped := if wrapped > maxVal then wrapped - (2 ^ n : Int) else wrapped
    (.int wrapped, .bool overflowed)

/-- Unsigned subtraction with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping difference. Secondary: overflow Bool. -/
def evalUSubOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let diff := a - b
    let overflowed := diff < 0
    let wrapped := diff % (2 ^ n : Int)
    let wrapped := if wrapped < 0 then wrapped + (2 ^ n : Int) else wrapped
    (.int wrapped, .bool overflowed)

/-- Signed multiplication with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping product. Secondary: overflow Bool. -/
def evalSMulOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let prod := a * b
    let minVal := -(2 : Int) ^ (n - 1)
    let maxVal := (2 : Int) ^ (n - 1) - 1
    let overflowed := prod > maxVal ∨ prod < minVal
    let wrapped := prod % (2 ^ n : Int)
    let wrapped := if wrapped > maxVal then wrapped - (2 ^ n : Int) else wrapped
    (.int wrapped, .bool overflowed)

/-- Unsigned multiplication with overflow detection in n bits. n = 0 produces poison.
    Primary result: wrapping product. Secondary: overflow Bool. -/
def evalUMulOverflow (a b : Int) (n : Nat) : Value × Value :=
  if n = 0 then (.poison, .poison)
  else
    let prod := a * b
    let maxVal := (2 : Int) ^ n - 1
    let overflowed := prod > maxVal
    let wrapped := prod % (2 ^ n : Int)
    (.int wrapped, .bool overflowed)

/-- Merge: replace the low `width` bits of `a` with the low `width` bits of `b`.
    width = 0 produces poison. -/
def evalMerge (a b : Int) (width : Nat) : Value :=
  if width = 0 then .poison
  else
    let mask := (2 : Int) ^ width - 1
    let hi := a - (a % ((2 : Int) ^ width))
    .int (hi + Int.land b mask)

/-- Split: decompose `a` at bit position `width`.
    Returns (hi, lo) where lo = low `width` bits of `a` (zero-extended),
    hi = `a` right-shifted by `width` bits.
    width = 0 produces poison. -/
def evalSplitHi (a : Int) (width : Nat) : Value :=
  if width = 0 then .poison
  else .int (a >>> width)

def evalSplitLo (a : Int) (width : Nat) : Value :=
  if width = 0 then .poison
  else .int ((a % ((2 : Int) ^ width)).toNat)

/-- Carry-less multiplication (polynomial multiplication over GF(2)).
    Multiplies two non-negative integers using XOR instead of addition
    for accumulating partial products. Negative inputs produce poison. -/
def clmulNat : Nat → Nat → Nat
  | _, 0 => 0
  | a, b + 1 =>
    let rest := clmulNat a ((b + 1) / 2)
    let shifted := rest + rest  -- left shift by 1
    if (b + 1) % 2 = 1 then Nat.xor shifted a else shifted

def evalClmul (a b : Int) : Value :=
  if a < 0 ∨ b < 0 then .poison
  else .int (clmulNat a.toNat b.toNat)

/-- Left shift. Poison if shift amount is negative. -/
def evalShl (a b : Int) : Value :=
  if b < 0 then .poison else .int (a <<< b.toNat)

/-- Right shift. Poison if shift amount is negative.
    Signedness is a property of operand annotations, not the operation.
    In infinite precision, logical and arithmetic right shift are identical. -/
def evalShr (a b : Int) : Value :=
  if b < 0 then .poison else .int (a >>> b.toNat)

/-- Integer minimum. -/
def evalMin (a b : Int) : Int := if a ≤ b then a else b

/-- Integer maximum. -/
def evalMax (a b : Int) : Int := if a ≥ b then a else b

-- Pointer operation semantics

/-- Pointer addition: offset a pointer by an integer amount.
    Preserves provenance from the base pointer. -/
def evalPtrAdd (base : Pointer) (offset : Int) : Value :=
  .ptr { allocId := base.allocId, offset := base.offset + offset }

/-- Pointer difference: compute the offset between two pointers.
    Both pointers must belong to the same allocation; otherwise poison. -/
def evalPtrDiff (a b : Pointer) : Value :=
  if a.allocId == b.allocId then .int (a.offset - b.offset) else .poison

/-- Pointer to integer: extract the offset as an integer.
    Provenance is captured (the integer "remembers" it came from a pointer). -/
def evalPtrToInt (p : Pointer) : Value := .int p.offset

/-- Pointer to address: extract the address, discarding provenance.
    Returns a plain integer with no provenance information. -/
def evalPtrToAddr (p : Pointer) : Value := .int p.offset

/-- Integer to pointer: create a pointer from an integer address.
    The resulting pointer has no valid provenance (wildcard). -/
def evalIntToPtr (addr : Int) (allocId : AllocId) : Value :=
  .ptr { allocId := allocId, offset := addr }

-- Floating point operation semantics
-- The IR adopts IEEE 754-2008 as the floating-point semantics standard.
-- These use Lean 4's native Float type (IEEE 754 binary64) as a placeholder
-- model. The formal float model will be refined when full NaN payload and
-- denormal semantics are decided.

/-- Floating point addition. -/
def evalFAdd (a b : Float) : Float := a + b

/-- Floating point subtraction. -/
def evalFSub (a b : Float) : Float := a - b

/-- Floating point multiplication. -/
def evalFMul (a b : Float) : Float := a * b

/-- Floating point division. -/
def evalFDiv (a b : Float) : Float := a / b

/-- Floating point remainder (IEEE 754 fmod: truncation toward zero).
    Lean 4's Float lacks a Mod instance, so we define it explicitly. -/
def evalFRem (a b : Float) : Float :=
  let q := a / b
  let t := if q ≥ 0.0 then q.floor else q.ceil
  a - t * b

/-- IEEE 754-2008 minNum: NaN-suppressing minimum. -/
def evalFMinNum (a b : Float) : Float :=
  if a.isNaN then b
  else if b.isNaN then a
  else if a < b then a else b

/-- IEEE 754-2008 maxNum: NaN-suppressing maximum. -/
def evalFMaxNum (a b : Float) : Float :=
  if a.isNaN then b
  else if b.isNaN then a
  else if a > b then a else b

/-- Floating point negation. -/
def evalFNeg (a : Float) : Float := -a

/-- Floating point absolute value. -/
def evalFAbs (a : Float) : Float := Float.abs a

/-- Copy sign: produce a value with the magnitude of `mag` and the sign of `sign`.
    Uses Float.toBits to check the sign bit (bit 63), correctly handling -0.0 and -NaN. -/
def evalCopySign (mag sign : Float) : Float :=
  let absMag := Float.abs mag
  if sign.toBits >>> 63 != 0 then -absMag else absMag

-- Annotation violation semantics: produce poison if constraint violated.
-- These define the semantics of :s<N> and :u<N> annotations on value
-- definitions (result-side) and use edges (use-side).

/-- Check signed range annotation :s<N>. Returns poison if value outside
    [-2^(N-1), 2^(N-1)-1]. -/
def checkSignedRange (v : Int) (n : Nat) : Value :=
  let min := -(2 ^ (n - 1))
  let max := 2 ^ (n - 1) - 1
  if min ≤ v ∧ v ≤ max then .int v else .poison

/-- Check unsigned range annotation :u<N>. Returns poison if value outside
    [0, 2^N-1]. -/
def checkUnsignedRange (v : Int) (n : Nat) : Value :=
  if 0 ≤ v ∧ v < 2 ^ n then .int v else .poison

/-- Apply an annotation to a value. Returns poison on violation. -/
def applyAnnotation (v : Int) (ann : Annotation) : Value :=
  match ann with
  | .signed n => checkSignedRange v n
  | .unsigned n => checkUnsignedRange v n
  | .dontCare n => .int (v % (2 ^ n))
  | .align _ => .int v

-- Memory load/store semantics
-- Load/store operations support int, float, vec, and byte types.
-- Array and struct types are not supported.

/-- Load a value from memory starting at address `addr`.
    The loaded value type is determined by the instruction's type annotation.
    For byte(N) types, returns a `bytes` value containing N abstract bytes.
    For int/float/vec types, the bytes are interpreted according to the type. -/
def evalLoad (mem : Memory) (addr : Int) (size : Nat) : Value :=
  .bytes (List.ofFn (fun (i : Fin size) => mem.bytes (addr + i.val)))

/-- Store a value to memory starting at address `addr`.
    The value must be of type int, float, vec, or byte(N).
    Returns the updated memory. -/
def evalStore (mem : Memory) (addr : Int) (bs : List AbstractByte) : Memory :=
  { bytes := fun a =>
      let offset := a - addr
      if 0 ≤ offset ∧ offset < bs.length then
        List.getD bs offset.toNat .uninit
      else mem.bytes a }

-- Atomic operation semantics (sequential model)

-- Integer comparison semantics

/-- Evaluate an integer comparison, returning a Bool value. -/
def evalICmp (op : ICmpOp) (a b : Int) : Value :=
  match op with
  | .eq => .bool (a == b)
  | .ne => .bool (a != b)
  | .lt => .bool (a < b)
  | .le => .bool (a ≤ b)
  | .gt => .bool (a > b)
  | .ge => .bool (a ≥ b)

/-- Evaluate a floating point comparison, returning a Bool value.
    Uses LLVM-style 4-bit predicate encoding.
    Ordered predicates return false if either operand is NaN.
    Unordered predicates return true if either operand is NaN. -/
def evalFCmp (op : FCmpOp) (a b : Float) : Value :=
  let unord := a.isNaN || b.isNaN
  match op with
  | .false_ => .bool false
  | .oeq => .bool (!unord && a == b)
  | .ogt => .bool (!unord && a > b)
  | .oge => .bool (!unord && a ≥ b)
  | .olt => .bool (!unord && a < b)
  | .ole => .bool (!unord && a ≤ b)
  | .one => .bool (!unord && a != b)
  | .ord => .bool !unord
  | .uno => .bool unord
  | .ueq => .bool (unord || a == b)
  | .ugt => .bool (unord || a > b)
  | .uge => .bool (unord || a ≥ b)
  | .ult => .bool (unord || a < b)
  | .ule => .bool (unord || a ≤ b)
  | .une => .bool (unord || a != b)
  | .true_ => .bool true

/-- Select between two values based on a boolean condition. -/
def evalSelect (cond : Bool) (tv fv : Value) : Value :=
  if cond then tv else fv

-- Memory bulk operation semantics

/-- MemCopy: copy `count` bytes from `src` to `dst` (non-overlapping, memcpy semantics).
    Reads `count` bytes starting at `src` and writes them to `dst`.
    The regions must not overlap; behavior on overlapping regions is undefined. -/
def evalMemCopy (mem : Memory) (dst src : Int) (count : Nat) : Memory :=
  let bs := List.ofFn (fun (i : Fin count) => mem.bytes (src + i.val))
  evalStore mem dst bs

/-- MemMove: copy `count` bytes from `src` to `dst` (may overlap, memmove semantics).
    Semantically equivalent to reading all source bytes first, then writing them to dst.
    Correctly handles overlapping regions. -/
def evalMemMove (mem : Memory) (dst src : Int) (count : Nat) : Memory :=
  let bs := List.ofFn (fun (i : Fin count) => mem.bytes (src + i.val))
  evalStore mem dst bs

/-- MemSet: fill `count` bytes starting at `dst` with `val` (low 8 bits).
    Writes the same byte value to each address in [dst, dst+count). -/
def evalMemSet (mem : Memory) (dst : Int) (val : UInt8) (count : Nat) : Memory :=
  let bs := List.replicate count (.bits val)
  evalStore mem dst bs

-- Atomic operation semantics (sequential model)
-- NOTE: These define sequential semantics only. A formal concurrency model
-- (e.g., based on C11 or a custom weak memory model) is TBD. Memory ordering
-- parameters are accepted but have no effect in this sequential model.

/-- Atomic load: sequentially equivalent to a regular load. -/
def evalLoadAtomic (mem : Memory) (addr : Int) (size : Nat)
    (_ordering : MemoryOrdering) : Value :=
  evalLoad mem addr size

/-- Atomic store: sequentially equivalent to a regular store. -/
def evalStoreAtomic (mem : Memory) (addr : Int) (bs : List AbstractByte)
    (_ordering : MemoryOrdering) : Memory :=
  evalStore mem addr bs

end TuffyLean.IR
