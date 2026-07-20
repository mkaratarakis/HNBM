/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Star

/-!
# Dyadic rationals: the scalar layer of the fast engine

A `Dyadic` is `man * 2^exp` with `man exp : Int`, so arithmetic is exact
integer arithmetic on GMP-backed `Int` and rounding is a bit-shift. This is
the bottom layer of the executable engine; `CRealsFast/Ball.lean` builds
interval arithmetic on top of it and `CRealsFast/FastReal.lean` builds the
precision-indexed streams on top of that.
-/
namespace Computable.Fast

/-!
## 1. The Engine: Raw Dyadic Arithmetic
A raw Dyadic number: `man * 2^exp`.
Uses `Int` (GMP) for high-performance arbitrary precision arithmetic.
-/
structure Dyadic where
  man : Int
  exp : Int
deriving Inhabited, Repr, DecidableEq

namespace Dyadic

/-- Convert to Rational for specification (not execution). -/
def toRat (d : Dyadic) : ℚ :=
  (d.man : ℚ) * (2 : ℚ) ^ d.exp

/-- `2^e` as a `Float` for `e : Int` (handles negative exponents). -/
@[inline] def pow2Float (e : Int) : Float :=
  Float.pow 2.0 (Float.ofInt e)

/-- Convert to Float for human-readable `#eval` output. -/
def toFloat (d : Dyadic) : Float :=
  (Float.ofInt d.man) * pow2Float d.exp

instance : ToString Dyadic where
  toString d := toString (d.toFloat)

/--
**Fast Rounding**:
Reduces precision using bit-shifts. Rounds to nearest (ties to even/up).
Target: Result will have exponent `min_exp`.
-/
@[inline] private def pow2Int (k : Nat) : Int :=
  (1 : Int) <<< k

/-- Round down (toward `-∞`) to the target exponent `min_exp`. -/
@[inline] def roundDown (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    { man := d.man >>> shift, exp := min_exp }

/-- Round up (toward `+∞`) to the target exponent `min_exp`. -/
@[inline] def roundUp (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := pow2Int shift
    let q := d.man >>> shift
    let r := d.man % denom
    { man := if r == 0 then q else q + 1, exp := min_exp }

/-- Round to nearest; ties go to even (banker's rounding). -/
@[inline] def round (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := pow2Int shift
    let q := d.man >>> shift
    let r := d.man % denom
    let half : Int := denom >>> 1
    let q' :=
      if r < half then q
      else if r > half then q + 1
      else if q % 2 == 0 then q else q + 1
    { man := q', exp := min_exp }

def neg (a : Dyadic) : Dyadic :=
  { man := -a.man, exp := a.exp }

def add (a b : Dyadic) : Dyadic :=
  -- Align exponents
  if a.exp <= b.exp then
    let shift := (b.exp - a.exp).toNat
    { man := a.man + (b.man <<< shift), exp := a.exp }
  else
    let shift := (a.exp - b.exp).toNat
    { man := (a.man <<< shift) + b.man, exp := b.exp }

def mul (a b : Dyadic) : Dyadic :=
  { man := a.man * b.man, exp := a.exp + b.exp }

def abs (a : Dyadic) : Dyadic :=
  { man := a.man.natAbs, exp := a.exp }

instance : Zero Dyadic := ⟨⟨0, 0⟩⟩
instance : One Dyadic := ⟨⟨1, 0⟩⟩

instance : Add Dyadic := ⟨add⟩
instance : Mul Dyadic := ⟨mul⟩
instance : Neg Dyadic := ⟨neg⟩

def lt (a b : Dyadic) : Prop :=
  if a.exp <= b.exp then
    let shift := (b.exp - a.exp).toNat
    a.man < (b.man <<< shift)
  else
    let shift := (a.exp - b.exp).toNat
    (a.man <<< shift) < b.man

instance : LT Dyadic := ⟨lt⟩
instance (a b : Dyadic) : Decidable (a < b) := by
  change Decidable (Dyadic.lt a b)
  unfold Dyadic.lt
  by_cases h : a.exp <= b.exp
  · simp [h]; exact a.man.decLt (b.man <<< (b.exp - a.exp).toNat)
  · simp [h]; exact (a.man <<< (a.exp - b.exp).toNat).decLt b.man

def le (a b : Dyadic) : Prop := a < b ∨ a = b
instance : LE Dyadic := ⟨le⟩
instance (a b : Dyadic) : Decidable (a ≤ b) :=
  if h : a < b then isTrue (Or.inl h)
  else if h' : a = b then isTrue (Or.inr h')
  else isFalse (fun | Or.inl l => h l | Or.inr e => h' e)

@[inline] private def divPow2Ceil (n : Int) (k : Nat) : Int :=
  let denom : Int := pow2Int k
  let q := n >>> k
  let r := n % denom
  if r == 0 then q else q + 1

/-- Square root, rounded down (toward `-∞`) at target exponent `prec`. -/
def sqrt (d : Dyadic) (prec : Int) : Dyadic :=
  if d.man < 0 then { man := 0, exp := prec }
  else
    let shift_amount := d.exp - 2 * prec
    let val : Int :=
      if shift_amount >= 0 then d.man <<< shift_amount.toNat
      else d.man >>> (-shift_amount).toNat
    let valNat : Nat := val.toNat
    let s : Nat := Nat.sqrt valNat
    { man := s, exp := prec }

/-- Square root, rounded up (toward `+∞`) at target exponent `prec`. -/
def sqrtUp (d : Dyadic) (prec : Int) : Dyadic :=
  if d.man < 0 then { man := 0, exp := prec }
  else
    let shift_amount := d.exp - 2 * prec
    let val : Int :=
      if shift_amount >= 0 then d.man <<< shift_amount.toNat
      else divPow2Ceil d.man (-shift_amount).toNat
    let valNat : Nat := val.toNat
    let s : Nat := Nat.sqrt valNat
    let s' : Nat := if s * s == valNat then s else s + 1
    { man := s', exp := prec }

@[inline] def normalizeDivisor (num den : Int) : Int × Int :=
  if den < 0 then (-num, -den) else (num, den)

@[inline] def scaledNumDen (a b : Dyadic) (prec : Int) : Int × Int :=
  let shift := a.exp - b.exp - prec
  if shift >= 0 then
    (a.man <<< shift.toNat, b.man)
  else
    (a.man, b.man <<< (-shift).toNat)

/--
Divide dyadics at target exponent `prec`, rounding down (toward `-∞`).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def divDown (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    { man := num / den, exp := prec }

/--
Divide dyadics at target exponent `prec`, rounding up (toward `+∞`).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def divUp (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    let q := num / den
    let r := num % den
    { man := if r == 0 then q else q + 1, exp := prec }

/--
Divide dyadics at target exponent `prec`, rounding to nearest (ties to even).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def div (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    let q := num / den
    let r := num % den
    let two_r := 2 * r
    let q' :=
      if two_r < den then q
      else if two_r > den then q + 1
      else if q % 2 == 0 then q else q + 1
    { man := q', exp := prec }

def sub (a b : Dyadic) : Dyadic := add a (neg b)
instance : Sub Dyadic := ⟨sub⟩

def floor (d : Dyadic) : Int :=
  if d.exp >= 0 then d.man * ((1 : Int) <<< d.exp.toNat)
  else d.man >>> (-d.exp).toNat

def ceil (d : Dyadic) : Int :=
  if d.exp >= 0 then d.man * ((1 : Int) <<< d.exp.toNat)
  else
    let shift := (-d.exp).toNat
    let mask := ((1 : Int) <<< shift) - 1
    (d.man + mask) >>> shift

def sign (d : Dyadic) : Int :=
  if d.man > 0 then 1 else if d.man < 0 then -1 else 0

def shiftl (d : Dyadic) (k : Int) : Dyadic :=
  { man := d.man, exp := d.exp + k }

def approxRat (q : ℚ) (n : Nat) : Dyadic :=
  let e := -(n : Int)
  let m := (q * (2 : ℚ)^n).floor
  { man := m, exp := e }

end Dyadic

end Computable.Fast
