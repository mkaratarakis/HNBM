/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CRealsFast.Ball

/-!
# `FastReal`: precision-indexed streams of balls

`FastReal = ℕ → Ball`, where the ball at index `n` is an enclosure accurate
to roughly `2^-n`. This is the executable real number type, carrying the
arithmetic, the transcendental functions, and the total fuel-based
`compare` that decides order (including exact ties) or honestly answers
`none`.
-/
namespace Computable.Fast

/-! # 3. FastReal (The Stream) -/

/--
**FastReal**: A function `ℕ → Ball`.
`n` represents the requested precision index (approx bits).
-/
def FastReal := ℕ → Ball

namespace FastReal

def ofDyadic (d : Dyadic) : FastReal := fun _ => Ball.ofDyadic d

instance : Zero FastReal := ⟨fun _ => Ball.zero⟩
instance : One FastReal := ⟨fun _ => Ball.one⟩
instance : Coe Dyadic FastReal := ⟨ofDyadic⟩
instance : OfNat FastReal n := ⟨ofDyadic ⟨n, 0⟩⟩

/--
**Addition**:
To satisfy precision `n`, we calculate at `n+2` to absorb rounding errors,
then round the result to `n`.
-/
def add (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  -- Pull slightly higher precision from inputs
  Ball.add (x (n + 4)) (y (n + 4)) prec

def neg (x : FastReal) : FastReal := fun n =>
  Ball.neg (x n)

/--
**Multiplication**:
We employ a heuristic. We peek at the magnitude of the numbers at low precision
to determine how much extra precision is needed to mask the error scaling.
-/
def mul (x y : FastReal) : FastReal := fun n =>
  -- 1. Peek at magnitude (Index 0)
  let x_mag := (x 0).mid.exp
  let y_mag := (y 0).mid.exp
  -- 2. Dynamic precision adjustment
  -- If numbers are large (exp > 0), we need more bits.
  let guard := Int.natAbs (x_mag + y_mag) + 4
  let lookahead := n + guard
  let prec := -((n : Int) + 2)
  Ball.mul (x lookahead) (y lookahead) prec

def sqrt (x : FastReal) : FastReal := fun n =>
  -- Peek at magnitude
  let x_0 := x 0
  let mag := x_0.mid.exp
  -- If number is small, we need more precision from input
  let extra := if mag < 0 then ((-mag).toNat / 2) + 4 else 2
  let lookahead := n + extra
  let prec := -((n : Int) + 2)
  Ball.sqrt (x lookahead) prec

def exp (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.exp (x lookahead) prec

def sin (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.sin (x lookahead) prec

def cos (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.cos (x lookahead) prec

def atan (x : FastReal) : FastReal := fun n =>
  let x0 := x 0
  let mag := x0.mid.exp
  let extra := if mag > 0 then mag.toNat else 0
  let lookahead := n + 10
  let prec := -((n : Int) + 2 + extra)
  Ball.atan (x lookahead) prec

def pi : FastReal := fun n =>
  let prec := -((n : Int) + 6)
  Ball.pi prec

/-!
### Partial operations

Some operations (reciprocal, division, `log`, `tan`) are **not computable as total functions**
on all computable reals. We therefore expose them as *partial approximators*:
they return `Option Ball` at each requested precision.
-/

/-- Approximate reciprocal; returns `none` if we can't certify separation from `0` at this
precision. -/
def inv? (x : FastReal) : ℕ → Option Ball := fun n =>
  let x0 := x 0
  let k := x0.mid.exp
  let extra := if k < 0 then 2 * (-k).toNat else 0
  let lookahead := n + extra + 4
  let prec := -((n : Int) + 2)
  Ball.inv? (x lookahead) prec

/-- Approximate division; returns `none` if we can't certify the denominator is separated from `0`.
-/
def div? (x y : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.div? (x lookahead) (y lookahead) prec

/-- Approximate natural logarithm; returns `none` unless we can certify the input is positive. -/
def log? (x : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.log? (x lookahead) prec

/-- Approximate logarithm base `b`; returns `none` if either log is undefined or division can't be
certified. -/
def logBase? (b x : FastReal) : ℕ → Option Ball := fun n => do
  let prec := -((n : Int) + 2)
  let lx ← log? x n
  let lb ← log? b n
  Ball.div? lx lb prec

/-- Approximate tangent; returns `none` if we can't certify `cos x` is separated from `0`. -/
def tan? (x : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.tan? (x lookahead) prec

/-!
### Decimal rendering (for `#eval`)

These helpers avoid `Float` and instead render dyadic/rational approximations as decimal strings.
They are intended for debugging / demos, not high-performance numerics.
-/

def ratToDecimal (q : ℚ) (digits : Nat) : String :=
  let sign := if q < 0 then "-" else ""
  let q' : ℚ := if q < 0 then -q else q
  let intPart : Nat := q'.floor.toNat
  let fracPart : ℚ := q' - intPart
  let rec go (k : Nat) (r : ℚ) (acc : String) : String :=
    match k with
    | 0 => acc
    | k + 1 =>
      let r' := 10 * r
      let digit : Nat := r'.floor.toNat
      go k (r' - digit) (acc ++ toString digit)
  sign ++ toString intPart ++ "." ++ go digits fracPart ""

def ballToDecimalMidRad (b : Ball) (digits : Nat) : String :=
  s!"[{ratToDecimal b.mid.toRat digits} ± {ratToDecimal b.rad.toRat digits}]"

def ballToDecimalInterval (b : Ball) (digits : Nat) : String :=
  s!"[{ratToDecimal b.lo.toRat digits}, {ratToDecimal b.hi.toRat digits}]"

def toDecimal (x : FastReal) (digits : Nat := 10) : String :=
  let n := 4 * digits
  ballToDecimalMidRad (x n) digits

def toDecimalInterval (x : FastReal) (digits : Nat := 10) : String :=
  let n := 4 * digits
  ballToDecimalInterval (x n) digits

def abs (x : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.abs (x n) prec

def pow (x : FastReal) (k : Nat) : FastReal := fun n =>
  if k == 0 then Ball.one
  else
    let x0 := x 0
    let mag := x0.mid.exp
    let extra := if mag > 0 then (k - 1) * mag.toNat else 0
    let lookahead := n + extra + k.log2 + 4
    let prec := -((n : Int) + 2)
    Ball.pow (x lookahead) k prec

def floor (x : FastReal) (fuel : Nat := 100) : Option Int :=
  let rec loop : Nat → Nat → Option Int
    | _, 0 => none
    | i, fuel + 1 =>
      match (x i).floor with
      | some f => some f
      | none => loop (i + 1) fuel
  loop 0 (fuel + 1)

def ceil (x : FastReal) (fuel : Nat := 100) : Option Int :=
  let rec loop : Nat → Nat → Option Int
    | _, 0 => none
    | i, fuel + 1 =>
      match (x i).ceil with
      | some c => some c
      | none => loop (i + 1) fuel
  loop 0 (fuel + 1)

def compare (x y : FastReal) (fuel : Nat := 100) : Option Ordering :=
  let rec loop : Nat → Nat → Option Ordering
    | _, 0 => none
    | i, fuel + 1 =>
      let bx := x i
      let byy := y i
      let x_max := bx.mid + bx.rad
      let x_min := bx.mid - bx.rad
      let y_max := byy.mid + byy.rad
      let y_min := byy.mid - byy.rad
      if x_max < y_min then some Ordering.lt
      else if y_max < x_min then some Ordering.gt
      else if bx.rad.man == 0 && byy.rad.man == 0 then
        -- Both balls are exact points: compare the midpoints exactly.
        -- This decides *equalities* of exact dyadic values (e.g. ties in
        -- threshold comparisons with integer weights), which interval
        -- refinement alone could never decide.
        if bx.mid < byy.mid then some Ordering.lt
        else if byy.mid < bx.mid then some Ordering.gt
        else some Ordering.eq
      else loop (i + 1) fuel
  loop 0 (fuel + 1)

def min (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.min (x n) (y n) prec

def max (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.max (x n) (y n) prec

def isPos (x : FastReal) (fuel : Nat := 100) : Option Bool :=
  match compare x 0 fuel with
  | some Ordering.gt => some true
  | some _ => some false
  | none => none

def isNeg (x : FastReal) (fuel : Nat := 100) : Option Bool :=
  match compare x 0 fuel with
  | some Ordering.lt => some true
  | some _ => some false
  | none => none

def sign (x : FastReal) (fuel : Nat := 100) : Option Int :=
  match compare x 0 fuel with
  | some Ordering.lt => some (-1)
  | some Ordering.gt => some 1
  | some Ordering.eq => some 0
  | none => none

def hypot (x y : FastReal) : FastReal :=
  sqrt (add (mul x x) (mul y y))

instance : Add FastReal := ⟨add⟩
instance : Sub FastReal := ⟨fun a b => add a (neg b)⟩
instance : Mul FastReal := ⟨mul⟩
instance : Neg FastReal := ⟨neg⟩
instance : Pow FastReal ℕ := ⟨pow⟩
instance : Min FastReal := ⟨min⟩
instance : Max FastReal := ⟨max⟩

instance : SMul ℤ FastReal where
  smul z f := mul (ofDyadic ⟨z, 0⟩) f

-- Pretty printer: Eval at index 20 (~6 decimal digits)
instance : Repr FastReal where
  reprPrec f _ :=
    let b := f 20
    s!"[{b.mid.toFloat} ± {b.rad.toFloat}]"

end FastReal

end Computable.Fast
