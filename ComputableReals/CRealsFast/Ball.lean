/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CRealsFast.Dyadic

/-!
# Ball arithmetic: midpoint ± radius over the dyadics

A `Ball` is a dyadic midpoint with a dyadic radius, i.e. a rigorous
enclosure of a real number. Every operation takes a target precision and
returns a ball guaranteed to contain the true result. Soundness is proved
in `Computable/Preservation.lean` and its successors.
-/
namespace Computable.Fast

/-! # 2. The Container: Interval (Ball) Arithmetic -/

/-- A Ball [mid ± rad]. -/
structure Ball where
  mid : Dyadic
  rad : Dyadic
deriving Repr, DecidableEq, Inhabited

namespace Ball

def zero : Ball := ⟨⟨0,0⟩, ⟨0,0⟩⟩
def one  : Ball := ⟨⟨1,0⟩, ⟨0,0⟩⟩

/--
**Precision Manager**:
Operations take a `prec` argument (target exponent, e.g., -64).
We round the result to this precision to stop expression swell.
-/
def add (x y : Ball) (prec : Int) : Ball :=
  let raw_mid := x.mid + y.mid
  let new_mid := raw_mid.round prec
  -- Rounding error bound: 2^(prec-1), incurred only if rounding changed the midpoint.
  -- Keeping exact results exact lets `compare` decide equalities of dyadic values.
  let err : Dyadic := if new_mid == raw_mid then ⟨0, 0⟩ else ⟨1, prec - 1⟩
  -- Radius: r1 + r2 + error
  let raw_rad := x.rad + y.rad + err
  { mid := new_mid, rad := raw_rad.abs.roundUp prec }

def neg (x : Ball) : Ball :=
  { mid := -x.mid, rad := x.rad }

def mul (x y : Ball) (prec : Int) : Ball :=
  let raw_mid := x.mid * y.mid
  let new_mid := raw_mid.round prec
  -- Rounding error incurred only if rounding changed the midpoint (see `add`).
  let err : Dyadic := if new_mid == raw_mid then ⟨0, 0⟩ else ⟨1, prec - 1⟩
  -- Product rule error: |x|ry + |y|rx + rx*ry
  let term1 := x.mid.abs * y.rad
  let term2 := y.mid.abs * x.rad
  let term3 := x.rad * y.rad
  let raw_rad := term1 + term2 + term3 + err
  { mid := new_mid, rad := raw_rad.abs.roundUp prec }

def ofDyadic (d : Dyadic) : Ball := ⟨d, ⟨0, 0⟩⟩

@[inline] def lo (b : Ball) : Dyadic := b.mid - b.rad
@[inline] def hi (b : Ball) : Dyadic := b.mid + b.rad

/--
Build a `Ball` enclosing the dyadic interval `[lo, hi]`, rounded to exponent `prec`.

This is the main “interval-to-ball” adapter; it takes care of midpoint rounding error.
-/
def ofInterval (lo hi : Dyadic) (prec : Int) : Ball :=
  let half : Dyadic := ⟨1, -1⟩
  let raw_mid := (lo + hi) * half
  let new_mid := raw_mid.round prec
  let err : Dyadic := ⟨1, prec - 1⟩
  let raw_rad := (hi - lo).abs * half + err
  { mid := new_mid, rad := raw_rad.roundUp prec }

/-- Upper bound on `|x|` for any `x` in this ball. -/
def absUpper (b : Ball) : Dyadic :=
  let lo := b.lo
  let hi := b.hi
  let alo := lo.abs
  let ahi := hi.abs
  if alo < ahi then ahi else alo

/-- Scale by a power of two: `scale2 b k` represents `b * 2^k`. -/
@[inline] def scale2 (b : Ball) (k : Int) : Ball :=
  { mid := b.mid.shiftl k, rad := b.rad.shiftl k }

def sqrt (x : Ball) (prec : Int) : Ball :=
  let lo := x.lo
  let hi := x.hi
  if hi.man < 0 then zero
  else
    let lo' : Dyadic := if lo.man < 0 then 0 else lo
    ofInterval (lo'.sqrt prec) (hi.sqrtUp prec) prec

def abs (x : Ball) (prec : Int) : Ball :=
  let lo := x.lo
  let hi := x.hi
  if lo.man >= 0 then
    ofInterval lo hi prec
  else if hi.man <= 0 then
    ofInterval (-hi) (-lo) prec
  else
    let neg_lo : Dyadic := -lo
    let m : Dyadic := if neg_lo < hi then hi else neg_lo
    ofInterval 0 m prec

def pow (x : Ball) (n : Nat) (prec : Int) : Ball :=
  Nat.rec (motive := fun _ => Ball) one (fun _ acc => mul acc x prec) n

def floor (b : Ball) : Option Int :=
  let min := b.mid - b.rad
  let max := b.mid + b.rad
  let f_min := min.floor
  let f_max := max.floor
  if f_min == f_max then some f_min else none

def ceil (b : Ball) : Option Int :=
  let min := b.mid - b.rad
  let max := b.mid + b.rad
  let c_min := min.ceil
  let c_max := max.ceil
  if c_min == c_max then some c_min else none

def min (x y : Ball) (prec : Int) : Ball :=
  let x_lo := x.lo
  let x_hi := x.hi
  let y_lo := y.lo
  let y_hi := y.hi
  let m_lo := if x_lo < y_lo then x_lo else y_lo
  let m_hi := if x_hi < y_hi then x_hi else y_hi
  ofInterval m_lo m_hi prec

def max (x y : Ball) (prec : Int) : Ball :=
  let x_lo := x.lo
  let x_hi := x.hi
  let y_lo := y.lo
  let y_hi := y.hi
  let m_lo := if x_lo < y_lo then y_lo else x_lo
  let m_hi := if x_hi < y_hi then y_hi else x_hi
  ofInterval m_lo m_hi prec

/--
Reciprocal of a ball at precision `prec`, if the interval is separated from `0`.

Returns `none` if the interval straddles `0`, because the image of the interval under
`x ↦ 1/x` is unbounded.
-/
def inv? (x : Ball) (prec : Int) : Option Ball :=
  let lo := x.lo
  let hi := x.hi
  if hi.man < 0 then
    -- lo < hi < 0, so `1/hi ≤ 1/x ≤ 1/lo`
    let loInv := Dyadic.divDown 1 hi prec
    let hiInv := Dyadic.divUp 1 lo prec
    some (ofInterval loInv hiInv prec)
  else if lo.man > 0 then
    -- 0 < lo ≤ hi, so `1/hi ≤ 1/x ≤ 1/lo`
    let loInv := Dyadic.divDown 1 hi prec
    let hiInv := Dyadic.divUp 1 lo prec
    some (ofInterval loInv hiInv prec)
  else
    none

/-- Divide `x` by `y` at precision `prec`, if `y` is separated from `0`. -/
def div? (x y : Ball) (prec : Int) : Option Ball := do
  let invy ← inv? y prec
  pure (mul x invy prec)

/-- Reciprocal of a nonzero dyadic, as a `Ball`. -/
def invDyadic? (d : Dyadic) (prec : Int) : Option Ball :=
  if d.man == 0 then none
  else
    let lo := Dyadic.divDown 1 d prec
    let hi := Dyadic.divUp 1 d prec
    some (ofInterval lo hi prec)

@[inline] private def invDyadic (d : Dyadic) (prec : Int) : Ball :=
  (invDyadic? d prec).getD zero

@[inline] private def divDyadic (x : Ball) (d : Dyadic) (prec : Int) : Ball :=
  mul x (invDyadic d prec) prec

def exp (x : Ball) (prec : Int) : Ball :=
  -- Scale down so that `|x_small|` is tiny (≈ ≤ 1/4), making the Taylor tail easy to bound.
  let u := x.absUpper
  let mag := u.exp + (if u.man = 0 then 0 else u.man.natAbs.log2)
  let k : Int := if mag > -2 then mag + 2 else 0
  let k_nat := k.toNat
  let x_small := x.scale2 (-k)

  -- Stop once the next term is below this threshold.
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- term₀ = 1, sum₀ = 1, term_{i+1} = term_i * x / (i+1)
  let rec taylor (fuel : Nat) (term sum : Ball) (i : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let i1 := i + 1
      let term' := divDyadic (mul term x_small prec) ⟨(i1 : Int), 0⟩ prec
      let sum' := add sum term' prec
      if term'.absUpper < tol then
        -- With `|x_small| ≤ 1/4`, the remaining tail is bounded by a small geometric series.
        -- A simple safe bound is `2 * |term'|`.
        let tail := (term'.absUpper * ⟨2, 0⟩).roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        taylor fuel term' sum' i1

  let y_small := taylor maxTerms one one 0

  let rec square (y : Ball) : Nat → Ball
    | 0 => y
    | count + 1 => square (mul y y prec) count

  square y_small k_nat

def ln2 (prec : Int) : Ball :=
  let y := divDyadic one ⟨3, 0⟩ prec
  let y2 := mul y y prec
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- ln(2) = 2 * Σ_{k>=0} (y^(2k+1) / (2k+1)), with y = 1/3 (geometric decay, ratio = 1/9).
  let rec loop (fuel : Nat) (t sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let term := divDyadic t ⟨(2 * k + 1 : Int), 0⟩ prec
      let sum' := add sum term prec
      let t' := mul t y2 prec
      let k' := k + 1
      let termNext := divDyadic t' ⟨(2 * k' + 1 : Int), 0⟩ prec
      if termNext.absUpper < tol then
        let tail := (termNext.absUpper * ⟨2, 0⟩).roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        loop fuel t' sum' k'

  let s := loop maxTerms y zero 0
  mul s (ofDyadic ⟨2, 0⟩) prec

/--
Natural logarithm on balls, as a **partial** operation.

We return `none` unless the ball is *provably positive* (its lower endpoint is `> 0`).
-/
def log? (x : Ball) (prec : Int) : Option Ball := do
  let lo := x.lo
  if lo.man <= 0 then none
  else
    let m := x.mid.man
    let e := x.mid.exp
    let shift := - ((m.natAbs.log2 : Int) + e)
    let x_norm := mul x (ofDyadic ⟨1, shift⟩) prec
    let num := add x_norm (neg one) prec
    let den := add x_norm one prec
    let y ← div? num den prec
    -- For the atanh-series to converge quickly, we want |y| ≤ 1/2.
    if y.absUpper < (⟨1, -1⟩ : Dyadic) then
      pure ()
    else
      none
    let y2 := mul y y prec
    let tol : Dyadic := ⟨1, prec - 4⟩
    let maxTerms : Nat := (-prec).toNat + 64

    -- log(x) = 2 * atanh(y), where y = (x-1)/(x+1) and atanh(y) = Σ y^(2k+1)/(2k+1).
    let rec loop (fuel : Nat) (t sum : Ball) (k : Nat) : Ball :=
      match fuel with
      | 0 => sum
      | fuel + 1 =>
        let term := divDyadic t ⟨(2 * k + 1 : Int), 0⟩ prec
        let sum' := add sum term prec
        let t' := mul t y2 prec
        let k' := k + 1
        let termNext := divDyadic t' ⟨(2 * k' + 1 : Int), 0⟩ prec
        if termNext.absUpper < tol then
          let tail := (termNext.absUpper * ⟨2, 0⟩).roundUp prec
          { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
        else
          loop fuel t' sum' k'

    let s := loop maxTerms y zero 0
    let ln_x_norm := mul s (ofDyadic ⟨2, 0⟩) prec
    let ln_2 := ln2 prec
    let shift_val := ofDyadic ⟨shift, 0⟩
    let term_shift := mul shift_val (neg ln_2) prec
    pure (add ln_x_norm term_shift prec)

@[inline] private def sinCosSmall (x : Ball) (prec : Int) : Ball × Ball :=
  let x2 := mul x x prec
  let neg_x2 := neg x2
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- sin(x) = Σ (-1)^k x^(2k+1)/(2k+1)!
  let rec sinLoop (fuel : Nat) (term sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let sum' := add sum term prec
      let denom := (2 * k + 2) * (2 * k + 3)
      let term' := divDyadic (mul term neg_x2 prec) ⟨(denom : Int), 0⟩ prec
      if term'.absUpper < tol then
        let tail := term'.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        sinLoop fuel term' sum' (k + 1)

  -- cos(x) = Σ (-1)^k x^(2k)/(2k)!
  let rec cosLoop (fuel : Nat) (term sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let sum' := add sum term prec
      let denom := (2 * k + 1) * (2 * k + 2)
      let term' := divDyadic (mul term neg_x2 prec) ⟨(denom : Int), 0⟩ prec
      if term'.absUpper < tol then
        let tail := term'.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        cosLoop fuel term' sum' (k + 1)

  (sinLoop maxTerms x zero 0, cosLoop maxTerms one zero 0)

@[inline] private def sinCos (x : Ball) (prec : Int) : Ball × Ball :=
  -- Scale down so the Taylor series converges very quickly.
  let u := x.absUpper
  let mag := u.exp + (if u.man = 0 then 0 else u.man.natAbs.log2)
  let k : Int := if mag > -2 then mag + 2 else 0
  let k_nat := k.toNat
  let x_small := x.scale2 (-k)
  let (s0, c0) := sinCosSmall x_small prec

  let two : Ball := ofDyadic ⟨2, 0⟩
  let rec dbl (s c : Ball) : Nat → Ball × Ball
    | 0 => (s, c)
    | n + 1 =>
      let s2 := mul two (mul s c prec) prec
      let c2 := add (mul c c prec) (neg (mul s s prec)) prec
      dbl s2 c2 n

  dbl s0 c0 k_nat

def sin (x : Ball) (prec : Int) : Ball :=
  (sinCos x prec).1

def cos (x : Ball) (prec : Int) : Ball :=
  (sinCos x prec).2

def atan (x : Ball) (prec : Int) : Ball :=
  let quarter : Dyadic := ⟨1, -2⟩ -- 1/4
  let rec reduce (z : Ball) (scale : Nat) (fuel : Nat) : Ball × Nat :=
    match fuel with
    | 0 => (z, scale)
    | fuel + 1 =>
      if z.absUpper < quarter then
        (z, scale)
      else
        let sq := mul z z prec
        let one_plus_sq := add one sq prec
        let root := sqrt one_plus_sq prec
        let den := add one root prec
        match div? z den prec with
        | some z_new => reduce z_new (scale + 1) fuel
        | none => (z, scale)

  let (z_small, scale) := reduce x 0 32

  let z2 := mul z_small z_small prec
  let neg_z2 := neg z2
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- atan(z) = Σ (-1)^k z^(2k+1)/(2k+1)
  -- We keep `powTerm = (-1)^k * z^(2k+1)` (no denominator), and divide by `(2k+1)` when adding.
  let rec loop (fuel : Nat) (powTerm sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let denom := 2 * k + 1
      let term := divDyadic powTerm ⟨(denom : Int), 0⟩ prec
      let sum' := add sum term prec
      let powTerm' := mul powTerm neg_z2 prec
      if term.absUpper < tol then
        let tail := term.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        loop fuel powTerm' sum' (k + 1)

  let res := loop maxTerms z_small zero 0
  mul res (ofDyadic ⟨1, (scale : Int)⟩) prec

def pi (prec : Int) : Ball :=
  let one_fifth := divDyadic one ⟨5, 0⟩ prec
  let one_239 := divDyadic one ⟨239, 0⟩ prec
  let at1 := atan one_fifth prec
  let at2 := atan one_239 prec
  let t1 := mul at1 (ofDyadic ⟨16, 0⟩) prec
  let t2 := mul at2 (ofDyadic ⟨4, 0⟩) prec
  add t1 (neg t2) prec

def tan? (x : Ball) (prec : Int) : Option Ball := do
  let s := sin x prec
  let c := cos x prec
  div? s c prec

end Ball

end Computable.Fast
