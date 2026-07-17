import HopfieldNet.CReals.CRealsFast

/-!
# FastComplex: executable computable complex numbers

A computable complex number is a pair of `FastReal`s (precision-indexed ball
oracles). Everything here is **purely executable** (usable with `#eval`),
following the design of `CRealsFast.lean`:

- Total operations (`add`, `mul`, `conj`, `normSq`, `abs`, `exp`, `sqrt`, `pow`)
  are ordinary functions.
- Operations that are **not computable as total functions** on all computable
  complex numbers are exposed as partial approximators returning `Option`:
  - `inv?`, `div?` (need the denominator apart from `0`),
  - `arg?`, `log?` (discontinuous on the closed negative real axis).

`sqrt` is total in the *enclosure* sense: on the branch cut with an
imaginary part whose sign cannot be certified, it returns a valid but
non-shrinking ball for the imaginary component instead of failing.
-/

namespace Computable.Fast

namespace Ball

/--
Two-argument arctangent on balls: an enclosure of `arg (x + y*I)` in `(-π, π]`,
as a **partial** operation.

Returns `none` when neither `x > 0` nor the sign of `y` can be certified —
in particular on (a neighbourhood of) the closed negative real axis, where
`arg` is discontinuous and hence not computable.
-/
def atan2? (y x : Ball) (prec : Int) : Option Ball :=
  let halfPi := mul (pi prec) (ofDyadic ⟨1, -1⟩) prec
  if x.lo.man > 0 then do
    -- Right half-plane: arg = atan (y/x).
    let q ← div? y x prec
    pure (atan q prec)
  else if y.lo.man > 0 then do
    -- Upper half-plane: arg = π/2 - atan (x/y), valid for every x.
    let q ← div? x y prec
    pure (add halfPi (neg (atan q prec)) prec)
  else if y.hi.man < 0 then do
    -- Lower half-plane: arg = -π/2 - atan (x/y), valid for every x.
    let q ← div? x y prec
    pure (add (neg halfPi) (neg (atan q prec)) prec)
  else
    none

end Ball

namespace FastReal

/-- Two-argument arctangent, as a partial approximator (see `Ball.atan2?`). -/
def atan2? (y x : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.atan2? (y lookahead) (x lookahead) prec

end FastReal

/-- A computable complex number: real and imaginary parts as `FastReal`s. -/
structure FastComplex where
  re : FastReal
  im : FastReal

namespace FastComplex

def ofFastReal (x : FastReal) : FastComplex := ⟨x, 0⟩

def ofDyadic (d : Dyadic) : FastComplex := ⟨FastReal.ofDyadic d, 0⟩

/-- The imaginary unit. -/
def I : FastComplex := ⟨0, 1⟩

instance : Zero FastComplex := ⟨⟨0, 0⟩⟩
instance : One FastComplex := ⟨⟨1, 0⟩⟩
instance : Coe FastReal FastComplex := ⟨ofFastReal⟩
instance : Coe Dyadic FastComplex := ⟨ofDyadic⟩
instance : OfNat FastComplex n := ⟨⟨FastReal.ofDyadic ⟨n, 0⟩, 0⟩⟩

def add (z w : FastComplex) : FastComplex :=
  ⟨z.re + w.re, z.im + w.im⟩

def neg (z : FastComplex) : FastComplex :=
  ⟨FastReal.neg z.re, FastReal.neg z.im⟩

def sub (z w : FastComplex) : FastComplex :=
  ⟨z.re - w.re, z.im - w.im⟩

def mul (z w : FastComplex) : FastComplex :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def conj (z : FastComplex) : FastComplex :=
  ⟨z.re, FastReal.neg z.im⟩

/-- Scale by a real. -/
def smul (x : FastReal) (z : FastComplex) : FastComplex :=
  ⟨x * z.re, x * z.im⟩

instance : Add FastComplex := ⟨add⟩
instance : Sub FastComplex := ⟨sub⟩
instance : Neg FastComplex := ⟨neg⟩
instance : Mul FastComplex := ⟨mul⟩
instance : SMul FastReal FastComplex := ⟨smul⟩

def pow (z : FastComplex) : Nat → FastComplex
  | 0 => 1
  | n + 1 => mul (pow z n) z

instance : Pow FastComplex ℕ := ⟨pow⟩

/-- Squared absolute value `re² + im²`, as a (total) `FastReal`. -/
def normSq (z : FastComplex) : FastReal :=
  z.re * z.re + z.im * z.im

/-- Absolute value `|z| = √(re² + im²)`, as a (total) `FastReal`. -/
def abs (z : FastComplex) : FastReal :=
  FastReal.hypot z.re z.im

/-- Complex exponential: `exp (a + b*I) = exp a * (cos b + sin b * I)`. Total. -/
def exp (z : FastComplex) : FastComplex :=
  let r := FastReal.exp z.re
  ⟨r * FastReal.cos z.im, r * FastReal.sin z.im⟩

/-- A pure phase `e^{iθ} = cos θ + i sin θ` (cheaper than `exp ⟨0, θ⟩`). Total. -/
def phase (θ : FastReal) : FastComplex :=
  ⟨FastReal.cos θ, FastReal.sin θ⟩

/-- Polar constructor `r·e^{iθ}`. Total. -/
def fromPolar (r θ : FastReal) : FastComplex :=
  ⟨r * FastReal.cos θ, r * FastReal.sin θ⟩

/-- `cos z = (exp (I*z) + exp (-I*z)) / 2`, computed componentwise. Total. -/
def cos (z : FastComplex) : FastComplex :=
  -- cos (a + b*I) = cos a * cosh b - sin a * sinh b * I, via exp of ±b.
  let eb := FastReal.exp z.im
  let enb := FastReal.exp (FastReal.neg z.im)
  let half : FastReal := FastReal.ofDyadic ⟨1, -1⟩
  let ch := (eb + enb) * half
  let sh := (eb - enb) * half
  ⟨FastReal.cos z.re * ch, FastReal.neg (FastReal.sin z.re * sh)⟩

/-- `sin (a + b*I) = sin a * cosh b + cos a * sinh b * I`. Total. -/
def sin (z : FastComplex) : FastComplex :=
  let eb := FastReal.exp z.im
  let enb := FastReal.exp (FastReal.neg z.im)
  let half : FastReal := FastReal.ofDyadic ⟨1, -1⟩
  let ch := (eb + enb) * half
  let sh := (eb - enb) * half
  ⟨FastReal.sin z.re * ch, FastReal.cos z.re * sh⟩

/--
Principal square root. Total in the enclosure sense:

`sqrt z = (√((|z|+re)/2), sign(im) * √((|z|-re)/2))`.

When the sign of `im` cannot be certified at the requested precision, the
imaginary component falls back to the valid enclosure `[-s, s]` (which does
not shrink on the branch cut `re < 0, im = 0` unless `im` is an *exact*
zero ball, in which case the principal branch `+s` is returned).
-/
def sqrt (z : FastComplex) : FastComplex :=
  let m := abs z
  let half : FastReal := FastReal.ofDyadic ⟨1, -1⟩
  let rePart := FastReal.sqrt ((m + z.re) * half)
  let s := FastReal.sqrt ((m - z.re) * half)
  { re := rePart
    im := fun n =>
      let prec := -((n : Int) + 2)
      let bi := z.im (n + 4)
      let bs := s n
      if bi.mid.man == 0 && bi.rad.man == 0 then
        -- `im` is exactly 0: z is real, principal sqrt has im = +√((|z|-re)/2).
        bs
      else if bi.lo.man > 0 then bs
      else if bi.hi.man < 0 then Ball.neg bs
      else
        let u := bs.absUpper
        Ball.ofInterval (Dyadic.neg u) u prec }

/-!
### Partial operations

Reciprocal and division need the denominator **apart from `0`**; argument and
logarithm are discontinuous on the closed negative real axis. As in
`CRealsFast.lean`, these are partial approximators: at each requested
precision `n` they either return a certified ball (pair) or `none`.
-/

/-- Reciprocal `z⁻¹ = conj z / |z|²`; `none` if apartness from `0` cannot be certified. -/
def inv? (z : FastComplex) : ℕ → Option (Ball × Ball) := fun n => do
  let ns := normSq z
  let r ← FastReal.div? z.re ns n
  let i ← FastReal.div? (FastReal.neg z.im) ns n
  pure (r, i)

/-- Division `z / w = z * conj w / |w|²`; `none` if `w`'s apartness from `0` cannot be certified. -/
def div? (z w : FastComplex) : ℕ → Option (Ball × Ball) := fun n => do
  let num := mul z (conj w)
  let ns := normSq w
  let r ← FastReal.div? num.re ns n
  let i ← FastReal.div? num.im ns n
  pure (r, i)

/-- Principal argument in `(-π, π]`; `none` on (a neighbourhood of) the closed
negative real axis, where `arg` is discontinuous. -/
def arg? (z : FastComplex) : ℕ → Option Ball :=
  FastReal.atan2? z.im z.re

/-- Principal logarithm `log z = (ln |z|, arg z)`; partial for the same reason as `arg?`. -/
def log? (z : FastComplex) : ℕ → Option (Ball × Ball) := fun n => do
  let m ← FastReal.log? (abs z) n
  let a ← arg? z n
  pure (m, a)

/-!
### Comparison and rendering
-/

/-- Semi-decidable equality test (componentwise fueled comparison). -/
def eq? (z w : FastComplex) (fuel : Nat := 100) : Option Bool := do
  let r ← FastReal.compare z.re w.re fuel
  let i ← FastReal.compare z.im w.im fuel
  pure (r == Ordering.eq && i == Ordering.eq)

/-- Exact decimal rendering of both components (see `FastReal.toDecimal`). -/
def toDecimal (z : FastComplex) (digits : Nat := 10) : String :=
  s!"{FastReal.toDecimal z.re digits} + {FastReal.toDecimal z.im digits}*I"

instance : Repr FastComplex where
  reprPrec z _ :=
    let br := z.re 20
    let bi := z.im 20
    s!"[{br.mid.toFloat} ± {br.rad.toFloat}] + [{bi.mid.toFloat} ± {bi.rad.toFloat}]*I"

end FastComplex

end Computable.Fast
