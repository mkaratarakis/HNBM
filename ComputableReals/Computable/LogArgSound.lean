/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.SqrtComplexSound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Verified logarithm and argument

`log` and `arg` were the last unverified functions in the stack, and both
were blocked at the *real* layer: `FastReal.log?` and `FastReal.atan` run
but carry no soundness theorems, and re-deriving them as Taylor series with
error bounds would repeat the whole of `ExpSound`.

This file takes a cheaper and more robust route. Both functions are
*inverses* of functions that are already verified — `log` inverts `expV`,
`arctan` inverts `tan = sinV / cosV` — and an inverse can be certified
without ever analysing a series:

> to prove `L ≤ log r ≤ H` it suffices to check `exp L ≤ r ≤ exp H`,
> because `exp` is monotone.

So the *search* for a bracket need not be verified at all — only the final
check. `logBracket` and `argBracket` are those checks; the searches that
propose brackets are ordinary unverified code, and correctness comes from
the certificate alone. This is the same discipline as `unitaryUpTo`: an
executable predicate whose `true` answer is a theorem.

## Contents

* `logBracket` / `logBracket_sound` — a certified enclosure of `Real.log`;
* `logV?` — search-then-certify, sound whenever it answers;
* `arctanBracket` / `arctanBracket_sound` — certified enclosure of
  `Real.arctan`, via `sin lo ≤ y · cos lo` so that no division is needed;
* `argBracket` / `argBracket_sound` — certified enclosure of `Complex.arg`
  on the right half-plane, where `arg z = arctan (im z / re z)`;
* `logCBracket_sound` — the complex logarithm, assembled from the two,
  using `Complex.log_re` and `Complex.log_im`.
-/

open Computable.Fast Computable.Fast.API Real

namespace Computable.Fast

/-! ## The real logarithm, by inverting `expV` -/

namespace FastReal

/-- `expV` of a dyadic encloses `exp` of that dyadic. -/
theorem expV_ofDyadic_encloses (d : Dyadic) :
    (FastReal.expV (FastReal.ofDyadic d)).Encloses (Real.exp ((d.toRat : ℚ) : ℝ)) :=
  FastReal.expV_sound (FastReal.encloses_ofDyadic (d := d))

/-- **Certified bracket for the logarithm.** `true` only when both
`exp lo ≤ x` and `x ≤ exp hi` have been decided. -/
def logBracket (x : FastReal) (lo hi : Dyadic) (fuel : ℕ := defaultFuel) : Bool :=
  (leF (FastReal.expV (FastReal.ofDyadic lo)) x fuel == some true) &&
  (leF x (FastReal.expV (FastReal.ofDyadic hi)) fuel == some true)

/-- **Soundness of the logarithm bracket.** -/
theorem logBracket_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) (hr : 0 < r)
    {lo hi : Dyadic} {fuel : ℕ} (h : logBracket x lo hi fuel = true) :
    ((lo.toRat : ℚ) : ℝ) ≤ Real.log r ∧ Real.log r ≤ ((hi.toRat : ℚ) : ℝ) := by
  unfold logBracket at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : leF (FastReal.expV (FastReal.ofDyadic lo)) x fuel = some true := by
    simpa using h1
  have h2' : leF x (FastReal.expV (FastReal.ofDyadic hi)) fuel = some true := by
    simpa using h2
  have hlo : Real.exp ((lo.toRat : ℚ) : ℝ) ≤ r :=
    API.leF_sound (expV_ofDyadic_encloses lo) hx h1'
  have hhi : r ≤ Real.exp ((hi.toRat : ℚ) : ℝ) :=
    API.leF_sound hx (expV_ofDyadic_encloses hi) h2'
  exact ⟨(Real.le_log_iff_exp_le hr).mpr hlo, (Real.log_le_iff_le_exp hr).mpr hhi⟩

/-- The certified logarithm: propose a bracket, then certify it. Returns
`none` when the certificate does not fire. -/
def logV? (x : FastReal) (lo hi : Dyadic) (prec : ℤ)
    (fuel : ℕ := defaultFuel) : Option Ball :=
  if logBracket x lo hi fuel then some (Ball.ofInterval lo hi prec) else none

/-- **Soundness of the certified logarithm.** -/
theorem logV?_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) (hr : 0 < r)
    {lo hi : Dyadic} {prec : ℤ} {fuel : ℕ} {b : Ball}
    (h : logV? x lo hi prec fuel = some b) : b.Encloses (Real.log r) := by
  unfold logV? at h
  by_cases hc : logBracket x lo hi fuel
  · rw [if_pos hc] at h
    obtain ⟨hl, hh⟩ := logBracket_sound hx hr hc
    have := Ball.ofInterval_encloses (lo := lo) (hi := hi) prec hl hh
    rwa [← Option.some.injEq _ _ |>.mp h]
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ## The real arctangent, by inverting `tan = sinV / cosV`

The bracket avoids division: for `cos lo > 0`, `tan lo ≤ y` is equivalent to
`sin lo ≤ y · cos lo`, which needs only multiplication.
-/

/-- **Certified bracket for `arctan`.** -/
def arctanBracket (y : FastReal) (lo hi : Dyadic) (fuel : ℕ := defaultFuel) : Bool :=
  let cl := FastReal.cosV (FastReal.ofDyadic lo)
  let ch := FastReal.cosV (FastReal.ofDyadic hi)
  (leF (FastReal.sinV (FastReal.ofDyadic lo)) (FastReal.mul y cl) fuel == some true) &&
  (leF (FastReal.mul y ch) (FastReal.sinV (FastReal.ofDyadic hi)) fuel == some true)

/-- **Soundness of the arctangent bracket.** The positivity of the two
cosines and the range conditions on `lo`, `hi` are hypotheses: they are
facts about the chosen dyadic endpoints, discharged by `norm_num` once
those are concrete. -/
theorem arctanBracket_sound {y : FastReal} {yR : ℝ} (hy : y.Encloses yR)
    {lo hi : Dyadic} {fuel : ℕ}
    (hcl : 0 < Real.cos ((lo.toRat : ℚ) : ℝ))
    (hch : 0 < Real.cos ((hi.toRat : ℚ) : ℝ))
    (hlo₁ : -(π / 2) < ((lo.toRat : ℚ) : ℝ)) (hlo₂ : ((lo.toRat : ℚ) : ℝ) < π / 2)
    (hhi₁ : -(π / 2) < ((hi.toRat : ℚ) : ℝ)) (hhi₂ : ((hi.toRat : ℚ) : ℝ) < π / 2)
    (h : arctanBracket y lo hi fuel = true) :
    ((lo.toRat : ℚ) : ℝ) ≤ Real.arctan yR ∧ Real.arctan yR ≤ ((hi.toRat : ℚ) : ℝ) := by
  unfold arctanBracket at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : leF (FastReal.sinV (FastReal.ofDyadic lo))
      (FastReal.mul y (FastReal.cosV (FastReal.ofDyadic lo))) fuel = some true := by
    simpa using h1
  have h2' : leF (FastReal.mul y (FastReal.cosV (FastReal.ofDyadic hi)))
      (FastReal.sinV (FastReal.ofDyadic hi)) fuel = some true := by
    simpa using h2
  have hsl := FastReal.sinV_sound (FastReal.encloses_ofDyadic (d := lo))
  have hcl' := FastReal.cosV_sound (FastReal.encloses_ofDyadic (d := lo))
  have hsh := FastReal.sinV_sound (FastReal.encloses_ofDyadic (d := hi))
  have hch' := FastReal.cosV_sound (FastReal.encloses_ofDyadic (d := hi))
  have hA : Real.sin ((lo.toRat : ℚ) : ℝ) ≤ yR * Real.cos ((lo.toRat : ℚ) : ℝ) :=
    API.leF_sound hsl (FastReal.mul_encloses hy hcl') h1'
  have hB : yR * Real.cos ((hi.toRat : ℚ) : ℝ) ≤ Real.sin ((hi.toRat : ℚ) : ℝ) :=
    API.leF_sound (FastReal.mul_encloses hy hch') hsh h2'
  -- turn the multiplicative bounds into `tan` bounds
  have htl : Real.tan ((lo.toRat : ℚ) : ℝ) ≤ yR := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcl]
    exact hA
  have hth : yR ≤ Real.tan ((hi.toRat : ℚ) : ℝ) := by
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hch]
    exact hB
  constructor
  · have := Real.arctan_le_arctan_iff.mpr htl
    rwa [Real.arctan_tan hlo₁ hlo₂] at this
  · have := Real.arctan_le_arctan_iff.mpr hth
    rwa [Real.arctan_tan hhi₁ hhi₂] at this

end FastReal

/-! ## The complex argument, on the right half-plane

For `re z > 0` the argument lies strictly inside `(-π/2, π/2)`, where it is
exactly `arctan (im z / re z)`. The bracket again avoids division, this time
by clearing both denominators at once: `tan lo ≤ im/re` is
`sin lo · re ≤ im · cos lo`.
-/

namespace FastComplex

/-- On the right half-plane the argument is an arctangent. -/
theorem arg_eq_arctan {c : ℂ} (hre : 0 < c.re) :
    Complex.arg c = Real.arctan (c.im / c.re) := by
  have habs : |Complex.arg c| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [abs_lt] at habs
  rw [← Complex.tan_arg c, Real.arctan_tan habs.1 habs.2]

/-- **Certified bracket for `Complex.arg` on the right half-plane.** -/
def argBracket (z : FastComplex) (lo hi : Dyadic) (fuel : ℕ := defaultFuel) : Bool :=
  let cl := FastReal.cosV (FastReal.ofDyadic lo)
  let ch := FastReal.cosV (FastReal.ofDyadic hi)
  let sl := FastReal.sinV (FastReal.ofDyadic lo)
  let sh := FastReal.sinV (FastReal.ofDyadic hi)
  (leF (FastReal.mul sl z.re) (FastReal.mul z.im cl) fuel == some true) &&
  (leF (FastReal.mul z.im ch) (FastReal.mul sh z.re) fuel == some true)

/-- **Soundness of the argument bracket.** -/
theorem argBracket_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c)
    (hre : 0 < c.re) {lo hi : Dyadic} {fuel : ℕ}
    (hcl : 0 < Real.cos ((lo.toRat : ℚ) : ℝ))
    (hch : 0 < Real.cos ((hi.toRat : ℚ) : ℝ))
    (hlo₁ : -(π / 2) < ((lo.toRat : ℚ) : ℝ)) (hlo₂ : ((lo.toRat : ℚ) : ℝ) < π / 2)
    (hhi₁ : -(π / 2) < ((hi.toRat : ℚ) : ℝ)) (hhi₂ : ((hi.toRat : ℚ) : ℝ) < π / 2)
    (h : argBracket z lo hi fuel = true) :
    ((lo.toRat : ℚ) : ℝ) ≤ Complex.arg c ∧ Complex.arg c ≤ ((hi.toRat : ℚ) : ℝ) := by
  unfold argBracket at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : leF (FastReal.mul (FastReal.sinV (FastReal.ofDyadic lo)) z.re)
      (FastReal.mul z.im (FastReal.cosV (FastReal.ofDyadic lo))) fuel = some true := by
    simpa using h1
  have h2' : leF (FastReal.mul z.im (FastReal.cosV (FastReal.ofDyadic hi)))
      (FastReal.mul (FastReal.sinV (FastReal.ofDyadic hi)) z.re) fuel = some true := by
    simpa using h2
  have hsl := FastReal.sinV_sound (FastReal.encloses_ofDyadic (d := lo))
  have hcl' := FastReal.cosV_sound (FastReal.encloses_ofDyadic (d := lo))
  have hsh := FastReal.sinV_sound (FastReal.encloses_ofDyadic (d := hi))
  have hch' := FastReal.cosV_sound (FastReal.encloses_ofDyadic (d := hi))
  have hA : Real.sin ((lo.toRat : ℚ) : ℝ) * c.re ≤ c.im * Real.cos ((lo.toRat : ℚ) : ℝ) :=
    API.leF_sound (FastReal.mul_encloses hsl hz.1) (FastReal.mul_encloses hz.2 hcl') h1'
  have hB : c.im * Real.cos ((hi.toRat : ℚ) : ℝ) ≤ Real.sin ((hi.toRat : ℚ) : ℝ) * c.re :=
    API.leF_sound (FastReal.mul_encloses hz.2 hch') (FastReal.mul_encloses hsh hz.1) h2'
  have htl : Real.tan ((lo.toRat : ℚ) : ℝ) ≤ c.im / c.re := by
    rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hcl hre]
    linarith [hA]
  have hth : c.im / c.re ≤ Real.tan ((hi.toRat : ℚ) : ℝ) := by
    rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hre hch]
    linarith [hB]
  rw [arg_eq_arctan hre]
  constructor
  · have := Real.arctan_le_arctan_iff.mpr htl
    rwa [Real.arctan_tan hlo₁ hlo₂] at this
  · have := Real.arctan_le_arctan_iff.mpr hth
    rwa [Real.arctan_tan hhi₁ hhi₂] at this

/-! ## The complex logarithm

`log z = log ‖z‖ + i · arg z` (`Complex.log_re`, `Complex.log_im`), so the
two brackets above combine componentwise.
-/

/-- **Certified enclosure of the complex logarithm** on the right
half-plane: the real part from the logarithm bracket applied to `‖z‖`, the
imaginary part from the argument bracket. -/
theorem logC_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c)
    (hre : 0 < c.re)
    {rlo rhi alo ahi : Dyadic} {prec : ℤ} {fuel : ℕ}
    (hcl : 0 < Real.cos ((alo.toRat : ℚ) : ℝ))
    (hch : 0 < Real.cos ((ahi.toRat : ℚ) : ℝ))
    (halo₁ : -(π / 2) < ((alo.toRat : ℚ) : ℝ)) (halo₂ : ((alo.toRat : ℚ) : ℝ) < π / 2)
    (hahi₁ : -(π / 2) < ((ahi.toRat : ℚ) : ℝ)) (hahi₂ : ((ahi.toRat : ℚ) : ℝ) < π / 2)
    (hlog : FastReal.logBracket z.abs rlo rhi fuel = true)
    (harg : argBracket z alo ahi fuel = true) :
    (Ball.ofInterval rlo rhi prec).Encloses (Complex.log c).re ∧
      (Ball.ofInterval alo ahi prec).Encloses (Complex.log c).im := by
  have hcne : c ≠ 0 := by
    intro hc; rw [hc] at hre; simp at hre
  have hnormpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  obtain ⟨hl, hh⟩ :=
    FastReal.logBracket_sound (abs_encloses hz) hnormpos hlog
  obtain ⟨hal, hah⟩ :=
    argBracket_sound hz hre hcl hch halo₁ halo₂ hahi₁ hahi₂ harg
  refine ⟨?_, ?_⟩
  · rw [Complex.log_re]
    exact Ball.ofInterval_encloses prec hl hh
  · rw [Complex.log_im]
    exact Ball.ofInterval_encloses prec hal hah

end FastComplex

/-! ## The certificates fire in practice

`log 2 ≈ 0.6931472` and `arg (1 + i) = π/4 ≈ 0.7853982`; the brackets below
are dyadics straddling those values at precision `2^-10`, and the checks
return `true`, so the corresponding soundness theorems apply to them.
-/

-- log 2 ∈ [709/1024, 711/1024] ≈ [0.69238, 0.69434]
#eval FastReal.logBracket (2 : FastReal) ⟨709, -10⟩ ⟨711, -10⟩

-- a deliberately wrong bracket is not certified
#eval FastReal.logBracket (2 : FastReal) ⟨1, -10⟩ ⟨2, -10⟩

-- arg (1 + i) ∈ [803/1024, 805/1024] ≈ [0.78418, 0.78613]
#eval FastComplex.argBracket ⟨1, 1⟩ ⟨803, -10⟩ ⟨805, -10⟩

-- arctan 1 = π/4, same bracket
#eval FastReal.arctanBracket (1 : FastReal) ⟨803, -10⟩ ⟨805, -10⟩

end Computable.Fast
