/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.ExpSound
import ComputableReals.Computable.FastComplexSound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Soundness of executable sine and cosine — verified phase gates

The photonics primitive: `phase θ = cos θ + i·sin θ = e^{iθ}`. This file
supplies verified `cosV`/`sinV` (and the complex `phaseV`) with
*unconditional* enclosure of `Real.cos`/`Real.sin`.

`Ball.sin`/`cos` run a variable-order Taylor loop, which Mathlib's
*fixed-order* `Real.sin_bound`/`cos_bound` (`|sin x − (x − x³/6)| ≤
|x|⁴·5/96`) do not directly certify. So — as with `expV` — this file
builds a verified **twin** (originals untouched):

* scale the argument by `2^{−k}` to `|x_small| ≤ ½` (reusing
  `ExpSound.abs_scaled_le_half`);
* `sinCosBaseV` — the order-4 polynomials `x − x³/6` and `1 − x²/2`,
  each ball widened by the `sin_bound`/`cos_bound` remainder radius
  (`|x|⁴·5/96 < |x|⁴·2^{−4}`);
* `dblV` — unwind the scaling with the double-angle identities
  `sin 2t = 2 sin t cos t`, `cos 2t = cos²t − sin²t`.

Soundness needs only `|x_small| ≤ 1`, so no precision/fuel certificate is
required. `phaseV_sound` then gives the verified `e^{iθ}` phase gate for
`FastComplex`.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.ExpSound

set_option maxHeartbeats 1000000

namespace Computable.Fast

namespace Ball

/-- Subtraction of balls (`Ball` provides only `add`/`neg`). -/
def bsub (x y : Ball) (prec : ℤ) : Ball := Ball.add x (Ball.neg y) prec

theorem bsub_encloses {x y : Ball} {a b : ℝ} (prec : ℤ)
    (hx : x.Encloses a) (hy : y.Encloses b) : (Ball.bsub x y prec).Encloses (a - b) := by
  have h := Ball.add_encloses prec hx (Ball.neg_encloses hy)
  rwa [show a + -b = a - b from by ring] at h

/-- Reciprocal of a positive dyadic constant, as a sound ball. -/
def recipD (d : Dyadic) (prec : ℤ) : Ball := (Ball.invDyadic? d prec).getD Ball.zero

theorem recipD_encloses {d : Dyadic} (hd : d.man ≠ 0) (prec : ℤ) :
    (recipD d prec).Encloses (((d.toRat : ℚ) : ℝ))⁻¹ :=
  invDyadicGetD_sound hd prec

theorem ofDyadic_encloses (d : Dyadic) :
    (Ball.ofDyadic d).Encloses ((d.toRat : ℚ) : ℝ) :=
  FastReal.encloses_ofDyadic d 0

/-- Widen a ball's radius by a nonnegative dyadic, preserving enclosure of
any point within the extra slack. -/
private lemma widen_encloses {b : Ball} {v t : ℝ} {e : Dyadic} (prec : ℤ)
    (hb : b.Encloses v) (hslack : |t - v| ≤ ((e.toRat : ℚ) : ℝ)) :
    (⟨b.mid, (b.rad + e).roundUp prec⟩ : Ball).Encloses t := by
  rw [encloses_iff_abs]
  have hbv : |v - (b.mid.toRat : ℝ)| ≤ (b.rad.toRat : ℝ) := encloses_iff_abs.mp hb
  have he0 : (0 : ℝ) ≤ ((e.toRat : ℚ) : ℝ) := le_trans (abs_nonneg _) hslack
  have hup := Dyadic.le_toRat_roundUp (b.rad + e) prec
  calc |t - (b.mid.toRat : ℝ)|
      ≤ |t - v| + |v - (b.mid.toRat : ℝ)| := abs_sub_le _ _ _
    _ ≤ ((e.toRat : ℚ) : ℝ) + (b.rad.toRat : ℝ) := add_le_add hslack hbv
    _ = (((b.rad + e).toRat : ℚ) : ℝ) := by rw [Dyadic.toRat_add]; push_cast; ring
    _ ≤ (((b.rad + e).roundUp prec).toRat : ℝ) := by exact_mod_cast hup

end Ball

namespace TrigSound

/-! ## The order-4 base -/

/-- Verified order-4 base: for `x` enclosing `s` with `|s| ≤ 1`, returns
`(S, C)` enclosing `(Real.sin s, Real.cos s)`. -/
def sinCosBaseV (x : Ball) (prec : ℤ) : Ball × Ball :=
  let x2 := Ball.mul x x prec
  let x3 := Ball.mul x2 x prec
  let sinP := Ball.bsub x (Ball.mul x3 (Ball.recipD ⟨6, 0⟩ prec) prec) prec
  let cosP := Ball.bsub Ball.one (Ball.mul x2 (Ball.recipD ⟨2, 0⟩ prec) prec) prec
  let u := x.absUpper
  let rem := u * u * (u * u) * ⟨1, -4⟩
  (⟨sinP.mid, (sinP.rad + rem).roundUp prec⟩, ⟨cosP.mid, (cosP.rad + rem).roundUp prec⟩)

/-- The remainder radius `|s|⁴·5/96 ≤ (absUpper)⁴·(1/16)`. -/
private lemma rem_bound {x : Ball} {s : ℝ} (hx : x.Encloses s) :
    |s| ^ 4 * (5 / 96) ≤ (((x.absUpper * x.absUpper * (x.absUpper * x.absUpper)
      * ⟨1, -4⟩).toRat : ℚ) : ℝ) := by
  have hu : |s| ≤ ((x.absUpper.toRat : ℚ) : ℝ) := Ball.absUpper_sound hx
  have hs4 : |s| ^ 4 ≤ ((x.absUpper.toRat : ℚ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hu 4
  have hval : (((x.absUpper * x.absUpper * (x.absUpper * x.absUpper) * ⟨1, -4⟩).toRat : ℚ) : ℝ)
      = ((x.absUpper.toRat : ℚ) : ℝ) ^ 4 * (1 / 16) := by
    simp only [Dyadic.toRat_mul]
    rw [show (Dyadic.toRat ⟨1, -4⟩ : ℚ) = 1 / 16 from by norm_num [Dyadic.toRat]]
    push_cast
    ring
  rw [hval]
  calc |s| ^ 4 * (5 / 96)
      ≤ ((x.absUpper.toRat : ℚ) : ℝ) ^ 4 * (5 / 96) :=
        mul_le_mul_of_nonneg_right hs4 (by norm_num)
    _ ≤ ((x.absUpper.toRat : ℚ) : ℝ) ^ 4 * (1 / 16) :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

theorem sinCosBaseV_sound {x : Ball} {s : ℝ} (hx : x.Encloses s) (hs : |s| ≤ 1)
    (prec : ℤ) :
    (sinCosBaseV x prec).1.Encloses (Real.sin s)
    ∧ (sinCosBaseV x prec).2.Encloses (Real.cos s) := by
  have hx2 : (Ball.mul x x prec).Encloses (s * s) := Ball.mul_encloses prec hx hx
  have hx3 : (Ball.mul (Ball.mul x x prec) x prec).Encloses (s * s * s) :=
    Ball.mul_encloses prec hx2 hx
  have h6 : (Ball.recipD ⟨6, 0⟩ prec).Encloses ((6 : ℝ))⁻¹ := by
    have := Ball.recipD_encloses (d := ⟨6, 0⟩) (by decide) prec
    rwa [show ((Dyadic.toRat ⟨6, 0⟩ : ℚ) : ℝ) = 6 from by norm_num [Dyadic.toRat]] at this
  have h2 : (Ball.recipD ⟨2, 0⟩ prec).Encloses ((2 : ℝ))⁻¹ := by
    have := Ball.recipD_encloses (d := ⟨2, 0⟩) (by decide) prec
    rwa [show ((Dyadic.toRat ⟨2, 0⟩ : ℚ) : ℝ) = 2 from by norm_num [Dyadic.toRat]] at this
  have hsinP : (Ball.bsub x (Ball.mul (Ball.mul (Ball.mul x x prec) x prec)
      (Ball.recipD ⟨6, 0⟩ prec) prec) prec).Encloses (s - s ^ 3 / 6) := by
    have h := Ball.bsub_encloses prec hx (Ball.mul_encloses prec hx3 h6)
    rwa [show s * s * s * (6 : ℝ)⁻¹ = s ^ 3 / 6 from by ring] at h
  have hcosP : (Ball.bsub Ball.one (Ball.mul (Ball.mul x x prec)
      (Ball.recipD ⟨2, 0⟩ prec) prec) prec).Encloses (1 - s ^ 2 / 2) := by
    have h := Ball.bsub_encloses prec Ball.one_encloses (Ball.mul_encloses prec hx2 h2)
    rwa [show s * s * (2 : ℝ)⁻¹ = s ^ 2 / 2 from by ring] at h
  refine ⟨?_, ?_⟩
  · exact Ball.widen_encloses prec hsinP
      (le_trans (Real.sin_bound hs) (rem_bound hx))
  · exact Ball.widen_encloses prec hcosP
      (le_trans (Real.cos_bound hs) (rem_bound hx))

/-! ## Double-angle unwinding -/

/-- One double-angle step: `(s, c) ↦ (2sc, c² − s²)`. -/
def dblStep (s c : Ball) (prec : ℤ) : Ball × Ball :=
  (Ball.mul (Ball.ofDyadic ⟨2, 0⟩) (Ball.mul s c prec) prec,
    Ball.add (Ball.mul c c prec) (Ball.neg (Ball.mul s s prec)) prec)

/-- `dblStep` preserves the sin/cos enclosure across `t ↦ 2t`. -/
theorem dblStep_sound {s c : Ball} {t : ℝ} (prec : ℤ)
    (hs : s.Encloses (Real.sin t)) (hc : c.Encloses (Real.cos t)) :
    (dblStep s c prec).1.Encloses (Real.sin (2 * t))
    ∧ (dblStep s c prec).2.Encloses (Real.cos (2 * t)) := by
  refine ⟨?_, ?_⟩
  · rw [Real.sin_two_mul]
    have h2 : (Ball.ofDyadic ⟨2, 0⟩).Encloses (2 : ℝ) := by
      have := Ball.ofDyadic_encloses (⟨2, 0⟩ : Dyadic)
      rwa [show ((Dyadic.toRat ⟨2, 0⟩ : ℚ) : ℝ) = 2 from by norm_num [Dyadic.toRat]] at this
    have h := Ball.mul_encloses prec h2 (Ball.mul_encloses prec hs hc)
    rwa [show (2 : ℝ) * (Real.sin t * Real.cos t) = 2 * Real.sin t * Real.cos t from by ring] at h
  · rw [Real.cos_two_mul']
    have h := Ball.add_encloses prec (Ball.mul_encloses prec hc hc)
      (Ball.neg_encloses (Ball.mul_encloses prec hs hs))
    rwa [show Real.cos t * Real.cos t + -(Real.sin t * Real.sin t)
      = Real.cos t ^ 2 - Real.sin t ^ 2 from by ring] at h

/-- Iterated doubling: after `n` steps, `(s, c)` encloses
`(sin (2^n · t), cos (2^n · t))`. -/
def dblV (s c : Ball) (prec : ℤ) : ℕ → Ball × Ball
  | 0 => (s, c)
  | n + 1 => dblV (dblStep s c prec).1 (dblStep s c prec).2 prec n

theorem dblV_sound (prec : ℤ) :
    ∀ (n : ℕ) (s c : Ball) (t : ℝ),
      s.Encloses (Real.sin t) → c.Encloses (Real.cos t) →
      (dblV s c prec n).1.Encloses (Real.sin (2 ^ n * t))
      ∧ (dblV s c prec n).2.Encloses (Real.cos (2 ^ n * t)) := by
  intro n
  induction n with
  | zero =>
    intro s c t hs hc
    simpa using ⟨hs, hc⟩
  | succ n ih =>
    intro s c t hs hc
    obtain ⟨hs', hc'⟩ := dblStep_sound prec hs hc
    have hrec := ih (dblStep s c prec).1 (dblStep s c prec).2 (2 * t) hs' hc'
    have hpow : (2 : ℝ) ^ n * (2 * t) = 2 ^ (n + 1) * t := by rw [pow_succ]; ring
    rw [hpow] at hrec
    rw [dblV]
    exact hrec

/-! ## Assembly

The scaling exponent `K` is a *parameter* ≥ `expK x`: any such `K` keeps
`|x_small| ≤ ½ ≤ 1` (soundness), while a larger `K` shrinks the order-4
base error `|x_small|⁴·5/96` — so `cosV`/`sinV` scale `K` with the
requested precision to actually converge. -/

/-- Verified `(sin, cos)` scaling by `2^{−K}` and unwinding `K` doublings. -/
def sinCosVWith (x : Ball) (K : ℕ) (prec : ℤ) : Ball × Ball :=
  let x_small := x.scale2 (-(K : ℤ))
  let (s0, c0) := sinCosBaseV x_small prec
  dblV s0 c0 prec K

theorem sinCosVWith_sound {x : Ball} {r : ℝ} (hx : x.Encloses r) {K : ℕ}
    (hK : expK x ≤ (K : ℤ)) (prec : ℤ) :
    (sinCosVWith x K prec).1.Encloses (Real.sin r)
    ∧ (sinCosVWith x K prec).2.Encloses (Real.cos r) := by
  have hxs : (x.scale2 (-(K : ℤ))).Encloses (r * (2 : ℝ) ^ (-(K : ℤ))) :=
    Ball.scale2_encloses hx _
  -- `|r·2^{−K}| ≤ |r·2^{−expK}| ≤ ½ ≤ 1`
  have hs : |r * (2 : ℝ) ^ (-(K : ℤ))| ≤ 1 := by
    have hhalf : |r| * (2 : ℝ) ^ (-(expK x)) ≤ 1 / 2 := by
      have h := abs_scaled_le_half hx
      rwa [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) (-(expK x)))] at h
    have hmono : (2 : ℝ) ^ (-(K : ℤ)) ≤ (2 : ℝ) ^ (-(expK x)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have : |r| * (2 : ℝ) ^ (-(K : ℤ)) ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hmono (abs_nonneg r)) hhalf
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) (-(K:ℤ)))]
    linarith
  set sm : ℝ := r * (2 : ℝ) ^ (-(K : ℤ)) with hsm
  obtain ⟨hs0, hc0⟩ := sinCosBaseV_sound hxs hs prec
  have hd := dblV_sound prec K (sinCosBaseV (x.scale2 (-(K : ℤ))) prec).1
    (sinCosBaseV (x.scale2 (-(K : ℤ))) prec).2 sm hs0 hc0
  have hpow : (2 : ℝ) ^ K * sm = r := by
    rw [hsm, show ((2 : ℝ) ^ K) = (2 : ℝ) ^ ((K : ℤ)) from (zpow_natCast (2 : ℝ) _).symm,
      show (2 : ℝ) ^ ((K : ℤ)) * (r * 2 ^ (-(K : ℤ)))
        = r * (2 ^ ((K : ℤ)) * 2 ^ (-(K : ℤ))) from by ring,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [hpow] at hd
  exact hd

/-- Precision-adaptive scaling: `expK x` (to reach `|·| ≤ ½`) plus a pad
`⌈−prec/4⌉` so the order-4 base error `~2^{−4K}` clears `2^{prec}`. -/
def sinCosKForPrec (x : Ball) (prec : ℤ) : ℕ :=
  (expK x).toNat + (-prec).toNat / 4 + 3

theorem expK_le_KForPrec (x : Ball) (prec : ℤ) : expK x ≤ (sinCosKForPrec x prec : ℤ) := by
  have := expK_nonneg x
  unfold sinCosKForPrec
  omega

/-! ## `FastReal` and `FastComplex` -/

end TrigSound

namespace FastReal

open TrigSound

/-- Verified cosine (precision-adaptive scaling). -/
def cosV (x : FastReal) : FastReal := fun n =>
  let b := x (n + 10)
  (sinCosVWith b (sinCosKForPrec b (-((n : ℤ) + 2))) (-((n : ℤ) + 2))).2

/-- Verified sine (precision-adaptive scaling). -/
def sinV (x : FastReal) : FastReal := fun n =>
  let b := x (n + 10)
  (sinCosVWith b (sinCosKForPrec b (-((n : ℤ) + 2))) (-((n : ℤ) + 2))).1

theorem cosV_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) :
    (FastReal.cosV x).Encloses (Real.cos r) :=
  fun n => (TrigSound.sinCosVWith_sound (hx (n + 10))
    (TrigSound.expK_le_KForPrec _ _) _).2

theorem sinV_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) :
    (FastReal.sinV x).Encloses (Real.sin r) :=
  fun n => (TrigSound.sinCosVWith_sound (hx (n + 10))
    (TrigSound.expK_le_KForPrec _ _) _).1

end FastReal

namespace FastComplex

open Computable.Fast.FastComplex

/-- Verified phase gate `e^{iθ} = cos θ + i·sin θ`. -/
def phaseV (θ : FastReal) : Computable.Fast.FastComplex :=
  { re := FastReal.cosV θ, im := FastReal.sinV θ }

/-- **The verified phase gate encloses `Complex.exp (θ·I)`.** The photonics
phase-shift primitive, proven correct against Mathlib's complex
exponential. -/
theorem phaseV_sound {θ : FastReal} {r : ℝ} (hθ : θ.Encloses r) :
    (phaseV θ).Encloses (Complex.exp ((r : ℂ) * Complex.I)) := by
  refine ⟨?_, ?_⟩
  · show (FastReal.cosV θ).Encloses (Complex.exp ((r : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re]
    exact FastReal.cosV_sound hθ
  · show (FastReal.sinV θ).Encloses (Complex.exp ((r : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im]
    exact FastReal.sinV_sound hθ

/-! ## Demos -/

-- `cos 1 ≈ 0.540302`, `sin 1 ≈ 0.841471`.
#eval FastReal.cosV 1
#eval FastReal.sinV 1

-- The phase gate `e^{i·1} = cos 1 + i sin 1`.
#eval FastComplex.phaseV 1

-- Each output is a *sound* enclosure of the true value (the theorems above
-- prove the interval contains it): `cos 1 = 0.5403023…`, `sin 1 =
-- 0.8414710…` both lie in the balls printed. Note the enclosures are sound
-- but not exact — the double-angle unwinding accumulates radius even on
-- exact inputs — so an `eqF` equality test on trig output returns `none`;
-- exact identities like `cos²+sin² = 1` are theorems, not decisions.

end FastComplex

end Computable.Fast
