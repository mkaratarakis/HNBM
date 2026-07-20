/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.FastComplexTransSound

/-!
# The verified complex square root

The complex square root is the first genuinely *branch-dependent* function
in this development, and the branch cannot always be chosen computably: the
principal root of `a + bi` takes the sign of its imaginary part from the
sign of `b`, and deciding `b < 0` for a computable real is undecidable when
`b = 0`. So a total verified complex `sqrt` cannot exist, for the same
reason a decidable order cannot.

What *can* exist, and is what this file provides, is the fueled version.
`sqrtV?` asks the fuel-based `compare` for the sign of the imaginary part;
if the comparison is decided — which includes the exact-zero case, since
radius-`0` balls compare exactly — it returns the principal root, and
`sqrtV?_sound` proves that root correct. If the sign is undecided within
fuel it honestly returns `none`.

## What "correct" means here

The target is `principalSqrt`, the closed-form principal root

`√((‖c‖ + re c)/2) + i · sgn(im c) · √((‖c‖ − re c)/2)`,

together with `principalSqrt_sq`, which proves it really is a square root:
`principalSqrt c * principalSqrt c = c`. Stating soundness against this
closed form rather than against `c ^ (1/2 : ℂ)` keeps the development free
of `cpow`, whose half-angle unfolding would drag in `Complex.log` and hence
`arg` — neither of which is verified here (see the note at the end of the
README).
-/

open Computable.Fast

namespace Computable.Fast

namespace FastComplex

/-! ## The closed-form principal root -/

/-- The branch sign: `-1` below the real axis, `+1` on or above it. -/
noncomputable def sgnIm (c : ℂ) : ℝ := if c.im < 0 then -1 else 1

private theorem sgnIm_mul_self (c : ℂ) : sgnIm c * sgnIm c = 1 := by
  unfold sgnIm; split_ifs <;> norm_num

private theorem sgnIm_mul_abs (c : ℂ) : sgnIm c * |c.im| = c.im := by
  unfold sgnIm
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

private theorem half_add_nonneg (c : ℂ) : 0 ≤ (‖c‖ + c.re) / 2 := by
  have := neg_le_of_abs_le (Complex.abs_re_le_norm c); linarith

private theorem half_sub_nonneg (c : ℂ) : 0 ≤ (‖c‖ - c.re) / 2 := by
  have := le_of_abs_le (Complex.abs_re_le_norm c); linarith

/-- The principal square root of a complex number, in closed form. -/
noncomputable def principalSqrt (c : ℂ) : ℂ :=
  { re := Real.sqrt ((‖c‖ + c.re) / 2)
    im := sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2) }

/-- The product of the two radicands is `(im c / 2)²`. -/
private theorem radicand_mul (c : ℂ) :
    (‖c‖ + c.re) / 2 * ((‖c‖ - c.re) / 2) = (c.im / 2) * (c.im / 2) := by
  have hnorm : ‖c‖ * ‖c‖ = c.re * c.re + c.im * c.im := by
    rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  nlinarith [hnorm]

/-- **The principal square root really is a square root.** -/
theorem principalSqrt_sq (c : ℂ) : principalSqrt c * principalSqrt c = c := by
  have hA := half_add_nonneg c
  have hB := half_sub_nonneg c
  have hsA : Real.sqrt ((‖c‖ + c.re) / 2) * Real.sqrt ((‖c‖ + c.re) / 2)
      = (‖c‖ + c.re) / 2 := Real.mul_self_sqrt hA
  have hsB : Real.sqrt ((‖c‖ - c.re) / 2) * Real.sqrt ((‖c‖ - c.re) / 2)
      = (‖c‖ - c.re) / 2 := Real.mul_self_sqrt hB
  have hcross : Real.sqrt ((‖c‖ + c.re) / 2) * Real.sqrt ((‖c‖ - c.re) / 2)
      = |c.im| / 2 := by
    rw [← Real.sqrt_mul hA, radicand_mul]
    rw [Real.sqrt_mul_self_eq_abs]
    rw [abs_div]
    norm_num
  apply Complex.ext
  · show Real.sqrt ((‖c‖ + c.re) / 2) * Real.sqrt ((‖c‖ + c.re) / 2)
        - sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2)
          * (sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2)) = c.re
    have : sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2)
        * (sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2))
        = (sgnIm c * sgnIm c) * (Real.sqrt ((‖c‖ - c.re) / 2)
          * Real.sqrt ((‖c‖ - c.re) / 2)) := by ring
    rw [this, sgnIm_mul_self, hsA, hsB]
    ring
  · show Real.sqrt ((‖c‖ + c.re) / 2) * (sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2))
        + sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2) * Real.sqrt ((‖c‖ + c.re) / 2) = c.im
    have hexp : Real.sqrt ((‖c‖ + c.re) / 2) * (sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2))
        + sgnIm c * Real.sqrt ((‖c‖ - c.re) / 2) * Real.sqrt ((‖c‖ + c.re) / 2)
        = sgnIm c * (2 * (Real.sqrt ((‖c‖ + c.re) / 2)
            * Real.sqrt ((‖c‖ - c.re) / 2))) := by ring
    rw [hexp, hcross]
    have : sgnIm c * (2 * (|c.im| / 2)) = sgnIm c * |c.im| := by ring
    rw [this, sgnIm_mul_abs]

/-! ## The executable, fueled square root -/

/-- The executable principal square root. Returns `none` exactly when the
sign of the imaginary part could not be decided within `fuel`. -/
def sqrtV? (z : FastComplex) (fuel : ℕ := Computable.Fast.API.defaultFuel) :
    Option FastComplex :=
  match FastReal.compare z.im 0 fuel with
  | none => none
  | some o =>
    let m := z.abs
    let hf := FastReal.ofDyadic ⟨1, -1⟩
    let a := FastReal.sqrt (FastReal.mul (FastReal.add m z.re) hf)
    let b := FastReal.sqrt (FastReal.mul (FastReal.add m (FastReal.neg z.re)) hf)
    some { re := a, im := if o = Ordering.lt then FastReal.neg b else b }

private theorem half_encloses_aux :
    (FastReal.ofDyadic ⟨1, -1⟩ : FastReal).Encloses ((1 : ℝ) / 2) := by
  have h := FastReal.encloses_ofDyadic (d := (⟨1, -1⟩ : Dyadic))
  have hv : ((Dyadic.toRat ⟨1, -1⟩ : ℚ) : ℝ) = (1 : ℝ) / 2 := by
    norm_num [Dyadic.toRat]
  rwa [hv] at h

/-- **Soundness of the executable complex square root**: whenever it
answers, the answer encloses the principal square root. -/
theorem sqrtV?_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c)
    {fuel : ℕ} {w : FastComplex} (h : sqrtV? z fuel = some w) :
    w.Encloses (principalSqrt c) := by
  unfold sqrtV? at h
  have him : z.im.Encloses c.im := hz.2
  have hzero : (0 : FastReal).Encloses (0 : ℝ) := FastReal.encloses_zero
  have habs : (z.abs).Encloses ‖c‖ := abs_encloses hz
  -- the two radicands
  have hA : (FastReal.mul (FastReal.add z.abs z.re) (FastReal.ofDyadic ⟨1, -1⟩)).Encloses
      ((‖c‖ + c.re) / 2) := by
    have := FastReal.mul_encloses (FastReal.add_encloses habs hz.1) half_encloses_aux
    have hrw : (‖c‖ + c.re) * ((1 : ℝ) / 2) = (‖c‖ + c.re) / 2 := by ring
    rwa [hrw] at this
  have hB : (FastReal.mul (FastReal.add z.abs (FastReal.neg z.re))
      (FastReal.ofDyadic ⟨1, -1⟩)).Encloses ((‖c‖ - c.re) / 2) := by
    have hneg : (FastReal.neg z.re).Encloses (-c.re) := FastReal.neg_encloses hz.1
    have := FastReal.mul_encloses (FastReal.add_encloses habs hneg) half_encloses_aux
    have hrw : (‖c‖ + -c.re) * ((1 : ℝ) / 2) = (‖c‖ - c.re) / 2 := by ring
    rwa [hrw] at this
  have hsA := FastReal.sqrt_sound hA (half_add_nonneg c)
  have hsB := FastReal.sqrt_sound hB (half_sub_nonneg c)
  -- case on the decided sign
  cases ho : FastReal.compare z.im 0 fuel with
  | none => rw [ho] at h; exact absurd h (by simp)
  | some o =>
    rw [ho] at h
    simp only [Option.some.injEq] at h
    subst h
    cases o with
    | lt =>
      have hneg : c.im < 0 := by
        have := FastReal.compare_lt_sound him hzero ho
        simpa using this
      refine ⟨hsA, ?_⟩
      show (FastReal.neg _).Encloses (principalSqrt c).im
      have hs : (principalSqrt c).im = -Real.sqrt ((‖c‖ - c.re) / 2) := by
        show sgnIm c * _ = _
        rw [sgnIm, if_pos hneg]; ring
      rw [hs]
      exact FastReal.neg_encloses hsB
    | eq =>
      have hz0 : c.im = 0 := by
        have := FastReal.compare_eq_sound him hzero ho
        simpa using this
      refine ⟨hsA, ?_⟩
      rw [if_neg (by simp : ¬((Ordering.eq : Ordering) = Ordering.lt))]
      have hs : (principalSqrt c).im = Real.sqrt ((‖c‖ - c.re) / 2) := by
        show sgnIm c * _ = _
        rw [sgnIm, if_neg (by rw [hz0]; norm_num)]; ring
      rw [hs]; exact hsB
    | gt =>
      have hpos : 0 < c.im := by
        have := FastReal.compare_gt_sound him hzero ho
        simpa using this
      refine ⟨hsA, ?_⟩
      rw [if_neg (by simp : ¬((Ordering.gt : Ordering) = Ordering.lt))]
      have hs : (principalSqrt c).im = Real.sqrt ((‖c‖ - c.re) / 2) := by
        show sgnIm c * _ = _
        rw [sgnIm, if_neg (not_lt.mpr (le_of_lt hpos))]; ring
      rw [hs]; exact hsB

/-- **The computed root squares back to the input.** Combining soundness
with `principalSqrt_sq`: what the engine returns encloses a genuine square
root of the enclosed value. -/
theorem sqrtV?_sq {z : FastComplex} {c : ℂ} (hz : z.Encloses c)
    {fuel : ℕ} {w : FastComplex} (h : sqrtV? z fuel = some w) :
    ∃ u : ℂ, w.Encloses u ∧ u * u = c :=
  ⟨principalSqrt c, sqrtV?_sound hz h, principalSqrt_sq c⟩

end FastComplex

end Computable.Fast
