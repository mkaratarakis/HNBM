/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.FastMatrixSound
import ComputableReals.Computable.FastComplexTransSound

/-!
# Certified optical components

`unitaryUpTo_sound` turns an executable certificate into rigorous unitarity,
but only for a matrix whose `Encloses` hypothesis has been discharged — and
until now nothing discharged it for an actual component. The `#eval`s said
"the certificate fired"; they did not say "this beam splitter is unitary".

This file closes that gap for the two primitives of linear optics, and does
better than the tolerance certificate: because the enclosed Mathlib matrices
are *exactly* unitary, the conclusions need no tolerance at all.

* `beamSplitterV` — the balanced 50:50 splitter, built on the verified
  `FastReal.sqrt`; it encloses `bsM`, and `bsM` is exactly unitary.
* `phaseShifterV` — the phase shifter `diag (1, e^{iφ})`, built on the
  verified `phaseV`; it encloses `psM φ`, and `psM φ` is exactly unitary.
* `mzV` — a Mach–Zehnder-style composite `BS · P(φ) · BS`, enclosing a
  product of unitaries and therefore unitary.

Each is an executable object you can `#eval`, paired with a theorem about
the complex matrix it denotes.
-/

open Computable.Fast Matrix

namespace Computable.Fast

namespace FastMatrix

/-! ## The balanced beam splitter -/

/-- `1/√2`, as the verified `√(1/2)`. -/
def invSqrt2V : FastReal := FastReal.sqrt (FastReal.ofDyadic ⟨1, -1⟩)

/-- `invSqrt2V` encloses `√(1/2)`. -/
theorem invSqrt2V_encloses : invSqrt2V.Encloses (Real.sqrt (1 / 2)) := by
  have hd : (FastReal.ofDyadic ⟨1, -1⟩ : FastReal).Encloses ((1 : ℝ) / 2) := by
    have h := FastReal.encloses_ofDyadic (d := (⟨1, -1⟩ : Dyadic))
    have hv : ((Dyadic.toRat ⟨1, -1⟩ : ℚ) : ℝ) = (1 : ℝ) / 2 := by
      norm_num [Dyadic.toRat]
    rwa [hv] at h
  exact FastReal.sqrt_sound hd (by norm_num)

/-- The executable balanced beam splitter `(1/√2)·[[1, 1], [1, −1]]`. -/
def beamSplitterV : FastMatrix 2 2 := fun i j =>
  if i = 1 ∧ j = 1 then ⟨FastReal.neg invSqrt2V, 0⟩ else ⟨invSqrt2V, 0⟩

/-- The ideal balanced beam splitter as a Mathlib complex matrix. -/
noncomputable def bsM : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 1 ∧ j = 1 then -(Real.sqrt (1 / 2) : ℂ) else (Real.sqrt (1 / 2) : ℂ)

/-- **The executable beam splitter encloses the ideal one.** -/
theorem beamSplitterV_encloses : beamSplitterV.Encloses bsM := by
  intro i j
  by_cases h : i = 1 ∧ j = 1
  · have hb : beamSplitterV i j = ⟨FastReal.neg invSqrt2V, 0⟩ := if_pos h
    have hm : bsM i j = -((Real.sqrt (1 / 2) : ℝ) : ℂ) := if_pos h
    rw [hb, hm]
    refine ⟨?_, ?_⟩
    · show (FastReal.neg invSqrt2V).Encloses _
      rw [Complex.neg_re, Complex.ofReal_re]
      exact FastReal.neg_encloses invSqrt2V_encloses
    · show (0 : FastReal).Encloses _
      rw [Complex.neg_im, Complex.ofReal_im, neg_zero]
      exact FastReal.encloses_zero
  · have hb : beamSplitterV i j = ⟨invSqrt2V, 0⟩ := if_neg h
    have hm : bsM i j = ((Real.sqrt (1 / 2) : ℝ) : ℂ) := if_neg h
    rw [hb, hm]
    refine ⟨?_, ?_⟩
    · show invSqrt2V.Encloses _
      rw [Complex.ofReal_re]; exact invSqrt2V_encloses
    · show (0 : FastReal).Encloses _
      rw [Complex.ofReal_im]; exact FastReal.encloses_zero

/-- `(√(1/2))² = 1/2`, as a complex identity. -/
private theorem sq_invSqrt2 : ((Real.sqrt (1 / 2) : ℂ)) * (Real.sqrt (1 / 2) : ℂ)
    = (1 / 2 : ℂ) := by
  have h : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 :=
    Real.mul_self_sqrt (by norm_num)
  have := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at this
  simpa using this

/-- `(√2 : ℂ)⁻¹ · (√2 : ℂ)⁻¹ = 1/2`. -/
private theorem inv_sqrt2_sq :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have hr : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
    push_cast at hc
    simpa using hc
  rw [h]
  norm_num

/-- A product of unitaries is unitary. -/
private theorem mul_unitary {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) : (A * B) * (A * B)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc A B, hB,
    Matrix.mul_one, hA]

/-- **The ideal beam splitter is exactly unitary.** -/
theorem bsM_unitary : bsM * bsMᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bsM, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    rw [inv_sqrt2_sq] <;> norm_num

/-! ## The phase shifter -/

/-- The executable phase shifter `diag (1, e^{iφ})`, on the verified phase. -/
def phaseShifterV (φ : FastReal) : FastMatrix 2 2 := fun i j =>
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 1 then FastComplex.phaseV φ
  else 0

/-- The ideal phase shifter as a Mathlib complex matrix. -/
noncomputable def psM (φR : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 1 then Complex.exp ((φR : ℂ) * Complex.I)
  else 0

/-- **The executable phase shifter encloses the ideal one.** -/
theorem phaseShifterV_encloses {φ : FastReal} {φR : ℝ} (hφ : φ.Encloses φR) :
    (phaseShifterV φ).Encloses (psM φR) := by
  intro i j
  by_cases h0 : i = 0 ∧ j = 0
  · have hb : phaseShifterV φ i j = 1 := if_pos h0
    have hm : psM φR i j = 1 := if_pos h0
    rw [hb, hm]; exact FastComplex.encloses_one
  · by_cases h1 : i = 1 ∧ j = 1
    · have hb : phaseShifterV φ i j = FastComplex.phaseV φ := by
        show (if _ then _ else if _ then _ else _) = _
        rw [if_neg h0, if_pos h1]
      have hm : psM φR i j = Complex.exp ((φR : ℂ) * Complex.I) := by
        show (if _ then _ else if _ then _ else _) = _
        rw [if_neg h0, if_pos h1]
      rw [hb, hm]; exact FastComplex.phaseV_sound hφ
    · have hb : phaseShifterV φ i j = 0 := by
        show (if _ then _ else if _ then _ else _) = _
        rw [if_neg h0, if_neg h1]
      have hm : psM φR i j = 0 := by
        show (if _ then _ else if _ then _ else _) = _
        rw [if_neg h0, if_neg h1]
      rw [hb, hm]; exact FastComplex.encloses_zero

/-- **The ideal phase shifter is exactly unitary.** -/
theorem psM_unitary (φR : ℝ) : psM φR * (psM φR)ᴴ = 1 := by
  have habs : Complex.exp ((φR : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp ((φR : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hz : (φR : ℂ) * Complex.I + (starRingEnd ℂ) ((φR : ℂ) * Complex.I) = 0 := by
      simp [Complex.conj_I]
    rw [hz, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [psM, Matrix.mul_apply, Matrix.conjTranspose_apply, habs]

/-! ## A Mach–Zehnder-style composite

Composition is where the enclosure lemmas earn their keep: `mul_encloses`
carries the certificate through, so the composite is certified without any
new numerical reasoning.
-/

/-- Executable `BS · P(φ) · BS`. -/
def mzV (φ : FastReal) : FastMatrix 2 2 :=
  beamSplitterV * (phaseShifterV φ * beamSplitterV)

/-- Its ideal counterpart. -/
noncomputable def mzM (φR : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  bsM * (psM φR * bsM)

/-- **The executable interferometer encloses the ideal one.** -/
theorem mzV_encloses {φ : FastReal} {φR : ℝ} (hφ : φ.Encloses φR) :
    (mzV φ).Encloses (mzM φR) :=
  mul_encloses beamSplitterV_encloses
    (mul_encloses (phaseShifterV_encloses hφ) beamSplitterV_encloses)

/-- **The ideal interferometer is exactly unitary** — a product of
unitaries, with no tolerance and no numerical certificate involved. -/
theorem mzM_unitary (φR : ℝ) : mzM φR * (mzM φR)ᴴ = 1 :=
  mul_unitary bsM_unitary (mul_unitary (psM_unitary φR) bsM_unitary)

/-! ## The executable certificates still fire

These `#eval`s are now backed by the theorems above rather than standing in
for them.
-/

#eval FastMatrix.unitaryUpTo beamSplitterV 30
#eval FastMatrix.unitaryUpTo (phaseShifterV (FastReal.pi)) 20
#eval FastMatrix.unitaryUpTo (mzV FastReal.pi) 20

end FastMatrix

end Computable.Fast
