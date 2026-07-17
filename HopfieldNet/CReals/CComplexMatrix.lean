import HopfieldNet.CReals.CComplexBridge
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# CMatrix: verified complex matrices over computable reals

Square matrices of computable complex numbers, via Mathlib's `Matrix` API.
Because `CommRing CComplex` and `StarRing CComplex` are **computable**
instances, all of the following come from Mathlib for free and remain
computable in principle: matrix `+`, `*` (via `Finset.sum`), `1`,
`conjTranspose` (`Aᴴ` = `star`), and the predicate
`Matrix.unitaryGroup (Fin k) CComplex`.

This file adds the theorem-transfer layer: entrywise `toComplex` is an
injective ring hom into `Matrix (Fin k) (Fin k) ℂ` that intertwines `star`,
so **a computable matrix is unitary iff its Mathlib-`ℂ` image is unitary**
(`mem_unitaryGroup_iff_map`). Facts proved over `ℂ` with Mathlib's analysis
pull back to `CMatrix`, and vice versa.

Executable numerics (certified unitarity bounds) live in
`FastComplexMatrix.lean`.
-/

namespace Computable

/-- Square matrices of computable complex numbers. -/
abbrev CMatrix (k : ℕ) : Type := Matrix (Fin k) (Fin k) CComplex

namespace CComplex

/-- `toComplex` intertwines `CComplex` conjugation with `ℂ`'s star. -/
@[simp] theorem toComplex_conj (z : CComplex) :
    toComplex (conj z) = star (toComplex z) := by
  apply Complex.ext
  · simp
  · simp [CReal.toReal_neg]

@[simp] theorem toComplex_star (z : CComplex) :
    toComplex (star z) = star (toComplex z) :=
  toComplex_conj z

/-- Entrywise `toComplex`, as a ring hom on square matrices. -/
noncomputable def toComplexMatrixHom (k : ℕ) :
    CMatrix k →+* Matrix (Fin k) (Fin k) ℂ :=
  toComplexRingHom.mapMatrix

theorem toComplexMatrixHom_apply {k : ℕ} (A : CMatrix k) :
    toComplexMatrixHom k A = A.map toComplex := rfl

theorem toComplexMatrixHom_injective (k : ℕ) :
    Function.Injective (toComplexMatrixHom k) := by
  intro A B h
  have h' : A.map toComplex = B.map toComplex := h
  refine Matrix.ext fun i j => ?_
  have hij : A.map toComplex i j = B.map toComplex i j := by rw [h']
  rw [Matrix.map_apply, Matrix.map_apply] at hij
  exact toComplex_injective hij

/-- Entrywise `toComplex` commutes with the conjugate transpose. -/
theorem toComplexMatrixHom_star {k : ℕ} (A : CMatrix k) :
    toComplexMatrixHom k (star A) = star (toComplexMatrixHom k A) := by
  show (star A).map toComplex = star (A.map toComplex)
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.star_apply, toComplex_star]

/-- **Unitarity transfers**: a computable complex matrix is unitary iff its
image in Mathlib's `ℂ` is unitary. -/
theorem mem_unitaryGroup_iff_map {k : ℕ} (A : CMatrix k) :
    A ∈ Matrix.unitaryGroup (Fin k) CComplex ↔
      toComplexMatrixHom k A ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · intro h
    rw [← toComplexMatrixHom_star, ← map_mul, h]
    exact map_one _
  · intro h
    refine toComplexMatrixHom_injective k ?_
    rw [map_mul, toComplexMatrixHom_star, h, map_one]

/-! ### Column and row norms of unitaries

The `normSq`s down any column (or across any row) of a unitary matrix sum to
exactly `1`, **as computable reals** — a polynomial statement, no square
roots involved.
-/

theorem sum_normSq_col_of_unitary {k : ℕ} {U : CMatrix k}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) CComplex) (j : Fin k) :
    ∑ i, normSq (U i j) = 1 := by
  have h : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hjj : (star U * U) j j = (1 : CMatrix k) j j := by rw [h]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
  have hterm : ∀ i, (star U) j i * U i j = ofReal (normSq (U i j)) := by
    intro i
    rw [Matrix.star_apply, star_def, mul_comm]
    exact mul_conj (U i j)
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hjj
  have := congrArg re hjj
  simpa [re_sum] using this

theorem sum_normSq_row_of_unitary {k : ℕ} {U : CMatrix k}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) CComplex) (i : Fin k) :
    ∑ j, normSq (U i j) = 1 := by
  have h : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hii : (U * star U) i i = (1 : CMatrix k) i i := by rw [h]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii
  have hterm : ∀ j, U i j * (star U) j i = ofReal (normSq (U i j)) := by
    intro j
    rw [Matrix.star_apply, star_def]
    exact mul_conj (U i j)
  rw [Finset.sum_congr rfl (fun j _ => hterm j)] at hii
  have := congrArg re hii
  simpa [re_sum] using this

/-! ### Sanity examples -/

-- The matrix ring over `CComplex` is available by substitution.
example {k : ℕ} (A B C : CMatrix k) : A * (B + C) = A * B + A * C := mul_add A B C

-- Unitary matrices form a group: the product of unitaries is unitary.
example {k : ℕ} (U V : Matrix.unitaryGroup (Fin k) CComplex) :
    (↑(U * V) : CMatrix k) ∈ Matrix.unitaryGroup (Fin k) CComplex :=
  (U * V).2

end CComplex

end Computable
