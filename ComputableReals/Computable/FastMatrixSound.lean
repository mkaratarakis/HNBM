/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.FastComplexSound
import ComputableReals.FoldSum
import ComputableReals.Computable.ExpSound
import ComputableReals.FastComplexMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Soundness of the executable complex matrices — the unitarity certificate

The capstone of the complex refinement layer. `FastMatrix m n` is a grid of
`FastComplex`; its enclosure of a Mathlib matrix is entrywise. Every
operation reduces to `FastComplexSound`:

* `sumFin_encloses` — the fold-sum encloses `∑` (bridged through
  `Sums.finRange_foldl_add_eq_sum` on `ℂ`);
* `mul_encloses` / `conjTranspose_encloses` / `one_encloses` /
  `sub_encloses` — matrix algebra;
* `certSmallC_sound` — the executable `|z| < 2^{-tol}` bound is sound:
  a `true` verdict proves the *real* enclosed complex has both components
  below `2^{-tol}`;
* **`unitaryUpTo_sound`** — the payoff: if the executable certificate
  `unitaryUpTo U tol` returns `true` and `U` encloses a Mathlib matrix `M`,
  then every entry of `M · Mᴴ − 1` has both components `< 2^{-tol}`. The
  optical unitarity check (e.g. a beam splitter) is thus a *theorem* about
  the honest `ℂ`-valued matrix, not a floating-point hope.
-/

open Computable.Fast Computable.Fast.API Matrix

namespace Computable.Fast

namespace FastMatrix

variable {m n p : ℕ}

/-- Entrywise enclosure of a Mathlib complex matrix by a `FastMatrix`. -/
def Encloses (A : FastMatrix m n) (M : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i j, (A i j).Encloses (M i j)

/-- The fold-sum encloses the Mathlib `∑`. -/
theorem sumFin_encloses {f : Fin n → FastComplex} {g : Fin n → ℂ}
    (h : ∀ k, (f k).Encloses (g k)) : (FastMatrix.sumFin f).Encloses (∑ k, g k) := by
  have hfold : ∀ (l : List (Fin n)) {z0 : FastComplex} {c0 : ℂ}, z0.Encloses c0 →
      (l.foldl (fun acc k => acc + f k) z0).Encloses (l.foldl (fun acc k => acc + g k) c0) := by
    intro l
    induction l with
    | nil => intro z0 c0 h0; simpa using h0
    | cons a t ih =>
      intro z0 c0 h0
      simp only [List.foldl_cons]
      exact ih (FastComplex.add_encloses h0 (h a))
  have hz : (FastMatrix.sumFin f).Encloses
      ((List.finRange n).foldl (fun acc k => acc + g k) 0) :=
    hfold (List.finRange n) FastComplex.encloses_zero
  rwa [Sums.finRange_foldl_add_eq_sum g] at hz

/-- Matrix multiplication preserves enclosure. -/
theorem mul_encloses {A : FastMatrix m n} {B : FastMatrix n p}
    {M : Matrix (Fin m) (Fin n) ℂ} {N : Matrix (Fin n) (Fin p) ℂ}
    (hA : A.Encloses M) (hB : B.Encloses N) : (A * B).Encloses (M * N) := by
  intro i j
  show (FastMatrix.sumFin (fun k => A i k * B k j)).Encloses ((M * N) i j)
  rw [Matrix.mul_apply]
  exact sumFin_encloses (fun k => FastComplex.mul_encloses (hA i k) (hB k j))

/-- Conjugate transpose preserves enclosure. -/
theorem conjTranspose_encloses {A : FastMatrix m n} {M : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) : (FastMatrix.conjTranspose A).Encloses Mᴴ := by
  intro i j
  show ((A j i).conj).Encloses (Mᴴ i j)
  rw [Matrix.conjTranspose_apply, show star (M j i) = (starRingEnd ℂ) (M j i) from rfl]
  exact FastComplex.conj_encloses (hA j i)

/-- The identity matrix encloses the Mathlib identity. -/
theorem one_encloses : (FastMatrix.one : FastMatrix n n).Encloses 1 := by
  intro i j
  show (if i = j then (1 : FastComplex) else 0).Encloses ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
  rw [Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; exact FastComplex.encloses_one
  · rw [if_neg h, if_neg h]; exact FastComplex.encloses_zero

/-- Subtraction preserves enclosure. -/
theorem sub_encloses {A B : FastMatrix m n}
    {M N : Matrix (Fin m) (Fin n) ℂ} (hA : A.Encloses M) (hB : B.Encloses N) :
    (A - B).Encloses (M - N) := by
  intro i j
  show (A i j - B i j).Encloses ((M - N) i j)
  rw [Matrix.sub_apply]
  exact FastComplex.sub_encloses (hA i j) (hB i j)

/-! ## The certificate is sound -/

/-- `certSmall x tol = true` proves the enclosed real is below `2^{-tol}`. -/
theorem certSmall_sound {x : FastReal} {r : ℝ} {tol : ℕ}
    (hx : x.Encloses r) (h : FastMatrix.certSmall x tol = true) :
    |r| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ) := by
  have hlt : (x (tol + 4)).absUpper < (⟨1, -(tol : ℤ)⟩ : Dyadic) := by
    simpa [FastMatrix.certSmall] using h
  have h1 : |r| ≤ (((x (tol + 4)).absUpper.toRat : ℚ) : ℝ) := Ball.absUpper_sound (hx _)
  have h2 : (((x (tol + 4)).absUpper.toRat : ℚ) : ℝ)
      < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ) := by
    have := Dyadic.toRat_lt_iff.mp hlt
    exact_mod_cast this
  exact lt_of_le_of_lt h1 h2

/-- `certSmallC z tol = true` proves both components of the enclosed complex
are below `2^{-tol}`. -/
theorem certSmallC_sound {z : FastComplex} {c : ℂ} {tol : ℕ}
    (hz : z.Encloses c) (h : FastMatrix.certSmallC z tol = true) :
    |c.re| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ)
    ∧ |c.im| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ) := by
  obtain ⟨hre, him⟩ := Bool.and_eq_true _ _ |>.mp h
  exact ⟨certSmall_sound hz.1 hre, certSmall_sound hz.2 him⟩

/-- `approxEq A B tol = true` proves every entry of `M − N` is small. -/
theorem approxEq_sound {A B : FastMatrix m n} {M N : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) (hB : B.Encloses N) {tol : ℕ}
    (h : FastMatrix.approxEq A B tol = true) :
    ∀ i j, |((M - N) i j).re| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ)
      ∧ |((M - N) i j).im| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ) := by
  intro i j
  have hcell : FastMatrix.certSmallC (A i j - B i j) tol = true := by
    simp only [FastMatrix.approxEq, List.all_eq_true, List.mem_finRange] at h
    exact h i (by trivial) j (by trivial)
  have hsub := sub_encloses hA hB i j
  exact certSmallC_sound hsub hcell

/-- **The unitarity certificate is a theorem.** If `unitaryUpTo U tol`
returns `true` and `U` encloses the Mathlib matrix `M`, then every entry of
`M · Mᴴ − 1` has both real and imaginary parts strictly below `2^{-tol}`:
`M` is unitary to within `2^{-tol}`, rigorously. -/
theorem unitaryUpTo_sound {U : FastMatrix n n} {M : Matrix (Fin n) (Fin n) ℂ}
    (hU : U.Encloses M) {tol : ℕ} (h : FastMatrix.unitaryUpTo U tol = true) :
    ∀ i j, |((M * Mᴴ - 1) i j).re| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ)
      ∧ |((M * Mᴴ - 1) i j).im| < ((Dyadic.toRat ⟨1, -(tol : ℤ)⟩ : ℚ) : ℝ) := by
  have hUU : (U * FastMatrix.conjTranspose U).Encloses (M * Mᴴ) :=
    mul_encloses hU (conjTranspose_encloses hU)
  exact approxEq_sound hUU one_encloses h

/-! ## Vectors: propagating a state through a device

`mulVec` is how light actually moves through a component: an amplitude
vector goes in, an amplitude vector comes out. Enclosure for it is what
turns an executable simulation into a statement about the true complex
amplitudes.
-/

/-- Entrywise enclosure of a complex vector by a vector of `FastComplex`. -/
def VecEncloses (v : Fin n → FastComplex) (w : Fin n → ℂ) : Prop :=
  ∀ i, (v i).Encloses (w i)

/-- **Applying a matrix to a vector preserves enclosure.** -/
theorem mulVec_encloses {A : FastMatrix m n} {M : Matrix (Fin m) (Fin n) ℂ}
    {v : Fin n → FastComplex} {w : Fin n → ℂ}
    (hA : A.Encloses M) (hv : VecEncloses v w) :
    VecEncloses (A.mulVec v) (M.mulVec w) := by
  intro i
  show (FastMatrix.sumFin (fun k => A i k * v k)).Encloses ((M.mulVec w) i)
  simpa [Matrix.mulVec, dotProduct] using
    sumFin_encloses fun k => FastComplex.mul_encloses (hA i k) (hv k)

/-- A vector of literals encloses itself entrywise (convenience wrapper). -/
theorem vecEncloses_of (v : Fin n → FastComplex) (w : Fin n → ℂ)
    (h : ∀ i, (v i).Encloses (w i)) : VecEncloses v w := h

/-! ## The remaining matrix operations -/

/-- The zero matrix encloses `0`. -/
theorem zero_encloses : (FastMatrix.zero : FastMatrix m n).Encloses 0 :=
  fun _ _ => FastComplex.encloses_zero

/-- Addition preserves enclosure. -/
theorem add_encloses {A B : FastMatrix m n} {M N : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) (hB : B.Encloses N) : (A + B).Encloses (M + N) :=
  fun i j => FastComplex.add_encloses (hA i j) (hB i j)

/-- Negation preserves enclosure. -/
theorem neg_encloses {A : FastMatrix m n} {M : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) : (-A).Encloses (-M) :=
  fun i j => FastComplex.neg_encloses (hA i j)

/-- Scalar multiplication preserves enclosure. -/
theorem smul_encloses {c : FastComplex} {d : ℂ} {A : FastMatrix m n}
    {M : Matrix (Fin m) (Fin n) ℂ}
    (hc : c.Encloses d) (hA : A.Encloses M) : (c • A).Encloses (d • M) :=
  fun i j => FastComplex.mul_encloses hc (hA i j)

/-- Transpose preserves enclosure. -/
theorem transpose_encloses {A : FastMatrix m n} {M : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) : (FastMatrix.transpose A).Encloses Mᵀ :=
  fun i j => hA j i

/-- The trace encloses Mathlib's trace. -/
theorem trace_encloses {A : FastMatrix n n} {M : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.Encloses M) : (FastMatrix.trace A).Encloses (Matrix.trace M) :=
  sumFin_encloses fun i => hA i i

/-! ## Kronecker product: composing optical modes

`FastMatrix.kron` is indexed by `Fin (m * p)` and splits an index with
`Fin.divNat`/`Fin.modNat`. The enclosed Mathlib matrix is the same
index-split of the entrywise product, which is Mathlib's Kronecker product
transported along `finProdFinEquiv`.
-/

/-- The `Fin (m * p)`-indexed Kronecker product of two Mathlib matrices,
matching `FastMatrix.kron`'s indexing convention. -/
def kronM (MA : Matrix (Fin m) (Fin n) ℂ) (MB : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin (m * p)) (Fin (n * q)) ℂ :=
  fun i j => MA i.divNat j.divNat * MB i.modNat j.modNat

/-- **The Kronecker product preserves enclosure** — composing two certified
components gives a certified composite. -/
theorem kron_encloses {A : FastMatrix m n} {B : FastMatrix p q}
    {MA : Matrix (Fin m) (Fin n) ℂ} {MB : Matrix (Fin p) (Fin q) ℂ}
    (hA : A.Encloses MA) (hB : B.Encloses MB) :
    (A.kron B).Encloses (kronM MA MB) :=
  fun i j => FastComplex.mul_encloses (hA i.divNat j.divNat) (hB i.modNat j.modNat)

/-- `kronM` really is the entrywise Kronecker rule. -/
@[simp] theorem kronM_apply (MA : Matrix (Fin m) (Fin n) ℂ)
    (MB : Matrix (Fin p) (Fin q) ℂ) (i : Fin (m * p)) (j : Fin (n * q)) :
    kronM MA MB i j = MA i.divNat j.divNat * MB i.modNat j.modNat := rfl

/-! ## Structural lemmas -/

/-- Enclosure only depends on the entries, so it transfers along entrywise
equality of the executable matrices. -/
theorem Encloses.congr {A B : FastMatrix m n} {M : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) (h : ∀ i j, A i j = B i j) : B.Encloses M :=
  fun i j => h i j ▸ hA i j

/-- Enclosure transfers along entrywise equality of the enclosed matrices. -/
theorem Encloses.congr_right {A : FastMatrix m n} {M N : Matrix (Fin m) (Fin n) ℂ}
    (hA : A.Encloses M) (h : ∀ i j, M i j = N i j) : A.Encloses N :=
  fun i j => h i j ▸ hA i j

/-! ## Demo: a balanced beam splitter is certifiably unitary

The `2×2` Hadamard beam splitter `(1/√2)·[[1,1],[1,−1]]` — with the
`1/√2` amplitude computed as the (total) `√(1/2)`. `unitaryUpTo` fires
`true`, so `unitaryUpTo_sound` certifies the corresponding `ℂ`-matrix is
unitary to `2^{-tol}`. -/

/-- `1/√2` as a total `FastReal` (`= √(1/2)`). -/
private def invSqrt2 : FastReal := FastReal.sqrt (FastReal.ofDyadic ⟨1, -1⟩)

/-- The balanced beam splitter. -/
private def beamSplitter : FastMatrix 2 2 := fun i j =>
  if i = 1 ∧ j = 1 then ⟨FastReal.neg invSqrt2, 0⟩ else ⟨invSqrt2, 0⟩

-- The executable certificate fires: expect `true`. Hence its `ℂ`-image is
-- unitary to within `2^{-30}` by `unitaryUpTo_sound`.
#eval FastMatrix.unitaryUpTo beamSplitter 30

end FastMatrix

end Computable.Fast
