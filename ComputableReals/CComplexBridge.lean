import ComputableReals.CComplex
import ComputableReals.CRealCCLOF
import Mathlib.Data.Complex.Basic

/-!
# CComplex ↔ ℂ bridge (theorem-transfer layer)

Mirrors `CRealCCLOF`/`ComputableRealsBridge` for the complex numbers:

* `toComplex : CComplex →+* ℂ` pushes computable complex numbers forward to
  Mathlib's `ℂ` (componentwise `CReal.toRealRingHom`), where all of Mathlib's
  complex analysis applies. It is injective, so `ℂ`-level equalities pull back.
* A classical (noncomputable) `Field CComplex` instance, so generic
  field-based developments instantiate at `CComplex` by substitution.
  Execution stays in `FastComplex`; this layer proves but does not execute.
-/

namespace Computable

namespace CComplex

/-- Push a computable complex number forward to Mathlib's `ℂ`. -/
def toComplex (z : CComplex) : ℂ :=
  ⟨CReal.toReal z.re, CReal.toReal z.im⟩

@[simp] theorem toComplex_re (z : CComplex) : (toComplex z).re = CReal.toReal z.re := rfl
@[simp] theorem toComplex_im (z : CComplex) : (toComplex z).im = CReal.toReal z.im := rfl

theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  ext
  · exact CReal.toReal_injective (congrArg Complex.re h)
  · exact CReal.toReal_injective (congrArg Complex.im h)

/-- `toComplex` as a ring homomorphism. -/
def toComplexRingHom : CComplex →+* ℂ where
  toFun := toComplex
  map_one' := by
    apply Complex.ext <;> simp
  map_mul' := by
    intro z w
    apply Complex.ext
    · -- `CReal` subtraction is definitionally `a + -b`; `show` avoids the
      -- non-canonical `Sub CReal` instance paths that block `simp` rewriting.
      show CReal.toReal (z.re * w.re + -(z.im * w.im)) = _
      rw [CReal.toReal_add, CReal.toReal_neg, CReal.toReal_mul, CReal.toReal_mul]
      simp only [Complex.mul_re, toComplex_re, toComplex_im]
      ring
    · show CReal.toReal (z.re * w.im + z.im * w.re) = _
      rw [CReal.toReal_add, CReal.toReal_mul, CReal.toReal_mul]
      simp only [Complex.mul_im, toComplex_re, toComplex_im]
  map_zero' := by
    apply Complex.ext <;> simp
  map_add' := by
    intro z w
    apply Complex.ext
    · show CReal.toReal (z.re + w.re) = _
      rw [CReal.toReal_add]; simp
    · show CReal.toReal (z.im + w.im) = _
      rw [CReal.toReal_add]; simp

@[simp] theorem toComplexRingHom_apply (z : CComplex) :
    toComplexRingHom z = toComplex z := rfl

@[simp] theorem toComplex_I : toComplex I = Complex.I := by
  apply Complex.ext <;> simp

theorem toComplex_ofReal (x : CReal) :
    toComplex (ofReal x) = (CReal.toReal x : ℂ) := by
  apply Complex.ext <;> simp

/-! ### Ring equivalence with Mathlib's `ℂ` -/

/-- The (noncomputable) inverse: pull a Mathlib complex number back to `CComplex`
componentwise via `CReal.FromReal.ofReal`. -/
noncomputable def ofComplex (w : ℂ) : CComplex :=
  ⟨CReal.FromReal.ofReal w.re, CReal.FromReal.ofReal w.im⟩

@[simp] theorem toComplex_ofComplex (w : ℂ) : toComplex (ofComplex w) = w := by
  apply Complex.ext <;> simp [ofComplex, CReal.toReal_ofReal]

@[simp] theorem ofComplex_toComplex (z : CComplex) : ofComplex (toComplex z) = z := by
  ext <;> simp [ofComplex, CReal.ofReal_toReal]

theorem toComplex_surjective : Function.Surjective toComplex :=
  fun w => ⟨ofComplex w, toComplex_ofComplex w⟩

theorem toComplex_bijective : Function.Bijective toComplex :=
  ⟨toComplex_injective, toComplex_surjective⟩

/-- The computable complex numbers are ring-equivalent to Mathlib's `ℂ`
(noncomputably: the inverse direction goes through `FromReal.ofReal`, which
cannot be computable since Mathlib's `ℝ` erases moduli of convergence). -/
noncomputable def complexRingEquiv : CComplex ≃+* ℂ where
  toFun := toComplex
  invFun := ofComplex
  left_inv := ofComplex_toComplex
  right_inv := toComplex_ofComplex
  map_mul' := map_mul toComplexRingHom
  map_add' := map_add toComplexRingHom

@[simp] theorem complexRingEquiv_apply (z : CComplex) :
    complexRingEquiv z = toComplex z := rfl

@[simp] theorem complexRingEquiv_symm_apply (w : ℂ) :
    complexRingEquiv.symm w = ofComplex w := rfl

/-! ### Classical field structure -/

theorem normSq_pos_of_ne_zero {z : CComplex} (hz : z ≠ 0) : 0 < normSq z := by
  show 0 < z.re * z.re + z.im * z.im
  rcases eq_or_ne z.re 0 with h1 | h1
  · rcases eq_or_ne z.im 0 with h2 | h2
    · exact absurd (CComplex.ext h1 h2) hz
    · exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.mpr h2)
  · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr h1) (mul_self_nonneg _)

theorem normSq_ne_zero_of_ne_zero {z : CComplex} (hz : z ≠ 0) : normSq z ≠ 0 :=
  ne_of_gt (normSq_pos_of_ne_zero hz)

theorem normSq_nonneg (z : CComplex) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] theorem normSq_eq_zero {z : CComplex} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact normSq_ne_zero_of_ne_zero hz h
  · rintro rfl
    exact normSq_zero

/-- `toComplex` intertwines the computable `normSq` with Mathlib's. -/
theorem toComplex_normSq (z : CComplex) :
    Complex.normSq (toComplex z) = CReal.toReal (normSq z) := by
  rw [show normSq z = z.re * z.re + z.im * z.im from rfl, CReal.toReal_add,
    CReal.toReal_mul, CReal.toReal_mul]
  simp [Complex.normSq_apply]

noncomputable instance : Inv CComplex :=
  ⟨fun z => ⟨z.re * (normSq z)⁻¹, -z.im * (normSq z)⁻¹⟩⟩

@[simp] theorem inv_re (z : CComplex) : z⁻¹.re = z.re * (normSq z)⁻¹ := rfl
@[simp] theorem inv_im (z : CComplex) : z⁻¹.im = -z.im * (normSq z)⁻¹ := rfl

noncomputable instance : Field CComplex where
  inv := Inv.inv
  nnqsmul := _
  qsmul := _
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg re h)⟩
  mul_inv_cancel := by
    intro z hz
    have hN : normSq z ≠ 0 := normSq_ne_zero_of_ne_zero hz
    have key : z.re * z.re + z.im * z.im = normSq z := rfl
    ext
    · show z.re * (z.re * (normSq z)⁻¹) + -(z.im * (-z.im * (normSq z)⁻¹)) = 1
      have h : z.re * (z.re * (normSq z)⁻¹) + -(z.im * (-z.im * (normSq z)⁻¹))
          = (z.re * z.re + z.im * z.im) * (normSq z)⁻¹ := by ring
      rw [h, key, mul_inv_cancel₀ hN]
    · show z.re * (-z.im * (normSq z)⁻¹) + z.im * (z.re * (normSq z)⁻¹) = 0
      ring
  inv_zero := by
    ext <;> simp

/-! ### `toComplex` preserves inversion and division

`toComplex` is a ring hom between fields, hence preserves `⁻¹` and `/`. This
completes the transfer picture: the full field structure moves across. -/

@[simp] theorem toComplex_inv (z : CComplex) : toComplex z⁻¹ = (toComplex z)⁻¹ :=
  map_inv₀ toComplexRingHom z

@[simp] theorem toComplex_div (z w : CComplex) :
    toComplex (z / w) = toComplex z / toComplex w :=
  map_div₀ toComplexRingHom z w

@[simp] theorem toComplex_zpow (z : CComplex) (n : ℤ) :
    toComplex (z ^ n) = toComplex z ^ n :=
  map_zpow₀ toComplexRingHom z n

/-! ### Theorem transfer examples

Generic field theorems instantiate at `CComplex` by substitution, and
`ℂ`-level equalities pull back along the injective ring hom.
-/

example (w : CComplex) (hw : w ≠ 0) : w * w⁻¹ = 1 := mul_inv_cancel₀ hw

example : (I : CComplex) ^ 2 = -1 := by rw [sq, I_mul_I]

example (z w : CComplex) (h : toComplex z = toComplex w) : z = w :=
  toComplex_injective h

example (z w : CComplex) : toComplex (z * w) = toComplex z * toComplex w :=
  map_mul toComplexRingHom z w

end CComplex

end Computable
