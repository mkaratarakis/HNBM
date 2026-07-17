import HopfieldNet.CReals.CComplexBridge
import HopfieldNet.CReals.CRealSqrt
import Mathlib.Analysis.Complex.Norm

/-!
# The absolute value on computable complex numbers

`CComplex.abs z = CReal.sqrt (normSq z)` — **computable**, since both
`normSq` and `CReal.sqrt` are. The transfer lemma
`toReal_abs : toReal (abs z) = ‖toComplex z‖` connects it to the norm on
Mathlib's `ℂ`, and the entire absolute-value lemma library follows one
`toReal_injective`/`toReal_le_iff` line at a time: multiplicativity, the
triangle inequality, `abs_conj`, `abs_eq_zero`, `sq_abs`, …

`absv` bundles it as an `AbsoluteValue CComplex CReal`.
-/

namespace Computable
namespace CComplex

/-! ### `toComplex` pushes through the ring operations (simp set) -/

@[simp] theorem toComplex_zero : toComplex (0 : CComplex) = 0 :=
  map_zero toComplexRingHom

@[simp] theorem toComplex_one : toComplex (1 : CComplex) = 1 :=
  map_one toComplexRingHom

@[simp] theorem toComplex_add (z w : CComplex) :
    toComplex (z + w) = toComplex z + toComplex w :=
  map_add toComplexRingHom z w

@[simp] theorem toComplex_mul (z w : CComplex) :
    toComplex (z * w) = toComplex z * toComplex w :=
  map_mul toComplexRingHom z w

@[simp] theorem toComplex_neg (z : CComplex) : toComplex (-z) = -toComplex z :=
  map_neg toComplexRingHom z

@[simp] theorem toComplex_sub (z w : CComplex) :
    toComplex (z - w) = toComplex z - toComplex w :=
  map_sub toComplexRingHom z w

@[simp] theorem toComplex_pow (z : CComplex) (n : ℕ) :
    toComplex (z ^ n) = toComplex z ^ n :=
  map_pow toComplexRingHom z n

/-! ### The absolute value -/

/-- The absolute value `|z| = √(re² + im²)`, as a computable real. -/
def abs (z : CComplex) : CReal := CReal.sqrt (normSq z)

/-- **Transfer**: `abs` agrees with the norm on `ℂ`. -/
@[simp] theorem toReal_abs (z : CComplex) :
    CReal.toReal (abs z) = ‖toComplex z‖ := by
  rw [abs, CReal.toReal_sqrt, ← toComplex_normSq, Complex.norm_def]

theorem abs_nonneg (z : CComplex) : 0 ≤ abs z :=
  CReal.sqrt_nonneg _

@[simp] theorem abs_zero : abs (0 : CComplex) = 0 := by
  apply CReal.toReal_injective; simp

@[simp] theorem abs_one : abs (1 : CComplex) = 1 := by
  apply CReal.toReal_injective; simp

@[simp] theorem abs_I : abs I = 1 := by
  apply CReal.toReal_injective; simp

theorem abs_mul (z w : CComplex) : abs (z * w) = abs z * abs w := by
  apply CReal.toReal_injective; simp

@[simp] theorem abs_conj (z : CComplex) : abs (conj z) = abs z := by
  unfold abs; rw [normSq_conj]

theorem abs_add (z w : CComplex) : abs (z + w) ≤ abs z + abs w := by
  rw [← CReal.toReal_le_iff]
  simp only [toReal_abs, CReal.toReal_add, toComplex_add]
  exact norm_add_le _ _

@[simp] theorem abs_neg (z : CComplex) : abs (-z) = abs z := by
  apply CReal.toReal_injective; simp

@[simp] theorem abs_eq_zero {z : CComplex} : abs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply toComplex_injective
    have h' := congrArg CReal.toReal h
    simp only [toReal_abs, CReal.toReal_zero, norm_eq_zero] at h'
    simpa using h'
  · rintro rfl
    exact abs_zero

/-- `|z|² = normSq z`: the absolute value squares back to the norm-square. -/
theorem sq_abs (z : CComplex) : abs z * abs z = normSq z :=
  CReal.sqrt_mul_self (normSq_nonneg z)

theorem abs_ofReal {x : CReal} (hx : 0 ≤ x) : abs (ofReal x) = x := by
  apply CReal.toReal_injective
  rw [toReal_abs, toComplex_ofReal]
  have h : (0 : ℝ) ≤ CReal.toReal x := by
    rw [← CReal.toReal_zero]; exact CReal.toReal_mono hx
  simp [Complex.norm_real, abs_of_nonneg h]

/-- `abs`, bundled as an `AbsoluteValue`. -/
def absv : AbsoluteValue CComplex CReal where
  toFun := abs
  map_mul' := abs_mul
  nonneg' := abs_nonneg
  eq_zero' := fun _ => abs_eq_zero
  add_le' := abs_add

@[simp] theorem absv_apply (z : CComplex) : absv z = abs z := rfl

/-! ### Sanity examples -/

example (z w : CComplex) : abs (z * w) * abs (z * w) = normSq z * normSq w := by
  rw [sq_abs, normSq_mul]

example (z : CComplex) : abs (z * conj z) = normSq z := by
  rw [mul_conj, abs_ofReal (normSq_nonneg z)]

end CComplex
end Computable
