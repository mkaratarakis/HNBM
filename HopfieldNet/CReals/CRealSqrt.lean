import HopfieldNet.CReals.CRealSqrtQ

/-!
# The square root of an arbitrary computable real

`CReal.sqrt : CReal → CReal` (clamping negatives to `0`, like `Real.sqrt`).

Construction: the `n`-th approximant is `ratSqrt (x.approx (2n+8)) (n+3)` —
a dyadic square-root of a rational approximant of `x`, sampled at *doubled*
precision because `√` halves the modulus (`|√a - √b| ≤ √|a-b|`). The data is
purely rational arithmetic; regularity, well-definedness on the quotient, and
the characterisation `toReal (sqrt x) = Real.sqrt (toReal x)` are all proved
classically through `ℝ` (they are `Prop`s, so computability is untouched).

With `toReal_sqrt` in hand, the entire `Real.sqrt` lemma library transfers to
`CReal.sqrt` one `toReal_injective`-line at a time: `sqrt_mul_self`,
`sqrt_zero/one`, `sqrt_mul`, `sqrt_le_sqrt`, `sqrt_nonneg`, …
-/

namespace Computable
namespace CReal

/-! ### Two analytic ingredients -/

/-- The fundamental approximation property: a regular pre-real is within
`2^{-k}` of its `k`-th rational approximant. -/
theorem Pre.toReal_sub_approx (x : CReal.Pre) (k : ℕ) :
    |Pre.toReal x - (x.approx k : ℝ)| ≤ 1 / 2 ^ k := by
  have h : |Real.mk (Pre.toCauSeq x) - (x.approx k : ℝ)| ≤ ((1 / 2 ^ k : ℚ) : ℝ) := by
    apply Real.mk_near_of_forall_near
    refine ⟨k, fun j hj => ?_⟩
    have hreg := x.is_regular k j hj
    rw [abs_sub_comm] at hreg
    exact_mod_cast hreg
  have hc : ((1 / 2 ^ k : ℚ) : ℝ) = 1 / 2 ^ k := by push_cast; ring
  rw [hc] at h
  exact h

/-- `√` is "half-Hölder": `|√a - √b| ≤ √|a-b|`, for all reals. -/
theorem abs_sqrt_sub_sqrt_le (a b : ℝ) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this b a (le_of_not_ge hab)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hab)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  rcases le_or_gt b 0 with hb | hb
  · rw [Real.sqrt_eq_zero'.mpr hb, sub_zero]
    exact Real.sqrt_le_sqrt (by linarith)
  · have h1 : Real.sqrt a ≤ Real.sqrt (a - b) + Real.sqrt b := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (a - b) + Real.sqrt b)]
      apply Real.sqrt_le_sqrt
      have e1 : Real.sqrt (a - b) ^ 2 = a - b := Real.sq_sqrt (by linarith)
      have e2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
      nlinarith [Real.sqrt_nonneg (a - b), Real.sqrt_nonneg b]
    linarith

/-- `ratSqrt_dist` without a sign hypothesis (both sides clamp negatives). -/
theorem ratSqrt_dist' (q : ℚ) (k : ℕ) :
    |((ratSqrt q k : ℚ) : ℝ) - Real.sqrt q| ≤ 2 / 2 ^ k := by
  rcases le_or_gt 0 q with hq | hq
  · exact ratSqrt_dist hq k
  · rw [ratSqrt_of_neg hq,
      Real.sqrt_eq_zero'.mpr (show ((q : ℚ) : ℝ) ≤ 0 by exact_mod_cast hq.le)]
    simp only [Rat.cast_zero, sub_zero, abs_zero]
    positivity

/-! ### The construction -/

/-- Per-index error of the `sqrt` approximants against the true value. -/
theorem sqrt_approx_dist (x : CReal.Pre) (n : ℕ) :
    |((ratSqrt (x.approx (2 * n + 8)) (n + 3) : ℚ) : ℝ) - Real.sqrt (Pre.toReal x)|
      ≤ 2 / 2 ^ (n + 3) + 1 / 2 ^ (n + 4) := by
  set q := x.approx (2 * n + 8) with hqdef
  have h1 : |((ratSqrt q (n + 3) : ℚ) : ℝ) - Real.sqrt (q : ℝ)| ≤ 2 / 2 ^ (n + 3) :=
    ratSqrt_dist' q (n + 3)
  have h2 : |Real.sqrt (q : ℝ) - Real.sqrt (Pre.toReal x)| ≤ 1 / 2 ^ (n + 4) := by
    refine (abs_sqrt_sub_sqrt_le (q : ℝ) (Pre.toReal x)).trans ?_
    have hd : |(q : ℝ) - Pre.toReal x| ≤ 1 / 2 ^ (2 * n + 8) := by
      have h := Pre.toReal_sub_approx x (2 * n + 8)
      rwa [abs_sub_comm] at h
    refine (Real.sqrt_le_sqrt hd).trans ?_
    have hsq : ((1 : ℝ) / 2 ^ (n + 4)) ^ 2 = 1 / 2 ^ (2 * n + 8) := by
      have he : (n + 4) * 2 = 2 * n + 8 := by ring
      rw [div_pow, one_pow, ← pow_mul, he]
    rw [← hsq, Real.sqrt_sq (by positivity)]
  calc |((ratSqrt q (n + 3) : ℚ) : ℝ) - Real.sqrt (Pre.toReal x)|
      ≤ |((ratSqrt q (n + 3) : ℚ) : ℝ) - Real.sqrt (q : ℝ)|
        + |Real.sqrt (q : ℝ) - Real.sqrt (Pre.toReal x)| := abs_sub_le _ _ _
    _ ≤ 2 / 2 ^ (n + 3) + 1 / 2 ^ (n + 4) := add_le_add h1 h2

private theorem scale_eq₁ (n : ℕ) : (2 : ℝ) / 2 ^ (n + 3) = 4 * (1 / 2 ^ (n + 4)) := by
  field_simp
  rw [show n + 4 = (n + 3) + 1 from rfl, pow_succ]
  ring

private theorem scale_eq₂ (n : ℕ) : (1 : ℝ) / 2 ^ n = 16 * (1 / 2 ^ (n + 4)) := by
  field_simp
  rw [pow_add]
  norm_num

/-- The pre-quotient square root. -/
def Pre.sqrt (x : CReal.Pre) : CReal.Pre where
  approx n := ratSqrt (x.approx (2 * n + 8)) (n + 3)
  is_regular := by
    intro n m hnm
    have hn := sqrt_approx_dist x n
    have hm := sqrt_approx_dist x m
    have tri := abs_sub_le
      ((ratSqrt (x.approx (2 * n + 8)) (n + 3) : ℚ) : ℝ)
      (Real.sqrt (Pre.toReal x))
      ((ratSqrt (x.approx (2 * m + 8)) (m + 3) : ℚ) : ℝ)
    rw [abs_sub_comm (Real.sqrt (Pre.toReal x))] at tri
    have e1n := scale_eq₁ n
    have e1m := scale_eq₁ m
    have e2 := scale_eq₂ n
    have hDm : (1 : ℝ) / 2 ^ (m + 4) ≤ 1 / 2 ^ (n + 4) := by
      have hp : (2 : ℝ) ^ (n + 4) ≤ 2 ^ (m + 4) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
    have hDpos : (0 : ℝ) ≤ 1 / 2 ^ (n + 4) := by positivity
    have hb : |((ratSqrt (x.approx (2 * n + 8)) (n + 3) : ℚ) : ℝ)
        - ((ratSqrt (x.approx (2 * m + 8)) (m + 3) : ℚ) : ℝ)|
        ≤ ((1 / 2 ^ n : ℚ) : ℝ) := by
      have hc : ((1 / 2 ^ n : ℚ) : ℝ) = 1 / 2 ^ n := by push_cast; ring
      rw [hc]
      linarith
    exact_mod_cast hb

theorem Pre.toReal_sqrt_aux (x : CReal.Pre) :
    Real.mk (Pre.toCauSeq (Pre.sqrt x)) = Real.sqrt (Pre.toReal x) := by
  set D := Real.mk (Pre.toCauSeq (Pre.sqrt x)) with hD
  have key : ∀ i : ℕ, |D - Real.sqrt (Pre.toReal x)| ≤ (1 / 2 : ℝ) ^ i := by
    intro i
    have hle : (2 : ℝ) / 2 ^ (i + 3) + 1 / 2 ^ (i + 4) ≤ (1 / 2 : ℝ) ^ i := by
      have e1 := scale_eq₁ i
      have e2 := scale_eq₂ i
      have hpos : (0 : ℝ) ≤ 1 / 2 ^ (i + 4) := by positivity
      have hp : ((1 : ℝ) / 2) ^ i = 1 / 2 ^ i := by
        rw [div_pow, one_pow]
      rw [hp]
      linarith
    refine LE.le.trans ?_ hle
    apply Real.mk_near_of_forall_near
    refine ⟨i, fun j hj => ?_⟩
    have happ : ((Pre.toCauSeq (Pre.sqrt x)) j : ℚ)
        = ratSqrt (x.approx (2 * j + 8)) (j + 3) := rfl
    rw [happ]
    refine (sqrt_approx_dist x j).trans ?_
    have h1 : (2 : ℝ) / 2 ^ (j + 3) ≤ 2 / 2 ^ (i + 3) := by
      have hp : (2 : ℝ) ^ (i + 3) ≤ 2 ^ (j + 3) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
    have h2 : (1 : ℝ) / 2 ^ (j + 4) ≤ 1 / 2 ^ (i + 4) := by
      have hp : (2 : ℝ) ^ (i + 4) ≤ 2 ^ (j + 4) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
    linarith
  by_contra hne
  have habs : 0 < |D - Real.sqrt (Pre.toReal x)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one habs (by norm_num : (1 : ℝ) / 2 < 1)
  exact absurd (key i) (not_le.mpr hi)

/-- The square root of a computable real (`0` on negatives). Well-definedness
on the quotient is inherited from `ℝ` through `toReal_injective`. -/
def sqrt : CReal → CReal :=
  Quotient.map Pre.sqrt fun x y h => by
    apply Quotient.exact (s := inferInstance)
    apply toReal_injective
    rw [toReal_mk, toReal_mk]
    show Real.mk (Pre.toCauSeq (Pre.sqrt x)) = Real.mk (Pre.toCauSeq (Pre.sqrt y))
    rw [Pre.toReal_sqrt_aux, Pre.toReal_sqrt_aux, Pre.toReal_congr h]

/-- **Characterisation**: `toReal` intertwines `CReal.sqrt` with `Real.sqrt`. -/
@[simp] theorem toReal_sqrt (x : CReal) : toReal (sqrt x) = Real.sqrt (toReal x) := by
  refine Quotient.inductionOn x fun a => ?_
  show toReal ⟦Pre.sqrt a⟧ = _
  rw [toReal_mk]
  exact Pre.toReal_sqrt_aux a

/-! ### The transferred lemma library -/

theorem sqrt_nonneg (x : CReal) : 0 ≤ sqrt x := by
  rw [← toReal_le_iff]
  simp [Real.sqrt_nonneg]

@[simp] theorem sqrt_zero : sqrt 0 = 0 := by
  apply toReal_injective; simp

@[simp] theorem sqrt_one : sqrt 1 = 1 := by
  apply toReal_injective; simp

theorem sqrt_mul_self {x : CReal} (hx : 0 ≤ x) : sqrt x * sqrt x = x := by
  apply toReal_injective
  have h : (0 : ℝ) ≤ toReal x := by
    rw [← toReal_zero]; exact toReal_mono hx
  simp [Real.mul_self_sqrt h]

theorem sq_sqrt {x : CReal} (hx : 0 ≤ x) : sqrt x ^ 2 = x := by
  apply toReal_injective
  have h : (0 : ℝ) ≤ toReal x := by
    rw [← toReal_zero]; exact toReal_mono hx
  simp [Real.sq_sqrt h]

theorem sqrt_mul {x : CReal} (hx : 0 ≤ x) (y : CReal) :
    sqrt (x * y) = sqrt x * sqrt y := by
  apply toReal_injective
  have h : (0 : ℝ) ≤ toReal x := by
    rw [← toReal_zero]; exact toReal_mono hx
  simp [Real.sqrt_mul h]

theorem sqrt_le_sqrt {x y : CReal} (h : x ≤ y) : sqrt x ≤ sqrt y := by
  rw [← toReal_le_iff]
  simp only [toReal_sqrt]
  exact Real.sqrt_le_sqrt (toReal_mono h)

theorem sqrt_eq_zero_of_nonpos {x : CReal} (h : x ≤ 0) : sqrt x = 0 := by
  apply toReal_injective
  simp only [toReal_sqrt, toReal_zero]
  refine Real.sqrt_eq_zero'.mpr ?_
  rw [← toReal_zero]; exact toReal_mono h

/-- Consistency with the fast rational special case. -/
theorem sqrt_ratCast {q : ℚ} (hq : 0 ≤ q) : sqrt ((q : ℚ) : CReal) = sqrtQ q := by
  apply toReal_injective
  rw [toReal_sqrt, toReal_ratCast, toReal_sqrtQ hq]

end CReal
end Computable
