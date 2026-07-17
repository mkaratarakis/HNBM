import HopfieldNet.CReals.CRealCast
import Mathlib.Data.Real.Sqrt

/-!
# Verified square roots of rationals as computable reals

`CReal.sqrtQ q` is `√q` as a computable real (`0` for `q < 0`): the underlying
data is the explicit rational sequence `Nat.sqrt ⌊q·4^k⌋₊ / 2^k` (computable),
while the regularity and correctness *proofs* freely use classical facts about
`Real.sqrt` — proofs are `Prop`s, so this does not compromise computability.

Main results:
* `CReal.toReal_sqrtQ : toReal (sqrtQ q) = Real.sqrt q` (for `0 ≤ q`);
* `CReal.sqrtQ_mul_self : sqrtQ q * sqrtQ q = (q : CReal)` (for `0 ≤ q`).

The general `CReal.sqrt : CReal → CReal` (arbitrary computable-real input)
lives in `CRealSqrt.lean`; this file is the rational special case with a
direct, fast representative.
-/

namespace Computable
namespace CReal

/-- Rational approximation to `√q` from below at scale `2^{-k}`. -/
def ratSqrt (q : ℚ) (k : ℕ) : ℚ :=
  (Nat.sqrt ⌊q * 4 ^ k⌋₊ : ℚ) / 2 ^ k

theorem ratSqrt_nonneg (q : ℚ) (k : ℕ) : 0 ≤ ratSqrt q k := by
  unfold ratSqrt; positivity

theorem ratSqrt_cast (q : ℚ) (k : ℕ) :
    ((ratSqrt q k : ℚ) : ℝ) = (Nat.sqrt ⌊q * 4 ^ k⌋₊ : ℝ) / 2 ^ k := by
  unfold ratSqrt; push_cast; ring

private theorem pow_two_pow_eq (k : ℕ) : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem ratSqrt_le_sqrt {q : ℚ} (hq : 0 ≤ q) (k : ℕ) :
    ((ratSqrt q k : ℚ) : ℝ) ≤ Real.sqrt q := by
  set m := ⌊q * 4 ^ k⌋₊ with hm
  have hle : ((Nat.sqrt m : ℝ)) ^ 2 ≤ (m : ℝ) := by
    exact_mod_cast Nat.sqrt_le' m
  have hfl : (m : ℝ) ≤ (q : ℝ) * 4 ^ k := by
    have h : ((m : ℚ)) ≤ q * 4 ^ k := Nat.floor_le (by positivity)
    exact_mod_cast h
  have hsq : (((ratSqrt q k : ℚ) : ℝ)) ^ 2 ≤ (q : ℝ) := by
    rw [ratSqrt_cast, div_pow, pow_two_pow_eq]
    rw [div_le_iff₀ (by positivity)]
    calc (Nat.sqrt m : ℝ) ^ 2 ≤ (m : ℝ) := hle
      _ ≤ (q : ℝ) * 4 ^ k := hfl
  calc ((ratSqrt q k : ℚ) : ℝ)
      = Real.sqrt ((((ratSqrt q k : ℚ) : ℝ)) ^ 2) := by
        rw [Real.sqrt_sq (by exact_mod_cast ratSqrt_nonneg q k)]
    _ ≤ Real.sqrt q := Real.sqrt_le_sqrt hsq

theorem sqrt_le_ratSqrt_add {q : ℚ} (_hq : 0 ≤ q) (k : ℕ) :
    Real.sqrt q ≤ ((ratSqrt q k : ℚ) : ℝ) + 2 / 2 ^ k := by
  set m := ⌊q * 4 ^ k⌋₊ with hm
  have h1 : (q : ℝ) * 4 ^ k < (m : ℝ) + 1 := by
    have h : q * 4 ^ k < (m : ℚ) + 1 := Nat.lt_floor_add_one (q * 4 ^ k)
    exact_mod_cast h
  have h2 : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' m
  have ha : (0 : ℝ) ≤ (Nat.sqrt m : ℝ) := Nat.cast_nonneg _
  have key : (q : ℝ) ≤ (((Nat.sqrt m : ℝ) + 2) / 2 ^ k) ^ 2 := by
    rw [div_pow, pow_two_pow_eq, le_div_iff₀ (by positivity)]
    nlinarith
  calc Real.sqrt q
      ≤ Real.sqrt ((((Nat.sqrt m : ℝ) + 2) / 2 ^ k) ^ 2) := Real.sqrt_le_sqrt key
    _ = ((Nat.sqrt m : ℝ) + 2) / 2 ^ k := Real.sqrt_sq (by positivity)
    _ = ((ratSqrt q k : ℚ) : ℝ) + 2 / 2 ^ k := by rw [ratSqrt_cast]; ring

/-- The approximants are within `2/2^k` of `√q`. -/
theorem ratSqrt_dist {q : ℚ} (hq : 0 ≤ q) (k : ℕ) :
    |((ratSqrt q k : ℚ) : ℝ) - Real.sqrt q| ≤ 2 / 2 ^ k := by
  rw [abs_sub_le_iff]
  constructor
  · have h := ratSqrt_le_sqrt hq k
    have h2 : (0 : ℝ) ≤ 2 / 2 ^ k := by positivity
    linarith
  · have h := sqrt_le_ratSqrt_add hq k
    linarith

theorem ratSqrt_of_neg {q : ℚ} (hq : q < 0) (k : ℕ) : ratSqrt q k = 0 := by
  have h4 : (0 : ℚ) < 4 ^ k := by positivity
  have : q * 4 ^ k ≤ 0 := by nlinarith
  simp [ratSqrt, Nat.floor_of_nonpos this]

/-- The pre-quotient representative of `√q`. -/
def Pre.sqrtQ (q : ℚ) : CReal.Pre where
  approx n := ratSqrt q (n + 2)
  is_regular := by
    intro n m hnm
    rcases le_or_gt 0 q with hq | hq
    · have h1 := ratSqrt_dist hq (n + 2)
      have h2 := ratSqrt_dist hq (m + 2)
      have hmono : (2 : ℝ) / 2 ^ (m + 2) ≤ 2 / 2 ^ (n + 2) := by
        have hp : (2 : ℝ) ^ (n + 2) ≤ 2 ^ (m + 2) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
      have hbound : |((ratSqrt q (n + 2) : ℚ) : ℝ) - ((ratSqrt q (m + 2) : ℚ) : ℝ)|
          ≤ 2 / 2 ^ (n + 2) + 2 / 2 ^ (n + 2) := by
        have tri := abs_sub_le ((ratSqrt q (n + 2) : ℚ) : ℝ) (Real.sqrt q)
          ((ratSqrt q (m + 2) : ℚ) : ℝ)
        rw [abs_sub_comm (Real.sqrt q)] at tri
        linarith
      have h4 : (2 : ℝ) / 2 ^ (n + 2) + 2 / 2 ^ (n + 2) = ((1 / 2 ^ n : ℚ) : ℝ) := by
        push_cast
        rw [pow_add]
        field_simp
        ring
      rw [h4] at hbound
      exact_mod_cast hbound
    · have hz : ∀ k, ratSqrt q k = 0 := fun k => ratSqrt_of_neg hq k
      simp only [hz, sub_zero, abs_zero]
      positivity

/-- `√q` as a computable real (`0` for `q < 0`). -/
def sqrtQ (q : ℚ) : CReal := ⟦Pre.sqrtQ q⟧

theorem toReal_sqrtQ {q : ℚ} (hq : 0 ≤ q) : toReal (sqrtQ q) = Real.sqrt q := by
  show Real.mk (Pre.toCauSeq (Pre.sqrtQ q)) = Real.sqrt q
  set D := Real.mk (Pre.toCauSeq (Pre.sqrtQ q)) with hD
  have key : ∀ i : ℕ, |D - Real.sqrt q| ≤ 2 / 2 ^ (i + 2) := by
    intro i
    apply Real.mk_near_of_forall_near
    refine ⟨i, fun j hj => ?_⟩
    have happ : ((Pre.toCauSeq (Pre.sqrtQ q)) j : ℚ) = ratSqrt q (j + 2) := rfl
    rw [happ]
    refine (ratSqrt_dist hq (j + 2)).trans ?_
    have hp : (2 : ℝ) ^ (i + 2) ≤ 2 ^ (j + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
  by_contra hne
  have habs : 0 < |D - Real.sqrt q| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one habs (by norm_num : (1 : ℝ) / 2 < 1)
  have hlt : (2 : ℝ) / 2 ^ (i + 2) < |D - Real.sqrt q| := by
    have he : (2 : ℝ) / 2 ^ (i + 2) = (1 / 2) ^ (i + 1) := by
      rw [div_pow, one_pow, show i + 2 = (i + 1) + 1 from rfl, pow_succ]
      have : ((2 : ℝ)) ^ (i + 1) ≠ 0 := by positivity
      field_simp
    have hle : ((1 : ℝ) / 2) ^ (i + 1) ≤ (1 / 2) ^ i := by
      rw [pow_succ]
      have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i := by positivity
      nlinarith
    calc (2 : ℝ) / 2 ^ (i + 2) = (1 / 2) ^ (i + 1) := he
      _ ≤ (1 / 2) ^ i := hle
      _ < |D - Real.sqrt q| := hi
  exact absurd (key i) (not_le.mpr hlt)

/-- The defining equation: `√q · √q = q` over the computable reals. -/
theorem sqrtQ_mul_self {q : ℚ} (hq : 0 ≤ q) : sqrtQ q * sqrtQ q = ((q : ℚ) : CReal) := by
  apply toReal_injective
  rw [toReal_mul, toReal_sqrtQ hq, toReal_ratCast,
    Real.mul_self_sqrt (by exact_mod_cast hq)]

/-- `sqrtQ q` is nonnegative (for `0 ≤ q`). -/
theorem sqrtQ_nonneg {q : ℚ} (hq : 0 ≤ q) : (0 : CReal) ≤ sqrtQ q := by
  rw [← toReal_le_iff, toReal_sqrtQ hq, toReal_zero]
  exact Real.sqrt_nonneg _

end CReal
end Computable
