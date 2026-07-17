/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.GibbsSound

/-!
# Soundness of the partial reciprocal

Discharges the `inv?` half of the remaining obligations: the executable
partial reciprocal really encloses the real reciprocal.

* `Dyadic.toRat_divDown_le` / `Dyadic.le_toRat_divUp` — the directed
  divisions are directed: `divDown a b prec ≤ a/b ≤ divUp a b prec`,
  through the `scaledNumDen`/`normalizeDivisor` plumbing;
* `Ball.inv?_sound` — a `some` answer of the ball reciprocal encloses
  `r⁻¹` for every enclosed `r` (both sign branches; monotonicity of
  inversion on each side of `0`);
* `FastReal.inv?_sound` — the `FastReal` wrapper is sound at every
  precision;
* `logistic?_sound` — the executable logistic is sound *conditional only
  on `exp` enclosure*: with `hexp : (FastReal.exp (-x)).Encloses
  (Real.exp (-xR))`, every ball emitted by `logistic? x` encloses the true
  logistic probability `(1 + Real.exp (-xR))⁻¹`. Combined with
  `GibbsSound.gibbsSiteUpdate?_sound`, the entire Gibbs layer is now
  theorem-grade modulo the single remaining obligation: enclosure for the
  Taylor-series `FastReal.exp`.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastLogistic

namespace Computable.Fast

namespace Dyadic

private lemma two_q_ne : (2 : ℚ) ≠ 0 := by norm_num

/-- Sign transfer: positive mantissa, positive value. -/
theorem toRat_pos_of_man_pos {d : Dyadic} (h : 0 < d.man) : 0 < d.toRat :=
  mul_pos (by exact_mod_cast h) (zpow_pos (by norm_num) _)

/-- Sign transfer: negative mantissa, negative value. -/
theorem toRat_neg_of_man_neg {d : Dyadic} (h : d.man < 0) : d.toRat < 0 :=
  mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos (by norm_num) _)

theorem man_ne_zero_of_toRat_neg {d : Dyadic} (h : d.toRat < 0) : d.man ≠ 0 :=
  fun h0 => absurd (toRat_eq_zero_of_man_eq_zero h0) h.ne

theorem man_ne_zero_of_toRat_pos {d : Dyadic} (h : 0 < d.toRat) : d.man ≠ 0 :=
  fun h0 => absurd (toRat_eq_zero_of_man_eq_zero h0) h.ne'

theorem toRat_ne_zero_of_man_ne_zero {d : Dyadic} (h : d.man ≠ 0) : d.toRat ≠ 0 :=
  mul_ne_zero (by exact_mod_cast h) (zpow_ne_zero _ two_q_ne)

/-- Cross-multiplied specification of `scaledNumDen`:
`num * 2^prec * b = a * den` as rationals. -/
private lemma scaled_cross (a b : Dyadic) (prec : ℤ) :
    ((Dyadic.scaledNumDen a b prec).1 : ℚ) * 2 ^ prec * b.toRat
      = a.toRat * ((Dyadic.scaledNumDen a b prec).2 : ℚ) := by
  unfold Dyadic.scaledNumDen
  by_cases hcond : a.exp - b.exp - prec ≥ 0
  · simp only [if_pos hcond]
    have hs : (((a.exp - b.exp - prec).toNat : ℤ)) = a.exp - b.exp - prec :=
      Int.toNat_of_nonneg hcond
    show ((a.man <<< (a.exp - b.exp - prec).toNat : ℤ) : ℚ) * 2 ^ prec
        * ((b.man : ℚ) * 2 ^ b.exp) = ((a.man : ℚ) * 2 ^ a.exp) * (b.man : ℚ)
    rw [Int.shiftLeft_eq]
    push_cast
    have hpow : (2 : ℚ) ^ ((a.exp - b.exp - prec).toNat : ℕ) * 2 ^ prec * 2 ^ b.exp
        = 2 ^ a.exp := by
      rw [← zpow_natCast (2 : ℚ), ← zpow_add₀ two_q_ne, ← zpow_add₀ two_q_ne]
      congr 1
      omega
    linear_combination ((a.man : ℚ) * (b.man : ℚ)) * hpow
  · simp only [if_neg hcond]
    have hs : (((-(a.exp - b.exp - prec)).toNat : ℤ)) = -(a.exp - b.exp - prec) :=
      Int.toNat_of_nonneg (by omega)
    show ((a.man : ℚ)) * 2 ^ prec * ((b.man : ℚ) * 2 ^ b.exp)
        = ((a.man : ℚ) * 2 ^ a.exp)
          * ((b.man <<< (-(a.exp - b.exp - prec)).toNat : ℤ) : ℚ)
    rw [Int.shiftLeft_eq]
    push_cast
    have hpow : (2 : ℚ) ^ prec * 2 ^ b.exp
        = 2 ^ a.exp * 2 ^ ((-(a.exp - b.exp - prec)).toNat : ℕ) := by
      rw [← zpow_natCast (2 : ℚ) ((-(a.exp - b.exp - prec)).toNat),
        ← zpow_add₀ two_q_ne, ← zpow_add₀ two_q_ne]
      congr 1
      omega
    linear_combination ((a.man : ℚ) * (b.man : ℚ)) * hpow

/-- The normalized pair keeps the cross identity and has positive
denominator (given `b.man ≠ 0`). -/
private lemma norm_spec (a b : Dyadic) (prec : ℤ) (hb : b.man ≠ 0)
    {num0 den0 num den : ℤ}
    (h1 : Dyadic.scaledNumDen a b prec = (num0, den0))
    (h2 : Dyadic.normalizeDivisor num0 den0 = (num, den)) :
    (num : ℚ) * 2 ^ prec * b.toRat = a.toRat * (den : ℚ) ∧ 0 < den := by
  have hcross0 := scaled_cross a b prec
  rw [h1] at hcross0
  have hcross : (num0 : ℚ) * 2 ^ prec * b.toRat = a.toRat * (den0 : ℚ) := hcross0
  have hden0' : (Dyadic.scaledNumDen a b prec).2 ≠ 0 := by
    by_cases hcond : a.exp - b.exp - prec ≥ 0
    · simp only [Dyadic.scaledNumDen, if_pos hcond]
      exact hb
    · simp only [Dyadic.scaledNumDen, if_neg hcond]
      show b.man <<< _ ≠ 0
      rw [Int.shiftLeft_eq]
      exact mul_ne_zero hb (pow_ne_zero _ (by norm_num))
  rw [h1] at hden0'
  have hden0 : den0 ≠ 0 := hden0'
  unfold Dyadic.normalizeDivisor at h2
  split_ifs at h2 with hneg
  · injection h2 with hnum hden
    refine ⟨?_, by omega⟩
    rw [← hnum, ← hden]
    push_cast
    linear_combination -hcross
  · injection h2 with hnum hden
    refine ⟨?_, by omega⟩
    rw [← hnum, ← hden]
    exact hcross

/-- **`divDown` rounds down**: `divDown a b prec ≤ a / b` (as rationals),
for any nonzero divisor. -/
theorem toRat_divDown_le (a b : Dyadic) (prec : ℤ) (hb : b.man ≠ 0) :
    (Dyadic.divDown a b prec).toRat ≤ a.toRat / b.toRat := by
  have hbq : b.toRat ≠ 0 := toRat_ne_zero_of_man_ne_zero hb
  unfold Dyadic.divDown
  rw [if_neg (by simpa using hb)]
  rcases hsc : Dyadic.scaledNumDen a b prec with ⟨num0, den0⟩
  rcases hnorm : Dyadic.normalizeDivisor num0 den0 with ⟨num, den⟩
  obtain ⟨hcross, hden⟩ := norm_spec a b prec hb hsc hnorm
  have hdenq : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  -- the true ratio in scaled form
  have hratio : a.toRat / b.toRat = ((num : ℚ) * 2 ^ prec) / (den : ℚ) := by
    rw [div_eq_div_iff hbq hdenq.ne']
    linear_combination -hcross
  -- floor bound
  have hfloor : ((num / den : ℤ) : ℚ) ≤ (num : ℚ) / (den : ℚ) := by
    rw [le_div_iff₀ hdenq]
    have h1 : num / den * den ≤ num := by
      have h2 := Int.mul_ediv_add_emod num den
      have h3 : 0 ≤ num % den := Int.emod_nonneg num hden.ne'
      linarith [mul_comm (num / den) den]
    exact_mod_cast h1
  dsimp only
  rw [hnorm]
  show ((num / den : ℤ) : ℚ) * 2 ^ prec ≤ a.toRat / b.toRat
  rw [hratio]
  calc ((num / den : ℤ) : ℚ) * 2 ^ prec
      ≤ ((num : ℚ) / (den : ℚ)) * 2 ^ prec :=
        mul_le_mul_of_nonneg_right hfloor (zpow_pos (by norm_num) prec).le
    _ = (num : ℚ) * 2 ^ prec / (den : ℚ) := by ring

/-- **`divUp` rounds up**: `a / b ≤ divUp a b prec` (as rationals), for any
nonzero divisor. -/
theorem le_toRat_divUp (a b : Dyadic) (prec : ℤ) (hb : b.man ≠ 0) :
    a.toRat / b.toRat ≤ (Dyadic.divUp a b prec).toRat := by
  have hbq : b.toRat ≠ 0 := toRat_ne_zero_of_man_ne_zero hb
  unfold Dyadic.divUp
  rw [if_neg (by simpa using hb)]
  rcases hsc : Dyadic.scaledNumDen a b prec with ⟨num0, den0⟩
  rcases hnorm : Dyadic.normalizeDivisor num0 den0 with ⟨num, den⟩
  obtain ⟨hcross, hden⟩ := norm_spec a b prec hb hsc hnorm
  have hdenq : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  have hratio : a.toRat / b.toRat = ((num : ℚ) * 2 ^ prec) / (den : ℚ) := by
    rw [div_eq_div_iff hbq hdenq.ne']
    linear_combination -hcross
  have hup : ∀ q' : ℤ, (num : ℚ) / (den : ℚ) ≤ (q' : ℚ) →
      a.toRat / b.toRat ≤ Dyadic.toRat ⟨q', prec⟩ := by
    intro q' hq
    show a.toRat / b.toRat ≤ (q' : ℚ) * 2 ^ prec
    rw [hratio]
    calc (num : ℚ) * 2 ^ prec / (den : ℚ)
        = ((num : ℚ) / (den : ℚ)) * 2 ^ prec := by ring
      _ ≤ (q' : ℚ) * 2 ^ prec :=
          mul_le_mul_of_nonneg_right hq (zpow_pos (by norm_num) prec).le
  dsimp only
  rw [hnorm]
  split_ifs with hr
  · -- exact division
    have hr0 : num % den = 0 := by simpa using hr
    apply hup
    rw [div_le_iff₀ hdenq]
    have h1 : num ≤ num / den * den := by
      have h2 := Int.mul_ediv_add_emod num den
      linarith [mul_comm (num / den) den]
    exact_mod_cast h1
  · apply hup
    rw [div_le_iff₀ hdenq]
    have h1 : num ≤ (num / den + 1) * den := by
      have h2 := Int.mul_ediv_add_emod num den
      have h3 : num % den < den := Int.emod_lt_of_pos num hden
      have h4 : (num / den + 1) * den = den * (num / den) + den := by ring
      linarith
    exact_mod_cast h1

end Dyadic

/-! ## Ball and FastReal reciprocals -/

namespace Ball

private lemma one_div_anti_neg {a b : ℝ} (hab : a ≤ b) (hb : b < 0) :
    1 / b ≤ 1 / a := by
  have ha : a < 0 := hab.trans_lt hb
  have hab0 : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have heq : 1 / b - 1 / a = (a - b) / (a * b) := by
    field_simp [ha.ne, hb.ne]
  have h1 : (a - b) / (a * b) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨sub_nonpos.mpr hab, hab0.le⟩)
  linarith [heq ▸ h1]

/-- **The ball reciprocal is sound**: a `some` answer encloses `r⁻¹` for
every enclosed `r`. -/
theorem inv?_sound {x : Ball} {r : ℝ} (hx : x.Encloses r) {prec : ℤ} {b : Ball}
    (h : Ball.inv? x prec = some b) : b.Encloses r⁻¹ := by
  have hloval : x.lo.toRat = x.mid.toRat - x.rad.toRat := by simp [Ball.lo]
  have hhival : x.hi.toRat = x.mid.toRat + x.rad.toRat := by simp [Ball.hi]
  have hlo : ((x.lo.toRat : ℚ) : ℝ) ≤ r := by rw [hloval]; exact hx.1
  have hhi : r ≤ ((x.hi.toRat : ℚ) : ℝ) := by rw [hhival]; exact hx.2
  simp only [Ball.inv?] at h
  split_ifs at h with h1 h2
  · -- entirely negative: lo ≤ r ≤ hi < 0, so 1/hi ≤ 1/r ≤ 1/lo
    injection h with h; subst h
    have hhiq : x.hi.toRat < 0 := Dyadic.toRat_neg_of_man_neg h1
    have hhiR : ((x.hi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hhiq
    have hr0 : r < 0 := lt_of_le_of_lt hhi hhiR
    have hloq : x.lo.toRat < 0 := by
      have hloR : ((x.lo.toRat : ℚ) : ℝ) < 0 := lt_of_le_of_lt hlo hr0
      exact_mod_cast hloR
    have hhiman : x.hi.man ≠ 0 := Dyadic.man_ne_zero_of_toRat_neg hhiq
    have hloman : x.lo.man ≠ 0 := Dyadic.man_ne_zero_of_toRat_neg hloq
    apply ofInterval_encloses
    · -- divDown 1 hi ≤ 1/hi ≤ 1/r = r⁻¹
      have hd : (Dyadic.divDown 1 x.hi prec).toRat ≤ (1 : ℚ) / x.hi.toRat := by
        simpa using Dyadic.toRat_divDown_le 1 x.hi prec hhiman
      calc ((Dyadic.divDown 1 x.hi prec).toRat : ℝ)
          ≤ (((1 : ℚ) / x.hi.toRat : ℚ) : ℝ) := by exact_mod_cast hd
        _ = 1 / ((x.hi.toRat : ℚ) : ℝ) := by push_cast; ring
        _ ≤ 1 / r := one_div_anti_neg hhi hhiR
        _ = r⁻¹ := one_div r
    · -- r⁻¹ = 1/r ≤ 1/lo ≤ divUp 1 lo
      have hd : (1 : ℚ) / x.lo.toRat ≤ (Dyadic.divUp 1 x.lo prec).toRat := by
        simpa using Dyadic.le_toRat_divUp 1 x.lo prec hloman
      calc r⁻¹ = 1 / r := (one_div r).symm
        _ ≤ 1 / ((x.lo.toRat : ℚ) : ℝ) := one_div_anti_neg hlo hr0
        _ = (((1 : ℚ) / x.lo.toRat : ℚ) : ℝ) := by push_cast; ring
        _ ≤ ((Dyadic.divUp 1 x.lo prec).toRat : ℝ) := by exact_mod_cast hd
  · -- entirely positive: 0 < lo ≤ r ≤ hi, so 1/hi ≤ 1/r ≤ 1/lo
    injection h with h; subst h
    have hloq : 0 < x.lo.toRat := Dyadic.toRat_pos_of_man_pos h2
    have hloR : (0 : ℝ) < ((x.lo.toRat : ℚ) : ℝ) := by exact_mod_cast hloq
    have hr0 : 0 < r := lt_of_lt_of_le hloR hlo
    have hhiq : 0 < x.hi.toRat := by
      have hhiR : (0 : ℝ) < ((x.hi.toRat : ℚ) : ℝ) := lt_of_lt_of_le hr0 hhi
      exact_mod_cast hhiR
    have hhiman : x.hi.man ≠ 0 := Dyadic.man_ne_zero_of_toRat_pos hhiq
    have hloman : x.lo.man ≠ 0 := Dyadic.man_ne_zero_of_toRat_pos hloq
    apply ofInterval_encloses
    · have hd : (Dyadic.divDown 1 x.hi prec).toRat ≤ (1 : ℚ) / x.hi.toRat := by
        simpa using Dyadic.toRat_divDown_le 1 x.hi prec hhiman
      calc ((Dyadic.divDown 1 x.hi prec).toRat : ℝ)
          ≤ (((1 : ℚ) / x.hi.toRat : ℚ) : ℝ) := by exact_mod_cast hd
        _ = 1 / ((x.hi.toRat : ℚ) : ℝ) := by push_cast; ring
        _ ≤ 1 / r := one_div_le_one_div_of_le hr0 hhi
        _ = r⁻¹ := one_div r
    · have hd : (1 : ℚ) / x.lo.toRat ≤ (Dyadic.divUp 1 x.lo prec).toRat := by
        simpa using Dyadic.le_toRat_divUp 1 x.lo prec hloman
      calc r⁻¹ = 1 / r := (one_div r).symm
        _ ≤ 1 / ((x.lo.toRat : ℚ) : ℝ) := one_div_le_one_div_of_le hloR hlo
        _ = (((1 : ℚ) / x.lo.toRat : ℚ) : ℝ) := by push_cast; ring
        _ ≤ ((Dyadic.divUp 1 x.lo prec).toRat : ℝ) := by exact_mod_cast hd

end Ball

namespace FastReal

/-- The `FastReal` partial reciprocal is sound at every precision. -/
theorem inv?_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) :
    ∀ (n : ℕ) {b : Ball}, FastReal.inv? x n = some b → b.Encloses r⁻¹ := by
  intro n b h
  exact Ball.inv?_sound (hx _) h

end FastReal

/-! ## The logistic, modulo `exp` -/

namespace FastLogistic

/-- **Conditional soundness of the executable logistic**: given enclosure
for the exponential (the single remaining obligation of the refinement
program), every ball emitted by `logistic? x` encloses the true logistic
probability `(1 + exp (-xR))⁻¹ = logisticProb xR`. Plugged into
`decideBernoulli?_sound`/`gibbsSiteUpdate?_sound`, this makes the whole
Gibbs layer theorem-grade modulo `exp`. -/
theorem logistic?_sound {x : FastReal} {xR : ℝ}
    (hexp : (FastReal.exp (-x)).Encloses (Real.exp (-xR))) :
    ∀ (i : ℕ) {b : Ball}, logistic? x i = some b →
      b.Encloses (1 + Real.exp (-xR))⁻¹ := by
  intro i b h
  have hden : (logisticDenom x).Encloses (1 + Real.exp (-xR)) :=
    FastReal.add_encloses FastReal.encloses_one hexp
  exact FastReal.inv?_sound hden i h

end FastLogistic

end Computable.Fast
