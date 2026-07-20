/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.InvSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Soundness of the executable square root

Rounds out the verified executable primitive set (`neg`, `add`, `sub`,
`mul`, `exp`, `inv?`, `compare` are already covered) with `sqrt` — the
last non-transcendental primitive, and the one a complex `abs`/`hypot`
needs.

`Ball.sqrt` clamps the lower endpoint to `0`, then encloses the dyadic
interval `[√lo', √hi]` using integer `Nat.sqrt` at the shifted precision.
The two directed dyadic bounds are:

* `Dyadic.sqrt_toRat_le` — `(Dyadic.sqrt d prec).toRat ≤ √(d.toRat)`
  (floor `Nat.sqrt` under-approximates);
* `Dyadic.le_sqrtUp_toRat` — `√(d.toRat) ≤ (Dyadic.sqrtUp d prec).toRat`
  (the `+1` correction over-approximates),

both for `0 ≤ d.man`, proved through the scaling identity
`d.toRat = (d.man · 2^{exp−2·prec}) · (2^prec)²` and the `Nat.sqrt`
bracketing lemmas `Nat.sqrt_le'` / `Nat.lt_succ_sqrt'`.

* `Ball.sqrt_sound` / `FastReal.sqrt_sound` — for a nonnegative enclosed
  real, the executable square root encloses `Real.sqrt`. Unconditional
  (no fuel certificate needed: `sqrt` has no series tail).

`Ball.sqrt`'s internals use the private helpers `divPow2Ceil`/`pow2Int`;
they are reached here only through defeq (`rfl`) against the nameable
mirrors `sqrtValFloor`/`sqrtValCeil`, never by name.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast

namespace Dyadic

private lemma two_r_ne : (2 : ℝ) ≠ 0 := by norm_num

/-- `((v.toNat : ℝ) = (v : ℝ)` for nonnegative `v`. -/
private lemma toNat_cast_real {v : ℤ} (h : 0 ≤ v) : ((v.toNat : ℝ)) = (v : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg h

/-- `toRat` of an explicit dyadic, over `ℝ`. -/
private lemma mk_toRat_real (m p : ℤ) :
    ((Dyadic.toRat ⟨m, p⟩ : ℚ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ p := by
  show (((m : ℚ) * 2 ^ p : ℚ) : ℝ) = _
  push_cast; ring

/-- `Nat.sqrt` under-approximates the real square root. -/
theorem natSqrt_le_rsqrt (v : ℕ) : (Nat.sqrt v : ℝ) ≤ Real.sqrt (v : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have := Nat.sqrt_le' v
  calc ((Nat.sqrt v : ℝ)) ^ 2 = ((Nat.sqrt v ^ 2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (v : ℝ) := by exact_mod_cast this

/-- Scaled radicand `d.man · 2^{exp − 2·prec}`. -/
private noncomputable def Vr (d : Dyadic) (prec : ℤ) : ℝ :=
  (d.man : ℝ) * (2 : ℝ) ^ (d.exp - 2 * prec)

private lemma Vr_nonneg {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) : 0 ≤ Vr d prec := by
  have : (0 : ℝ) ≤ (d.man : ℝ) := by exact_mod_cast hd
  unfold Vr; positivity

/-- `√(d.toRat) = √(Vr) · 2^prec`. -/
private lemma sqrt_toRat_scaled {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    Real.sqrt ((d.toRat : ℚ) : ℝ) = Real.sqrt (Vr d prec) * (2 : ℝ) ^ prec := by
  have hexp : ((2 : ℝ) ^ prec) ^ 2 = (2 : ℝ) ^ (2 * prec) := by
    rw [← zpow_natCast ((2 : ℝ) ^ prec) 2, ← zpow_mul]
    congr 1; push_cast; ring
  have hdval : ((d.toRat : ℚ) : ℝ) = Vr d prec * ((2 : ℝ) ^ prec) ^ 2 := by
    show (((d.man : ℚ) * 2 ^ d.exp : ℚ) : ℝ) = _
    push_cast
    unfold Vr
    rw [hexp, mul_assoc, ← zpow_add₀ two_r_ne,
      show d.exp - 2 * prec + 2 * prec = d.exp from by ring]
  rw [hdval, Real.sqrt_mul (Vr_nonneg hd prec), Real.sqrt_sq (by positivity)]

/-! ### The scaled integer values, as nameable mirrors -/

/-- The floor variant's scaled value (mirrors `Dyadic.sqrt`'s `val`). -/
private def sqrtValFloor (d : Dyadic) (prec : ℤ) : ℤ :=
  let sa := d.exp - 2 * prec
  if 0 ≤ sa then d.man <<< sa.toNat else d.man >>> (-sa).toNat

/-- The ceil variant's scaled value (mirrors `Dyadic.sqrtUp`'s `val`;
`divPow2Ceil`/`pow2Int` inlined by hand). -/
private def sqrtValCeil (d : Dyadic) (prec : ℤ) : ℤ :=
  let sa := d.exp - 2 * prec
  if 0 ≤ sa then d.man <<< sa.toNat
  else if d.man % ((1 : ℤ) <<< (-sa).toNat) == 0 then d.man >>> (-sa).toNat
       else (d.man >>> (-sa).toNat) + 1

/-- `Dyadic.sqrt` in terms of the nameable `sqrtValFloor` (defeq). -/
private lemma sqrt_eq {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    Dyadic.sqrt d prec
      = ⟨(Nat.sqrt (sqrtValFloor d prec).toNat : ℤ), prec⟩ := by
  unfold Dyadic.sqrt sqrtValFloor
  rw [if_neg (not_lt.mpr hd)]

/-- `Dyadic.sqrtUp` in terms of the nameable `sqrtValCeil` (defeq — this is
where the private `divPow2Ceil`/`pow2Int` are reached, by `rfl`). -/
private lemma sqrtUp_eq {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    Dyadic.sqrtUp d prec
      = ⟨((if Nat.sqrt (sqrtValCeil d prec).toNat * Nat.sqrt (sqrtValCeil d prec).toNat
            == (sqrtValCeil d prec).toNat
          then Nat.sqrt (sqrtValCeil d prec).toNat
          else Nat.sqrt (sqrtValCeil d prec).toNat + 1 : ℕ) : ℤ), prec⟩ := by
  unfold Dyadic.sqrtUp sqrtValCeil
  rw [if_neg (not_lt.mpr hd)]
  rfl

/-- The floor value under-approximates `Vr` and is nonnegative. -/
private lemma sqrtValFloor_le {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    ((sqrtValFloor d prec).toNat : ℝ) ≤ Vr d prec ∧ 0 ≤ sqrtValFloor d prec := by
  unfold sqrtValFloor
  by_cases hsh : 0 ≤ d.exp - 2 * prec
  · simp only [hsh, if_true]
    have hval : (d.man <<< (d.exp - 2 * prec).toNat : ℤ)
        = d.man * 2 ^ (d.exp - 2 * prec).toNat := Int.shiftLeft_eq _ _
    have hnn : 0 ≤ (d.man <<< (d.exp - 2 * prec).toNat : ℤ) := by rw [hval]; positivity
    refine ⟨?_, hnn⟩
    rw [toNat_cast_real hnn, hval]
    push_cast
    unfold Vr
    rw [← zpow_natCast (2 : ℝ) (d.exp - 2 * prec).toNat, Int.toNat_of_nonneg hsh]
  · simp only [hsh, if_false]
    push_neg at hsh
    set k : ℕ := (-(d.exp - 2 * prec)).toNat with hk
    have hkcast : (k : ℤ) = -(d.exp - 2 * prec) := Int.toNat_of_nonneg (by omega)
    have hval : (d.man >>> k : ℤ) = d.man / 2 ^ k := by
      rw [Int.shiftRight_eq_div_pow]; norm_cast
    have hnn : 0 ≤ (d.man >>> k : ℤ) := by rw [hval]; positivity
    refine ⟨?_, hnn⟩
    rw [toNat_cast_real hnn, hval]
    have hdenpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hVeq : Vr d prec = (d.man : ℝ) / (2 ^ k : ℝ) := by
      unfold Vr
      have he : d.exp - 2 * prec = -(k : ℤ) := by omega
      rw [he, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hVeq, le_div_iff₀ hdenpos]
    have hmul : (d.man / 2 ^ k : ℤ) * 2 ^ k ≤ d.man := by
      have := Int.ediv_add_emod d.man (2 ^ k)
      have hr : 0 ≤ d.man % 2 ^ k := Int.emod_nonneg _ (by positivity)
      nlinarith [this, hr]
    calc ((d.man / 2 ^ k : ℤ) : ℝ) * (2 ^ k : ℝ)
        = (((d.man / 2 ^ k : ℤ) * 2 ^ k : ℤ) : ℝ) := by push_cast; ring
      _ ≤ (d.man : ℝ) := by exact_mod_cast hmul

/-- The ceil value over-approximates `Vr` and is nonnegative. -/
private lemma le_sqrtValCeil {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    Vr d prec ≤ ((sqrtValCeil d prec).toNat : ℝ) ∧ 0 ≤ sqrtValCeil d prec := by
  unfold sqrtValCeil
  by_cases hsh : 0 ≤ d.exp - 2 * prec
  · simp only [hsh, if_true]
    have hval : (d.man <<< (d.exp - 2 * prec).toNat : ℤ)
        = d.man * 2 ^ (d.exp - 2 * prec).toNat := Int.shiftLeft_eq _ _
    have hnn : 0 ≤ (d.man <<< (d.exp - 2 * prec).toNat : ℤ) := by rw [hval]; positivity
    refine ⟨?_, hnn⟩
    rw [toNat_cast_real hnn, hval]
    push_cast
    unfold Vr
    rw [← zpow_natCast (2 : ℝ) (d.exp - 2 * prec).toNat, Int.toNat_of_nonneg hsh]
  · simp only [hsh, if_false]
    push_neg at hsh
    set k : ℕ := (-(d.exp - 2 * prec)).toNat with hk
    have hkcast : (k : ℤ) = -(d.exp - 2 * prec) := Int.toNat_of_nonneg (by omega)
    have hpow2 : ((1 : ℤ) <<< k) = 2 ^ k := by rw [Int.shiftLeft_eq]; ring
    have hqval : (d.man >>> k : ℤ) = d.man / 2 ^ k := by
      rw [Int.shiftRight_eq_div_pow]; norm_cast
    have hdenpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hVeq : Vr d prec = (d.man : ℝ) / (2 ^ k : ℝ) := by
      unfold Vr
      have he : d.exp - 2 * prec = -(k : ℤ) := by omega
      rw [he, zpow_neg, zpow_natCast, div_eq_mul_inv]
    -- both ceil sub-branches `v` satisfy `d.man ≤ v * 2^k` and `0 ≤ v`
    have hbound : ∀ v : ℤ, 0 ≤ v → d.man ≤ v * 2 ^ k →
        Vr d prec ≤ ((v.toNat : ℝ)) ∧ 0 ≤ v := by
      intro v hv0 hdle
      refine ⟨?_, hv0⟩
      rw [toNat_cast_real hv0, hVeq, div_le_iff₀ hdenpos]
      calc (d.man : ℝ) ≤ ((v * 2 ^ k : ℤ) : ℝ) := by exact_mod_cast hdle
        _ = (v : ℝ) * (2 ^ k : ℝ) := by push_cast; ring
    rw [hpow2]
    split_ifs with hr0
    · have hrz : d.man % 2 ^ k = 0 := by simpa using hr0
      have hq0 : 0 ≤ (d.man >>> k : ℤ) := by rw [hqval]; positivity
      refine hbound _ hq0 ?_
      rw [hqval, Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hrz)]
    · have hq0 : 0 ≤ (d.man >>> k : ℤ) + 1 := by rw [hqval]; positivity
      refine hbound _ hq0 ?_
      rw [hqval]
      have hcomm : (2 ^ k : ℤ) * (d.man / 2 ^ k) = (d.man / 2 ^ k) * 2 ^ k := by ring
      have hdm : (d.man / 2 ^ k) * 2 ^ k + d.man % 2 ^ k = d.man := by
        have := Int.ediv_add_emod d.man (2 ^ k); linarith [hcomm]
      have hrlt : d.man % 2 ^ k < 2 ^ k := Int.emod_lt_of_pos _ (by positivity)
      have hexpand : (d.man / 2 ^ k + 1) * 2 ^ k = (d.man / 2 ^ k) * 2 ^ k + 2 ^ k := by ring
      rw [hexpand]; linarith

/-- **`Dyadic.sqrt` under-approximates the real root.** -/
theorem sqrt_toRat_le {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    ((Dyadic.sqrt d prec).toRat : ℝ) ≤ Real.sqrt ((d.toRat : ℚ) : ℝ) := by
  rw [sqrt_toRat_scaled hd prec, sqrt_eq hd prec, mk_toRat_real]
  have h2p : (0 : ℝ) < (2 : ℝ) ^ prec := zpow_pos (by norm_num) _
  obtain ⟨hle, _⟩ := sqrtValFloor_le hd prec
  have h1 : ((Nat.sqrt (sqrtValFloor d prec).toNat : ℤ) : ℝ) ≤ Real.sqrt (Vr d prec) := by
    calc ((Nat.sqrt (sqrtValFloor d prec).toNat : ℤ) : ℝ)
        = (Nat.sqrt (sqrtValFloor d prec).toNat : ℝ) := by push_cast; ring
      _ ≤ Real.sqrt ((sqrtValFloor d prec).toNat : ℝ) := natSqrt_le_rsqrt _
      _ ≤ Real.sqrt (Vr d prec) := Real.sqrt_le_sqrt hle
  exact mul_le_mul_of_nonneg_right h1 h2p.le

/-- **`Dyadic.sqrtUp` over-approximates the real root.** -/
theorem le_sqrtUp_toRat {d : Dyadic} (hd : 0 ≤ d.man) (prec : ℤ) :
    Real.sqrt ((d.toRat : ℚ) : ℝ) ≤ ((Dyadic.sqrtUp d prec).toRat : ℝ) := by
  rw [sqrt_toRat_scaled hd prec, sqrtUp_eq hd prec, mk_toRat_real]
  have h2p : (0 : ℝ) < (2 : ℝ) ^ prec := zpow_pos (by norm_num) _
  obtain ⟨hge, _⟩ := le_sqrtValCeil hd prec
  set vn : ℕ := (sqrtValCeil d prec).toNat with hvn
  set s : ℕ := Nat.sqrt vn with hs
  set s' : ℕ := if s * s == vn then s else s + 1 with hs'
  -- `vn ≤ (s')²`
  have hvns' : (vn : ℝ) ≤ ((s' : ℝ)) ^ 2 := by
    by_cases hp : s * s == vn
    · have heq : s * s = vn := by simpa using hp
      have : s' = s := by rw [hs']; simp [hp]
      rw [this]
      have hsq : (s : ℝ) ^ 2 = (vn : ℝ) := by
        rw [sq, ← Nat.cast_mul, heq]
      rw [hsq]
    · have hlt : vn < (s + 1) ^ 2 := Nat.lt_succ_sqrt' vn
      have hs'eq : s' = s + 1 := by rw [hs']; simp [hp]
      rw [hs'eq]
      have : (vn : ℝ) < ((s + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt
      push_cast at this ⊢
      linarith
  have h1 : Real.sqrt (Vr d prec) ≤ ((s' : ℤ) : ℝ) := by
    calc Real.sqrt (Vr d prec) ≤ Real.sqrt (vn : ℝ) := Real.sqrt_le_sqrt hge
      _ ≤ Real.sqrt (((s' : ℝ)) ^ 2) := Real.sqrt_le_sqrt hvns'
      _ = ((s' : ℤ) : ℝ) := by rw [Real.sqrt_sq (by positivity)]; push_cast; ring
  exact mul_le_mul_of_nonneg_right h1 h2p.le

end Dyadic

/-! ## Ball and FastReal square roots -/

namespace Ball

/-- **The ball square root is sound** for nonnegative enclosed reals. -/
theorem sqrt_sound {x : Ball} {r : ℝ} (hx : x.Encloses r) (hr : 0 ≤ r)
    (prec : ℤ) : (Ball.sqrt x prec).Encloses (Real.sqrt r) := by
  have hloval : x.lo.toRat = x.mid.toRat - x.rad.toRat := by simp [Ball.lo]
  have hhival : x.hi.toRat = x.mid.toRat + x.rad.toRat := by simp [Ball.hi]
  have hlo : ((x.lo.toRat : ℚ) : ℝ) ≤ r := by rw [hloval]; exact hx.1
  have hhi : r ≤ ((x.hi.toRat : ℚ) : ℝ) := by rw [hhival]; exact hx.2
  have hhi_man : 0 ≤ x.hi.man := by
    by_contra hneg
    push_neg at hneg
    have h1 : x.hi.toRat < 0 := Dyadic.toRat_neg_of_man_neg hneg
    have h2 : ((x.hi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast h1
    linarith
  unfold Ball.sqrt
  rw [if_neg (by simpa using not_lt.mpr hhi_man)]
  set lo' : Dyadic := if x.lo.man < 0 then 0 else x.lo with hlo'
  have hlo'_man : 0 ≤ lo'.man := by
    rw [hlo']; split_ifs with h
    · exact le_refl 0
    · exact not_lt.mp h
  have hlo'_le : ((lo'.toRat : ℚ) : ℝ) ≤ r := by
    rw [hlo']; split_ifs with h
    · show ((Dyadic.toRat ⟨0, 0⟩ : ℚ) : ℝ) ≤ r
      rw [Dyadic.toRat_eq_zero_of_man_eq_zero rfl]; exact_mod_cast hr
    · exact hlo
  apply ofInterval_encloses
  · calc ((Dyadic.sqrt lo' prec).toRat : ℝ)
        ≤ Real.sqrt ((lo'.toRat : ℚ) : ℝ) := Dyadic.sqrt_toRat_le hlo'_man prec
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hlo'_le
  · calc Real.sqrt r
        ≤ Real.sqrt ((x.hi.toRat : ℚ) : ℝ) := Real.sqrt_le_sqrt hhi
      _ ≤ ((Dyadic.sqrtUp x.hi prec).toRat : ℝ) := Dyadic.le_sqrtUp_toRat hhi_man prec

end Ball

namespace FastReal

/-- **The `FastReal` square root is sound** for nonnegative enclosed reals,
at every precision. -/
theorem sqrt_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) (hr : 0 ≤ r) :
    (FastReal.sqrt x).Encloses (Real.sqrt r) := by
  intro n
  exact Ball.sqrt_sound (hx _) hr _

end FastReal

end Computable.Fast
