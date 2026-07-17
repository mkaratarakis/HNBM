/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.InvSound
import HopfieldNet.CReals.Computable.EnergySound
import Mathlib.Analysis.Complex.Exponential

/-!
# Soundness of the executable exponential

The last obligation of the refinement program. `Ball.exp` scales its
argument down by `2^k` so that `|x_small| ≤ 1/2`, runs a fueled Taylor
loop that exits when the current term drops below tolerance (adding a
geometric tail bound `2·|term|` to the radius), and squares the result
`k` times. This file proves the computation **sound**, conditional on one
runtime-checkable certificate:

* the fuel-exhaustion branch of the Taylor loop returns the bare partial
  sum *without* a remainder bound, so unconditional enclosure is not a
  theorem of this implementation. `Ball.expExits` mirrors the loop and
  returns `true` exactly when it exits through the tolerance branch — a
  decidable, executable certificate in the spirit of every other
  certificate in this development;
* `Ball.exp_sound` — if `expExits x prec = true` and `x` encloses `r`,
  then `Ball.exp x prec` encloses `Real.exp r`. The Taylor invariant is
  `term ∋ s^i/i!` and `sum ∋ ∑_{m ≤ i} s^m/m!`; the tail is justified by
  `Real.exp_bound` together with `|s| ≤ 1/2` (proved from `absUpper` and
  `Nat.log2` magnitude arithmetic); the squaring phase is
  `exp s ^ 2^k = exp r`;
* `FastReal.exp_sound` — the pointwise wrapper, under `FastReal.ExpExits`;
* `logistic?_sound_of_expExits` — **the stochastic layer closes**: with
  the `ExpExits` certificate, the executable logistic encloses the true
  Gibbs probability, and via `GibbsSound` the executable sampler provably
  samples the true Bernoulli distribution. No unproved obligations remain.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastLogistic

set_option maxRecDepth 8192

namespace Computable.Fast

/-! ## Primitive soundness -/

namespace Ball

theorem one_encloses : Ball.one.Encloses 1 := by
  constructor <;> norm_num [Ball.one, Dyadic.toRat]

private lemma abs_man_nonneg (d : Dyadic) : 0 ≤ (Dyadic.abs d).man :=
  Int.natCast_nonneg _

/-- `absUpper` bounds the absolute value of every enclosed real. -/
theorem absUpper_sound {b : Ball} {t : ℝ} (h : b.Encloses t) :
    |t| ≤ ((b.absUpper.toRat : ℚ) : ℝ) := by
  have hloval : b.lo.toRat = b.mid.toRat - b.rad.toRat := by simp [Ball.lo]
  have hhival : b.hi.toRat = b.mid.toRat + b.rad.toRat := by simp [Ball.hi]
  have hlo : ((b.lo.toRat : ℚ) : ℝ) ≤ t := by rw [hloval]; exact h.1
  have hhi : t ≤ ((b.hi.toRat : ℚ) : ℝ) := by rw [hhival]; exact h.2
  have hlo_abs : (b.lo.abs).toRat = |b.lo.toRat| := Dyadic.toRat_abs _
  have hhi_abs : (b.hi.abs).toRat = |b.hi.toRat| := Dyadic.toRat_abs _
  have hboth : ∀ M : Dyadic, |b.lo.toRat| ≤ M.toRat → |b.hi.toRat| ≤ M.toRat →
      |t| ≤ ((M.toRat : ℚ) : ℝ) := by
    intro M h1 h2
    rw [abs_le]
    constructor
    · have ha : -((|b.lo.toRat| : ℚ) : ℝ) ≤ ((b.lo.toRat : ℚ) : ℝ) := by
        exact_mod_cast neg_abs_le (b.lo.toRat : ℚ)
      have hb : ((|b.lo.toRat| : ℚ) : ℝ) ≤ ((M.toRat : ℚ) : ℝ) := by exact_mod_cast h1
      linarith
    · have ha : ((b.hi.toRat : ℚ) : ℝ) ≤ ((|b.hi.toRat| : ℚ) : ℝ) := by
        exact_mod_cast le_abs_self (b.hi.toRat : ℚ)
      have hb : ((|b.hi.toRat| : ℚ) : ℝ) ≤ ((M.toRat : ℚ) : ℝ) := by exact_mod_cast h2
      linarith
  show |t| ≤ (((if b.lo.abs < b.hi.abs then b.hi.abs else b.lo.abs).toRat : ℚ) : ℝ)
  split_ifs with hc
  · have hle : |b.lo.toRat| ≤ |b.hi.toRat| := by
      have := Dyadic.toRat_lt_iff.mp hc
      rw [hlo_abs, hhi_abs] at this
      exact this.le
    exact hboth _ (hhi_abs ▸ hle) (le_of_eq hhi_abs.symm)
  · have hle : |b.hi.toRat| ≤ |b.lo.toRat| := by
      have h1 : ¬ (b.lo.abs).toRat < (b.hi.abs).toRat :=
        fun hlt => hc (Dyadic.toRat_lt_iff.mpr hlt)
      rw [hlo_abs, hhi_abs] at h1
      exact not_lt.mp h1
    exact hboth _ (le_of_eq hlo_abs.symm) (hlo_abs ▸ hle)

/-- Scaling by a power of two is exact. -/
theorem scale2_encloses {b : Ball} {r : ℝ} (h : b.Encloses r) (k : ℤ) :
    (b.scale2 k).Encloses (r * (2 : ℝ) ^ k) := by
  rw [encloses_iff_abs] at h ⊢
  have hmid : (b.scale2 k).mid = b.mid.shiftl k := rfl
  have hrad : (b.scale2 k).rad = b.rad.shiftl k := rfl
  rw [hmid, hrad, Dyadic.toRat_shiftl, Dyadic.toRat_shiftl]
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hcast : ∀ q : ℚ, ((q * 2 ^ k : ℚ) : ℝ) = (q : ℝ) * (2 : ℝ) ^ k := by
    intro q; push_cast; ring
  rw [hcast, hcast]
  have h1 : r * (2 : ℝ) ^ k - (b.mid.toRat : ℝ) * (2 : ℝ) ^ k
      = (r - (b.mid.toRat : ℝ)) * (2 : ℝ) ^ k := by ring
  rw [h1, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_right h hp.le

/-- The `getD zero` composition of the exact-dyadic reciprocal is sound
for nonzero mantissa. -/
theorem invDyadicGetD_sound {d : Dyadic} (hd : d.man ≠ 0) (prec : ℤ) :
    ((Ball.invDyadic? d prec).getD Ball.zero).Encloses
      (((d.toRat : ℚ) : ℝ))⁻¹ := by
  unfold Ball.invDyadic?
  rw [if_neg (by simpa using hd)]
  simp only [Option.getD_some]
  apply ofInterval_encloses
  · have h1 : (Dyadic.divDown 1 d prec).toRat ≤ (1 : ℚ) / d.toRat := by
      simpa using Dyadic.toRat_divDown_le 1 d prec hd
    calc ((Dyadic.divDown 1 d prec).toRat : ℝ)
        ≤ (((1 : ℚ) / d.toRat : ℚ) : ℝ) := by exact_mod_cast h1
      _ = ((d.toRat : ℚ) : ℝ)⁻¹ := by push_cast; rw [one_div]
  · have h1 : (1 : ℚ) / d.toRat ≤ (Dyadic.divUp 1 d prec).toRat := by
      simpa using Dyadic.le_toRat_divUp 1 d prec hd
    calc ((d.toRat : ℚ) : ℝ)⁻¹
        = (((1 : ℚ) / d.toRat : ℚ) : ℝ) := by push_cast; rw [one_div]
      _ ≤ ((Dyadic.divUp 1 d prec).toRat : ℝ) := by exact_mod_cast h1

end Ball

namespace ExpSound

/-! ## The scaled argument is small -/

/-- Mirror of the magnitude estimate in `Ball.exp`. -/
def expMag (x : Ball) : ℤ :=
  x.absUpper.exp +
    ((if x.absUpper.man = 0 then 0 else x.absUpper.man.natAbs.log2 : ℕ) : ℤ)

/-- Mirror of the scaling exponent in `Ball.exp`. -/
def expK (x : Ball) : ℤ := if expMag x > -2 then expMag x + 2 else 0

theorem expK_nonneg (x : Ball) : 0 ≤ expK x := by
  unfold expK
  split_ifs <;> omega

/-- The scaled argument is at most `1/2` in absolute value. -/
theorem abs_scaled_le_half {x : Ball} {r : ℝ} (hx : x.Encloses r) :
    |r * (2 : ℝ) ^ (-(expK x))| ≤ 1 / 2 := by
  have hU := Ball.absUpper_sound hx
  have hp : (0 : ℝ) < (2 : ℝ) ^ (-(expK x)) := zpow_pos (by norm_num) _
  rw [abs_mul, abs_of_pos hp]
  by_cases h0 : x.absUpper.man = 0
  · have hz : x.absUpper.toRat = 0 := Dyadic.toRat_eq_zero_of_man_eq_zero h0
    rw [hz] at hU
    have hr : |r| = 0 := le_antisymm (by exact_mod_cast hU) (abs_nonneg r)
    rw [hr, zero_mul]
    norm_num
  · -- `U < 2^(mag+1)` from the log2 magnitude estimate
    have hman_nonneg : 0 ≤ x.absUpper.man := by
      show 0 ≤ (if x.lo.abs < x.hi.abs then x.hi.abs else x.lo.abs).man
      split_ifs
      · exact Ball.abs_man_nonneg _
      · exact Ball.abs_man_nonneg _
    have hnat0 : x.absUpper.man.natAbs ≠ 0 := by
      simpa [Int.natAbs_eq_zero] using h0
    have hman_lt : x.absUpper.man.natAbs < 2 ^ (x.absUpper.man.natAbs.log2 + 1) :=
      (Nat.log2_lt hnat0).mp (Nat.lt_succ_self _)
    set l : ℕ := x.absUpper.man.natAbs.log2 with hl
    have hmanR : (x.absUpper.man : ℝ) < (2 : ℝ) ^ (l + 1 : ℕ) := by
      have h1 : (x.absUpper.man.natAbs : ℝ) < (2 : ℝ) ^ (l + 1 : ℕ) := by
        exact_mod_cast hman_lt
      have h2 : ((x.absUpper.man.natAbs : ℤ) : ℝ) = (x.absUpper.man : ℝ) := by
        rw [Int.natAbs_of_nonneg hman_nonneg]
      rw [← h2]
      exact_mod_cast h1
    have hUval : ((x.absUpper.toRat : ℚ) : ℝ)
        = (x.absUpper.man : ℝ) * (2 : ℝ) ^ x.absUpper.exp := by
      show (((x.absUpper.man : ℚ) * 2 ^ x.absUpper.exp : ℚ) : ℝ) = _
      push_cast
      ring
    have hmag : expMag x = x.absUpper.exp + (l : ℤ) := by
      unfold expMag
      rw [if_neg h0]
    have hUlt : ((x.absUpper.toRat : ℚ) : ℝ) < (2 : ℝ) ^ (expMag x + 1) := by
      rw [hUval, hmag]
      calc (x.absUpper.man : ℝ) * (2 : ℝ) ^ x.absUpper.exp
          < (2 : ℝ) ^ (l + 1 : ℕ) * (2 : ℝ) ^ x.absUpper.exp :=
            mul_lt_mul_of_pos_right hmanR (zpow_pos (by norm_num) _)
        _ = (2 : ℝ) ^ (x.absUpper.exp + (l : ℤ) + 1) := by
            rw [← zpow_natCast (2 : ℝ) (l + 1), ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
              show ((l + 1 : ℕ) : ℤ) + x.absUpper.exp = x.absUpper.exp + (l : ℤ) + 1
                from by omega]
    have habs : |r| < (2 : ℝ) ^ (expMag x + 1) := lt_of_le_of_lt hU hUlt
    calc |r| * (2 : ℝ) ^ (-(expK x))
        ≤ (2 : ℝ) ^ (expMag x + 1) * (2 : ℝ) ^ (-(expK x)) :=
          mul_le_mul_of_nonneg_right habs.le hp.le
      _ = (2 : ℝ) ^ (expMag x + 1 - expK x) := by
          rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
          congr 1
      _ ≤ (2 : ℝ) ^ (-1 : ℤ) := by
          apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
          unfold expK
          split_ifs with hcase <;> omega
      _ = 1 / 2 := by norm_num

/-! ## The Taylor loop -/

/-- The (private-`divDyadic`-inlined) step of the Taylor loop: it is
definitionally the `term'` computed inside `Ball.exp.taylor`. -/
def taylorStep (prec : ℤ) (xs term : Ball) (i : ℕ) : Ball :=
  Ball.mul (Ball.mul term xs prec)
    ((Ball.invDyadic? ⟨((i + 1 : ℕ) : ℤ), 0⟩ prec).getD Ball.zero) prec

/-- Executable mirror of the Taylor loop's control flow: `true` iff the
loop exits through the tolerance branch within fuel. -/
def taylorExits (prec : ℤ) (xs : Ball) (tol : Dyadic) :
    ℕ → Ball → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, term, i =>
    if (taylorStep prec xs term i).absUpper < tol then true
    else taylorExits prec xs tol fuel (taylorStep prec xs term i) (i + 1)

/-- One Taylor step encloses the next true term. -/
theorem taylorStep_encloses {xs term : Ball} {s t : ℝ} (prec : ℤ)
    (hxs : xs.Encloses s) (hterm : term.Encloses t) (i : ℕ) :
    (taylorStep prec xs term i).Encloses (t * s / ((i : ℝ) + 1)) := by
  unfold taylorStep
  have hmul := Ball.mul_encloses prec hterm hxs
  have hd : ((⟨((i + 1 : ℕ) : ℤ), 0⟩ : Dyadic)).man ≠ 0 := by
    show ((i + 1 : ℕ) : ℤ) ≠ 0
    omega
  have hinv := Ball.invDyadicGetD_sound hd prec
  have h := Ball.mul_encloses prec hmul hinv
  have hval : ((Dyadic.toRat ⟨((i + 1 : ℕ) : ℤ), 0⟩ : ℚ) : ℝ) = (i : ℝ) + 1 := by
    show (((((i + 1 : ℕ) : ℤ) : ℚ) * 2 ^ (0 : ℤ) : ℚ) : ℝ) = _
    push_cast
    ring
  rw [hval] at h
  rwa [div_eq_mul_inv]

/-- The padded partial sum encloses `exp s`: adding the geometric tail
`2·|term'|` to the radius covers the whole remainder of the series (via
`Real.exp_bound` and `|s| ≤ 1/2`). Shared by the tolerance exit of
`Ball.exp` and by both exits of the verified variant `expV`. -/
theorem pad_sound (prec : ℤ) {s : ℝ} (hs : |s| ≤ 1 / 2) {T' S' : Ball} {i : ℕ}
    (hstep : T'.Encloses (s ^ (i + 1) / ((i + 1).factorial : ℝ)))
    (hsum' : S'.Encloses (∑ m ∈ Finset.range (i + 2), s ^ m / (m.factorial : ℝ))) :
    (({ mid := S'.mid,
        rad := (S'.rad + (T'.absUpper * ⟨2, 0⟩).roundUp prec).roundUp prec } : Ball)).Encloses
      (Real.exp s) := by
  rw [Ball.encloses_iff_abs]
  show |Real.exp s - (S'.mid.toRat : ℝ)| ≤
    ((((S'.rad + (T'.absUpper * ⟨2, 0⟩).roundUp prec).roundUp prec).toRat : ℚ) : ℝ)
  set P : ℝ := ∑ m ∈ Finset.range (i + 2), s ^ m / (m.factorial : ℝ) with hP
  have hmid : |P - (S'.mid.toRat : ℝ)| ≤ (S'.rad.toRat : ℝ) :=
    Ball.encloses_iff_abs.mp hsum'
  set U : ℝ := ((T'.absUpper.toRat : ℚ) : ℝ) with hU_def
  have hUb : |s ^ (i + 1) / ((i + 1).factorial : ℝ)| ≤ U :=
    Ball.absUpper_sound hstep
  have hU0 : (0 : ℝ) ≤ U := le_trans (abs_nonneg _) hUb
  have hrem : |Real.exp s - P| ≤ U := by
    have hs1 : |s| ≤ 1 := hs.trans (by norm_num)
    have hb := Real.exp_bound (x := s) hs1 (n := i + 2) (by omega)
    push_cast at hb
    have hb' : |Real.exp s - P| ≤ |s| ^ (i + 2) *
        (((i : ℝ) + 3) / (((i + 2).factorial : ℝ) * ((i : ℝ) + 2))) := by
      have h3 : ((i : ℝ) + 3) = (i : ℝ) + 2 + 1 := by ring
      rw [h3]
      exact hb
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hfact_pos : (0 : ℝ) < ((i + 1).factorial : ℝ) := by
      exact_mod_cast (i + 1).factorial_pos
    have hfact_succ : ((i + 2).factorial : ℝ)
        = ((i : ℝ) + 2) * ((i + 1).factorial : ℝ) := by
      have h1 : (i + 2).factorial = (i + 2) * (i + 1).factorial :=
        Nat.factorial_succ (i + 1)
      rw [h1]
      push_cast
      ring
    have hkey : |s| * ((i : ℝ) + 3) ≤ ((i : ℝ) + 2) * ((i : ℝ) + 2) := by
      have h1 : |s| * ((i : ℝ) + 3) ≤ (1 / 2) * ((i : ℝ) + 3) :=
        mul_le_mul_of_nonneg_right hs (by linarith)
      nlinarith
    have hcore : |s| * (((i : ℝ) + 3) /
        (((i + 2).factorial : ℝ) * ((i : ℝ) + 2)))
        ≤ 1 / ((i + 1).factorial : ℝ) := by
      rw [hfact_succ]
      rw [show |s| * (((i : ℝ) + 3) /
          ((((i : ℝ) + 2) * ((i + 1).factorial : ℝ)) * ((i : ℝ) + 2)))
          = (|s| * ((i : ℝ) + 3)) /
            ((((i : ℝ) + 2) * ((i + 1).factorial : ℝ)) * ((i : ℝ) + 2))
        from by ring]
      rw [div_le_div_iff₀ (by positivity) hfact_pos]
      nlinarith [mul_le_mul_of_nonneg_right hkey hfact_pos.le]
    have harith : |s| ^ (i + 2) *
        (((i : ℝ) + 3) / (((i + 2).factorial : ℝ) * ((i : ℝ) + 2)))
        ≤ |s| ^ (i + 1) / ((i + 1).factorial : ℝ) := by
      have hA : (0 : ℝ) ≤ |s| ^ (i + 1) := pow_nonneg (abs_nonneg s) _
      calc |s| ^ (i + 2) *
          (((i : ℝ) + 3) / (((i + 2).factorial : ℝ) * ((i : ℝ) + 2)))
          = |s| ^ (i + 1) * (|s| * (((i : ℝ) + 3) /
              (((i + 2).factorial : ℝ) * ((i : ℝ) + 2)))) := by
            rw [pow_succ]
            ring
        _ ≤ |s| ^ (i + 1) * (1 / ((i + 1).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hcore hA
        _ = |s| ^ (i + 1) / ((i + 1).factorial : ℝ) := by ring
    have habs_eq : |s ^ (i + 1) / ((i + 1).factorial : ℝ)|
        = |s| ^ (i + 1) / ((i + 1).factorial : ℝ) := by
      rw [abs_div, abs_pow]
      congr 1
      exact abs_of_pos hfact_pos
    calc |Real.exp s - P|
        ≤ |s| ^ (i + 2) *
          (((i : ℝ) + 3) / (((i + 2).factorial : ℝ) * ((i : ℝ) + 2))) := hb'
      _ ≤ |s| ^ (i + 1) / ((i + 1).factorial : ℝ) := harith
      _ = |s ^ (i + 1) / ((i + 1).factorial : ℝ)| := habs_eq.symm
      _ ≤ U := hUb
  have htail : 2 * U ≤ ((((T'.absUpper * ⟨2, 0⟩).roundUp prec).toRat : ℚ) : ℝ) := by
    have h1 : (T'.absUpper * (⟨2, 0⟩ : Dyadic)).toRat = T'.absUpper.toRat * 2 := by
      rw [Dyadic.toRat_mul]
      norm_num [Dyadic.toRat]
    have h2 := Dyadic.le_toRat_roundUp (T'.absUpper * ⟨2, 0⟩) prec
    rw [h1] at h2
    calc (2 : ℝ) * U = ((T'.absUpper.toRat * 2 : ℚ) : ℝ) := by
          rw [hU_def]; push_cast; ring
      _ ≤ _ := by exact_mod_cast h2
  have hfinal := Dyadic.le_toRat_roundUp
    (S'.rad + (T'.absUpper * ⟨2, 0⟩).roundUp prec) prec
  calc |Real.exp s - (S'.mid.toRat : ℝ)|
      ≤ |Real.exp s - P| + |P - (S'.mid.toRat : ℝ)| := abs_sub_le _ _ _
    _ ≤ U + (S'.rad.toRat : ℝ) := add_le_add hrem hmid
    _ ≤ 2 * U + (S'.rad.toRat : ℝ) := by linarith
    _ ≤ ((((T'.absUpper * ⟨2, 0⟩).roundUp prec).toRat : ℚ) : ℝ)
          + (S'.rad.toRat : ℝ) := add_le_add htail le_rfl
    _ = (((S'.rad + (T'.absUpper * ⟨2, 0⟩).roundUp prec).toRat : ℚ) : ℝ) := by
        rw [Dyadic.toRat_add]; push_cast; ring
    _ ≤ _ := by exact_mod_cast hfinal

/-- **Soundness of the Taylor loop**, by induction on fuel, conditional on
the tolerance-exit certificate. -/
theorem taylor_sound (prec : ℤ) (xs : Ball) (tol : Dyadic) {s : ℝ}
    (hxs : xs.Encloses s) (hs : |s| ≤ 1 / 2) :
    ∀ (fuel : ℕ) (term sum : Ball) (i : ℕ),
      term.Encloses (s ^ i / (i.factorial : ℝ)) →
      sum.Encloses (∑ m ∈ Finset.range (i + 1), s ^ m / (m.factorial : ℝ)) →
      taylorExits prec xs tol fuel term i = true →
      (Ball.exp.taylor prec xs tol fuel term sum i).Encloses (Real.exp s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro term sum i _ _ hex
    simp [taylorExits] at hex
  | succ fuel ih =>
    intro term sum i hterm hsum hex
    -- the new term and partial sum
    have hstep : (taylorStep prec xs term i).Encloses
        (s ^ (i + 1) / ((i + 1).factorial : ℝ)) := by
      have h1 := taylorStep_encloses prec hxs hterm i
      have heq : s ^ i / (i.factorial : ℝ) * s / ((i : ℝ) + 1)
          = s ^ (i + 1) / ((i + 1).factorial : ℝ) := by
        have hfac : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hif : ((i.factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast i.factorial_pos.ne'
        have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
        rw [hfac, pow_succ]
        field_simp
      rwa [heq] at h1
    have hsum' : (Ball.add sum (taylorStep prec xs term i) prec).Encloses
        (∑ m ∈ Finset.range (i + 2), s ^ m / (m.factorial : ℝ)) := by
      have h := Ball.add_encloses prec hsum hstep
      rwa [← Finset.sum_range_succ] at h
    -- unfold both the mirror and the target one step
    simp only [taylorExits] at hex
    show (if (taylorStep prec xs term i).absUpper < tol then
        ({ mid := (Ball.add sum (taylorStep prec xs term i) prec).mid,
           rad := ((Ball.add sum (taylorStep prec xs term i) prec).rad +
             ((taylorStep prec xs term i).absUpper * ⟨2, 0⟩).roundUp prec).roundUp
             prec } : Ball)
      else Ball.exp.taylor prec xs tol fuel (taylorStep prec xs term i)
        (Ball.add sum (taylorStep prec xs term i) prec) (i + 1)).Encloses
      (Real.exp s)
    split_ifs at hex ⊢ with hcond
    · -- tolerance exit: add the certified tail
      exact pad_sound prec hs hstep hsum'
    · -- keep looping
      exact ih (taylorStep prec xs term i) _ (i + 1) hstep hsum' hex

/-! ## The squaring phase -/

theorem square_sound (prec : ℤ) :
    ∀ (c : ℕ) (y : Ball) (v : ℝ), y.Encloses v →
      (Ball.exp.square prec y c).Encloses (v ^ (2 ^ c)) := by
  intro c
  induction c with
  | zero =>
    intro y v h
    show y.Encloses (v ^ (2 ^ 0))
    simpa using h
  | succ n ih =>
    intro y v h
    show (Ball.exp.square prec (Ball.mul y y prec) n).Encloses (v ^ (2 ^ (n + 1)))
    have h2 := ih (Ball.mul y y prec) (v * v) (Ball.mul_encloses prec h h)
    have hpow : (v * v) ^ (2 ^ n) = v ^ (2 ^ (n + 1)) := by
      rw [← pow_two, ← pow_mul]
      congr 1
      rw [pow_succ]
      ring
    rwa [hpow] at h2

end ExpSound

/-! ## Assembly -/

namespace Ball

open ExpSound

/-- **The exit certificate**: `true` iff the Taylor loop inside
`Ball.exp x prec` exits through its tolerance branch (the branch whose
result carries a remainder bound). Decidable and executable. -/
def expExits (x : Ball) (prec : ℤ) : Bool :=
  taylorExits prec (x.scale2 (-(expK x))) ⟨1, prec - 4⟩
    ((-prec).toNat + 64) Ball.one 0

set_option maxHeartbeats 2000000 in
private lemma exp_eq (x : Ball) (prec : ℤ) :
    Ball.exp x prec
      = Ball.exp.square prec
          (Ball.exp.taylor prec (x.scale2 (-(expK x))) ⟨1, prec - 4⟩
            ((-prec).toNat + 64) Ball.one Ball.one 0)
          (expK x).toNat := rfl

/-- **Soundness of the executable exponential**, conditional on the
tolerance-exit certificate. -/
theorem exp_sound {x : Ball} {r : ℝ} {prec : ℤ} (hx : x.Encloses r)
    (hex : Ball.expExits x prec = true) :
    (Ball.exp x prec).Encloses (Real.exp r) := by
  rw [exp_eq]
  have hk := expK_nonneg x
  have hxs : (x.scale2 (-(expK x))).Encloses (r * (2 : ℝ) ^ (-(expK x))) :=
    Ball.scale2_encloses hx _
  have hs : |r * (2 : ℝ) ^ (-(expK x))| ≤ 1 / 2 := abs_scaled_le_half hx
  set s : ℝ := r * (2 : ℝ) ^ (-(expK x)) with hs_def
  have hterm0 : Ball.one.Encloses (s ^ 0 / ((0).factorial : ℝ)) := by
    simpa using Ball.one_encloses
  have hsum0 : Ball.one.Encloses
      (∑ m ∈ Finset.range 1, s ^ m / (m.factorial : ℝ)) := by
    simpa using Ball.one_encloses
  have htay := taylor_sound prec _ _ hxs hs ((-prec).toNat + 64)
    Ball.one Ball.one 0 hterm0 hsum0 hex
  have hsq := square_sound prec (expK x).toNat _ _ htay
  have hfinal : Real.exp s ^ (2 ^ (expK x).toNat) = Real.exp r := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hkn : (((expK x).toNat : ℕ) : ℤ) = expK x := Int.toNat_of_nonneg hk
    rw [hs_def]
    rw [show ((2 ^ (expK x).toNat : ℕ) : ℝ) = (2 : ℝ) ^ (((expK x).toNat : ℕ) : ℤ) from by
      rw [zpow_natCast]; push_cast; ring]
    rw [hkn, mul_comm r _, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    simp
  rw [← hfinal]
  exact hsq

end Ball

/-! ## `FastReal` and the logistic: the stochastic layer closes -/

namespace FastReal

/-- The exponential's exit certificate at every precision. Each instance
is decidable and executable; consumers may check any finite prefix at
runtime. -/
def ExpExits (x : FastReal) : Prop :=
  ∀ n : ℕ, Ball.expExits (x (n + 10)) (-((n : ℤ) + 2)) = true

/-- **Soundness of the `FastReal` exponential** under the exit
certificate. -/
theorem exp_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r)
    (hex : ExpExits x) : (FastReal.exp x).Encloses (Real.exp r) := by
  intro n
  exact Ball.exp_sound (hx (n + 10)) (hex n)

end FastReal

namespace FastLogistic

/-- **The executable logistic is sound** given the exponential's exit
certificate: every emitted ball encloses the true Gibbs probability.
Together with `decideBernoulli?_sound` and `gibbsSiteUpdate?_sound`, the
executable Gibbs sampler provably samples the true Bernoulli
distribution — the refinement program has no unproved obligations left. -/
theorem logistic?_sound_of_expExits {x : FastReal} {xR : ℝ}
    (hx : x.Encloses xR) (hex : FastReal.ExpExits (-x)) :
    ∀ (i : ℕ) {b : Ball}, logistic? x i = some b →
      b.Encloses (1 + Real.exp (-xR))⁻¹ :=
  logistic?_sound (FastReal.exp_sound (FastReal.neg_encloses hx) hex)

end FastLogistic

/-! ## `expV`: the verified exponential

The `#eval`s below document an honest finding: at practical precisions the
tolerance `⟨1, prec-4⟩` of `Ball.exp` sits *below* the per-operation
rounding error `2^(prec-1)`, so the tolerance branch never fires and
`expExits` is `false` — the conditional `exp_sound` is true but vacuous
there. `expV` is the three-line repair (this file's code, originals
untouched): the same computation, but the geometric tail is added on
*both* exits, making soundness **unconditional**. The Gibbs layer built on
it below closes the refinement program with no hypotheses left. -/

namespace ExpSound

/-- The Taylor loop with the tail bound added on both exits. -/
def taylorV (prec : ℤ) (xs : Ball) (tol : Dyadic) :
    ℕ → Ball → Ball → ℕ → Ball
  | 0, term, sum, i =>
    let term' := taylorStep prec xs term i
    let sum' := Ball.add sum term' prec
    { mid := sum'.mid,
      rad := (sum'.rad + (term'.absUpper * ⟨2, 0⟩).roundUp prec).roundUp prec }
  | fuel + 1, term, sum, i =>
    let term' := taylorStep prec xs term i
    let sum' := Ball.add sum term' prec
    if term'.absUpper < tol then
      { mid := sum'.mid,
        rad := (sum'.rad + (term'.absUpper * ⟨2, 0⟩).roundUp prec).roundUp prec }
    else taylorV prec xs tol fuel term' sum' (i + 1)

/-- **Unconditional soundness of the padded Taylor loop.** -/
theorem taylorV_sound (prec : ℤ) (xs : Ball) (tol : Dyadic) {s : ℝ}
    (hxs : xs.Encloses s) (hs : |s| ≤ 1 / 2) :
    ∀ (fuel : ℕ) (term sum : Ball) (i : ℕ),
      term.Encloses (s ^ i / (i.factorial : ℝ)) →
      sum.Encloses (∑ m ∈ Finset.range (i + 1), s ^ m / (m.factorial : ℝ)) →
      (taylorV prec xs tol fuel term sum i).Encloses (Real.exp s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro term sum i hterm hsum
    have hstep : (taylorStep prec xs term i).Encloses
        (s ^ (i + 1) / ((i + 1).factorial : ℝ)) := by
      have h1 := taylorStep_encloses prec hxs hterm i
      have heq : s ^ i / (i.factorial : ℝ) * s / ((i : ℝ) + 1)
          = s ^ (i + 1) / ((i + 1).factorial : ℝ) := by
        have hfac : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hif : ((i.factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast i.factorial_pos.ne'
        have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
        rw [hfac, pow_succ]
        field_simp
      rwa [heq] at h1
    have hsum' : (Ball.add sum (taylorStep prec xs term i) prec).Encloses
        (∑ m ∈ Finset.range (i + 2), s ^ m / (m.factorial : ℝ)) := by
      have h := Ball.add_encloses prec hsum hstep
      rwa [← Finset.sum_range_succ] at h
    exact pad_sound prec hs hstep hsum'
  | succ fuel ih =>
    intro term sum i hterm hsum
    have hstep : (taylorStep prec xs term i).Encloses
        (s ^ (i + 1) / ((i + 1).factorial : ℝ)) := by
      have h1 := taylorStep_encloses prec hxs hterm i
      have heq : s ^ i / (i.factorial : ℝ) * s / ((i : ℝ) + 1)
          = s ^ (i + 1) / ((i + 1).factorial : ℝ) := by
        have hfac : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hif : ((i.factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast i.factorial_pos.ne'
        have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
        rw [hfac, pow_succ]
        field_simp
      rwa [heq] at h1
    have hsum' : (Ball.add sum (taylorStep prec xs term i) prec).Encloses
        (∑ m ∈ Finset.range (i + 2), s ^ m / (m.factorial : ℝ)) := by
      have h := Ball.add_encloses prec hsum hstep
      rwa [← Finset.sum_range_succ] at h
    show (if (taylorStep prec xs term i).absUpper < tol then
        ({ mid := (Ball.add sum (taylorStep prec xs term i) prec).mid,
           rad := ((Ball.add sum (taylorStep prec xs term i) prec).rad +
             ((taylorStep prec xs term i).absUpper * ⟨2, 0⟩).roundUp prec).roundUp
             prec } : Ball)
      else taylorV prec xs tol fuel (taylorStep prec xs term i)
        (Ball.add sum (taylorStep prec xs term i) prec) (i + 1)).Encloses
      (Real.exp s)
    split_ifs with hcond
    · exact pad_sound prec hs hstep hsum'
    · exact ih (taylorStep prec xs term i) _ (i + 1) hstep hsum'

end ExpSound

namespace Ball

open ExpSound

/-- **The verified exponential**: `Ball.exp` with the geometric tail added
on both exits of the Taylor loop. -/
def expV (x : Ball) (prec : ℤ) : Ball :=
  Ball.exp.square prec
    (taylorV prec (x.scale2 (-(expK x))) ⟨1, prec - 4⟩
      ((-prec).toNat + 64) Ball.one Ball.one 0)
    (expK x).toNat

/-- **Unconditional soundness of the verified exponential.** -/
theorem expV_sound {x : Ball} {r : ℝ} {prec : ℤ} (hx : x.Encloses r) :
    (Ball.expV x prec).Encloses (Real.exp r) := by
  unfold expV
  have hk := expK_nonneg x
  have hxs : (x.scale2 (-(expK x))).Encloses (r * (2 : ℝ) ^ (-(expK x))) :=
    Ball.scale2_encloses hx _
  have hs : |r * (2 : ℝ) ^ (-(expK x))| ≤ 1 / 2 := abs_scaled_le_half hx
  set s : ℝ := r * (2 : ℝ) ^ (-(expK x)) with hs_def
  have hterm0 : Ball.one.Encloses (s ^ 0 / ((0).factorial : ℝ)) := by
    simpa using Ball.one_encloses
  have hsum0 : Ball.one.Encloses
      (∑ m ∈ Finset.range 1, s ^ m / (m.factorial : ℝ)) := by
    simpa using Ball.one_encloses
  have htay := taylorV_sound prec (x.scale2 (-(expK x))) ⟨1, prec - 4⟩ hxs hs
    ((-prec).toNat + 64) Ball.one Ball.one 0 hterm0 hsum0
  have hsq := square_sound prec (expK x).toNat _ _ htay
  have hfinal : Real.exp s ^ (2 ^ (expK x).toNat) = Real.exp r := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hkn : (((expK x).toNat : ℕ) : ℤ) = expK x := Int.toNat_of_nonneg hk
    rw [hs_def]
    rw [show ((2 ^ (expK x).toNat : ℕ) : ℝ) = (2 : ℝ) ^ (((expK x).toNat : ℕ) : ℤ) from by
      rw [zpow_natCast]; push_cast; ring]
    rw [hkn, mul_comm r _, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    simp
  rw [← hfinal]
  exact hsq

end Ball

namespace FastReal

/-- The verified `FastReal` exponential. -/
def expV (x : FastReal) : FastReal := fun n =>
  Ball.expV (x (n + 10)) (-((n : ℤ) + 2))

/-- **Unconditional soundness**: no certificate needed. -/
theorem expV_sound {x : FastReal} {r : ℝ} (hx : x.Encloses r) :
    (FastReal.expV x).Encloses (Real.exp r) := fun n =>
  Ball.expV_sound (hx (n + 10))

end FastReal

namespace FastLogistic

/-- The verified logistic: `1 / (1 + expV (-x))`. -/
def logisticV? (x : FastReal) : ℕ → Option Ball :=
  FastReal.inv? ((1 : FastReal) + FastReal.expV (-x))

/-- **Unconditional soundness of the verified logistic.** -/
theorem logisticV?_sound {x : FastReal} {xR : ℝ} (hx : x.Encloses xR) :
    ∀ (i : ℕ) {b : Ball}, logisticV? x i = some b →
      b.Encloses (1 + Real.exp (-xR))⁻¹ := by
  intro i b h
  have hden : ((1 : FastReal) + FastReal.expV (-x)).Encloses (1 + Real.exp (-xR)) :=
    FastReal.add_encloses FastReal.encloses_one
      (FastReal.expV_sound (FastReal.neg_encloses hx))
  exact FastReal.inv?_sound hden i h

/-- The verified Gibbs acceptance probability. -/
def probPosV? (κ β L : FastReal) : ℕ → Option Ball :=
  logisticV? (κ * L * β)

/-- The verified one-site Gibbs sampler. -/
def gibbsSiteUpdateV? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (θ : Fin n → FastReal) (κ β : FastReal) (act : Fin n → FastReal)
    (u : Fin n) (r : Dyadic) (fuel : ℕ := defaultFuel) :
    Option (Fin n → FastReal) := do
  let L := FastEnergy.netF w act u - θ u
  let pos ← decideBernoulli? (probPosV? κ β L) r 0 fuel
  pure (Function.update act u (if pos then 1 else -1))

/-- **The refinement program closes.** The verified one-site Gibbs sampler
provably samples the true Bernoulli distribution of the classical Gibbs
kernel — every hypothesis is an enclosure built from literals and ring
operations; nothing is assumed. -/
theorem gibbsSiteUpdateV?_sound {n : ℕ}
    {w : Matrix (Fin n) (Fin n) FastReal} {wR : Matrix (Fin n) (Fin n) ℝ}
    {θ : Fin n → FastReal} {θR : Fin n → ℝ} {κ β : FastReal} {κR βR : ℝ}
    {act : Fin n → FastReal} {actR : Fin n → ℝ}
    (hw : ∀ u v, (w u v).Encloses (wR u v)) (hθ : ∀ u, (θ u).Encloses (θR u))
    (hκ : κ.Encloses κR) (hβ : β.Encloses βR)
    (ha : ∀ v, (act v).Encloses (actR v))
    (u : Fin n) (r : Dyadic) (fuel : ℕ) {act' : Fin n → FastReal}
    (h : gibbsSiteUpdateV? w θ κ β act u r fuel = some act') :
    act' = Function.update act u
      (if ((r.toRat : ℚ) : ℝ) <
          (1 + Real.exp (-(κR * (FastEnergy.netR wR actR u - θR u) * βR)))⁻¹
       then (1 : FastReal) else -1) := by
  classical
  have hL : (FastEnergy.netF w act u - θ u).Encloses
      (FastEnergy.netR wR actR u - θR u) :=
    FastReal.sub_encloses (FastEnergy.netF_encloses hw ha u) (hθ u)
  have harg : (κ * (FastEnergy.netF w act u - θ u) * β).Encloses
      (κR * (FastEnergy.netR wR actR u - θR u) * βR) :=
    FastReal.mul_encloses (FastReal.mul_encloses hκ hL) hβ
  have hp : ∀ i b, probPosV? κ β (FastEnergy.netF w act u - θ u) i = some b →
      b.Encloses (1 + Real.exp (-(κR * (FastEnergy.netR wR actR u - θR u) * βR)))⁻¹ :=
    fun i b hb => logisticV?_sound harg i hb
  unfold gibbsSiteUpdateV? at h
  simp only [Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨pos, hd, hupd⟩ := h
  subst hupd
  have hs := decideBernoulli?_sound hp r 0 fuel hd
  cases pos with
  | true => rw [if_pos (hs.1 rfl)]; simp
  | false => rw [if_neg (not_lt.mpr (hs.2 rfl))]; simp

end FastLogistic

/-! ## Certificates hold in practice -/

-- The honest finding: `Ball.exp`'s tolerance sits below its per-operation
-- rounding error, so the tolerance exit never fires at practical
-- precisions — the certificate is `false` and `exp_sound` is vacuous
-- there. (`expV` below repairs this with an unconditional theorem.)
#eval Ball.expExits (Ball.ofDyadic ⟨-4, 0⟩) (-22)
#eval Ball.expExits (Ball.ofDyadic ⟨1, 0⟩) (-30)

-- The verified exponential agrees with the runtime one and encloses the
-- true values (`e ≈ 2.71828`, `e⁻⁴ ≈ 0.01832`):
#eval Ball.expV (Ball.ofDyadic ⟨1, 0⟩) (-30)
#eval Ball.exp (Ball.ofDyadic ⟨1, 0⟩) (-30)
#eval Ball.expV (Ball.ofDyadic ⟨-4, 0⟩) (-30)

-- The verified logistic: `logisticV? 0 = 1/2` exactly-centered, and the
-- verified Gibbs sampler reproduces the demo decision.
#eval FastLogistic.logisticV? (0 : FastReal) 20
#eval (FastLogistic.gibbsSiteUpdateV? (FastEnergy.hebbW FastEnergy.ps)
  (fun _ => 0) 2 1 ![1, -1, -1, 1] 0 ⟨1, -2⟩).bind actsToInts

end Computable.Fast
