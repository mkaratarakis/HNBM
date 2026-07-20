import ComputableReals.Decision
/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CRealsFastBackend
import Mathlib.Data.List.Chain

/-!
# Refinement: soundness of fueled comparisons over `ℝ`

This file welds the executable layer to the real numbers: it gives raw
`FastReal` values (bare `ℕ → Ball` programs, which carry no invariant)
*enclosure semantics* and proves that the fueled comparison primitives are
**sound** for any reals so enclosed:

* `Dyadic.toRat_lt_iff` — the bit-shift comparison on dyadics agrees with
  the rational order (the missing order counterpart of the backend's
  `toRat_add/sub/mul` lemmas);
* `Ball.Encloses b r` / `FastReal.Encloses x r` — `r` lies in every ball
  `x n`;
* `FastReal.compare_sound` — if `compare x y fuel = some o` and `x, y`
  enclose `r, s`, then `o` truthfully orders `r` and `s` (`lt → r < s`,
  `eq → r = s`, `gt → s < r`). Both the separation branches *and* the
  exact-point (tie-deciding) branch are covered;
* `API.leF_sound` / `API.eqF_sound` — the derived tests are sound;
  really is a monotone non-increasing chain of the enclosed real energies.

Consequently the runtime certificates of `CReals/API/` and
`CReals/Computable/` are not mere observations: combined with an enclosure
proof for the inputs, they are *theorems* about the `ℝ`-dynamics. Enclosure
preservation for the arithmetic (`add`, `mul`, `exp`, …) is the remaining
future work; grounding facts for exact inputs (`encloses_ofDyadic`,
`encloses_zero`, `encloses_one`) are provided here.

`none` never asserts anything, so no completeness claim is made — matching
the undecidability of the order on computable reals.
-/

namespace Computable.Fast

/-! ## Dyadic order agrees with the rational order -/

namespace Dyadic

private lemma two_q_pos : (0 : ℚ) < 2 := by norm_num
private lemma two_q_ne : (2 : ℚ) ≠ 0 := by norm_num

/-- `m₁ < m₂ <<< s`, read at exponents `e` and `e + s`. -/
private lemma lt_shift_iff (m₁ m₂ : ℤ) (e : ℤ) (s : ℕ) :
    m₁ < m₂ <<< s ↔ (m₁ : ℚ) * 2 ^ e < (m₂ : ℚ) * 2 ^ (e + (s : ℤ)) := by
  rw [Int.shiftLeft_eq]
  constructor
  · intro hlt
    have h1 : (m₁ : ℚ) < (m₂ : ℚ) * 2 ^ s := by exact_mod_cast hlt
    calc (m₁ : ℚ) * 2 ^ e < ((m₂ : ℚ) * 2 ^ s) * 2 ^ e :=
          mul_lt_mul_of_pos_right h1 (zpow_pos two_q_pos e)
      _ = (m₂ : ℚ) * 2 ^ (e + (s : ℤ)) := by
          rw [zpow_add₀ two_q_ne, zpow_natCast]; ring
  · intro hlt
    have h1 : (m₁ : ℚ) * 2 ^ e < ((m₂ : ℚ) * 2 ^ s) * 2 ^ e := by
      calc (m₁ : ℚ) * 2 ^ e < (m₂ : ℚ) * 2 ^ (e + (s : ℤ)) := hlt
        _ = ((m₂ : ℚ) * 2 ^ s) * 2 ^ e := by
            rw [zpow_add₀ two_q_ne, zpow_natCast]; ring
    have h2 : (m₁ : ℚ) < (m₂ : ℚ) * 2 ^ s :=
      lt_of_mul_lt_mul_right h1 (zpow_pos two_q_pos e).le
    exact_mod_cast h2

/-- `m₁ <<< s < m₂`, read at exponents `e + s` and `e`. -/
private lemma shift_lt_iff (m₁ m₂ : ℤ) (e : ℤ) (s : ℕ) :
    m₁ <<< s < m₂ ↔ (m₁ : ℚ) * 2 ^ (e + (s : ℤ)) < (m₂ : ℚ) * 2 ^ e := by
  rw [Int.shiftLeft_eq]
  constructor
  · intro hlt
    have h1 : (m₁ : ℚ) * 2 ^ s < (m₂ : ℚ) := by exact_mod_cast hlt
    calc (m₁ : ℚ) * 2 ^ (e + (s : ℤ)) = ((m₁ : ℚ) * 2 ^ s) * 2 ^ e := by
          rw [zpow_add₀ two_q_ne, zpow_natCast]; ring
      _ < (m₂ : ℚ) * 2 ^ e :=
          mul_lt_mul_of_pos_right h1 (zpow_pos two_q_pos e)
  · intro hlt
    have h1 : ((m₁ : ℚ) * 2 ^ s) * 2 ^ e < (m₂ : ℚ) * 2 ^ e := by
      calc ((m₁ : ℚ) * 2 ^ s) * 2 ^ e = (m₁ : ℚ) * 2 ^ (e + (s : ℤ)) := by
            rw [zpow_add₀ two_q_ne, zpow_natCast]; ring
        _ < (m₂ : ℚ) * 2 ^ e := hlt
    have h2 : (m₁ : ℚ) * 2 ^ s < (m₂ : ℚ) :=
      lt_of_mul_lt_mul_right h1 (zpow_pos two_q_pos e).le
    exact_mod_cast h2

/-- The executable bit-shift order on dyadics agrees with the rational
order: the missing order counterpart of the backend's `toRat` ring
lemmas. -/
theorem toRat_lt_iff {a b : Dyadic} : a < b ↔ a.toRat < b.toRat := by
  show Dyadic.lt a b ↔ _
  unfold Dyadic.lt
  by_cases h : a.exp ≤ b.exp
  · have key := lt_shift_iff a.man b.man a.exp (b.exp - a.exp).toNat
    rw [show a.exp + ((b.exp - a.exp).toNat : ℤ) = b.exp from by omega] at key
    simpa [Dyadic.toRat, if_pos h] using key
  · have key := shift_lt_iff a.man b.man b.exp (a.exp - b.exp).toNat
    rw [show b.exp + ((a.exp - b.exp).toNat : ℤ) = a.exp from by omega] at key
    simpa [Dyadic.toRat, if_neg h] using key

/-- Undecided both ways means equal denotations (used by the exact-point
branch of `compare`). Note `Dyadic.le` itself is *not* complete for
`toRat` — distinct representations of the same value (`⟨2,0⟩` vs `⟨1,1⟩`)
are `le`-incomparable — which is why soundness goes through `toRat`. -/
theorem toRat_eq_of_not_lt {a b : Dyadic} (h1 : ¬ a < b) (h2 : ¬ b < a) :
    a.toRat = b.toRat :=
  le_antisymm
    (not_lt.mp fun hlt => h2 (toRat_lt_iff.mpr hlt))
    (not_lt.mp fun hlt => h1 (toRat_lt_iff.mpr hlt))

/-- A dyadic with zero mantissa denotes `0` (radius of an exact ball). -/
theorem toRat_eq_zero_of_man_eq_zero {d : Dyadic} (h : d.man = 0) :
    d.toRat = 0 := by
  simp [Dyadic.toRat, h]

end Dyadic

/-! ## Enclosure semantics -/

/-- A ball encloses a real: `r ∈ [mid - rad, mid + rad]`. -/
def Ball.Encloses (b : Ball) (r : ℝ) : Prop :=
  ((b.mid.toRat - b.rad.toRat : ℚ) : ℝ) ≤ r ∧
    r ≤ ((b.mid.toRat + b.rad.toRat : ℚ) : ℝ)

/-- A raw `FastReal` program encloses a real if every emitted ball does.
This is the refinement relation: `FastReal` carries no invariant of its
own, so soundness statements are conditional on it. -/
def FastReal.Encloses (x : FastReal) (r : ℝ) : Prop :=
  ∀ n : ℕ, (x n).Encloses r

/-- Exact dyadic constants enclose their denotation (radius `0`). -/
theorem FastReal.encloses_ofDyadic (d : Dyadic) :
    (FastReal.ofDyadic d).Encloses ((d.toRat : ℚ) : ℝ) := by
  intro n
  have h : (FastReal.ofDyadic d) n = Ball.ofDyadic d := rfl
  simp only [h, Ball.Encloses, Ball.ofDyadic]
  norm_num [Dyadic.toRat]

theorem FastReal.encloses_zero : (0 : FastReal).Encloses 0 := by
  intro n
  have h : (0 : FastReal) n = Ball.zero := rfl
  simp only [h, Ball.Encloses, Ball.zero]
  norm_num [Dyadic.toRat]

theorem FastReal.encloses_one : (1 : FastReal).Encloses 1 := by
  intro n
  have h : (1 : FastReal) n = Ball.one := rfl
  simp only [h, Ball.Encloses, Ball.one]
  norm_num [Dyadic.toRat]

/-! ## Soundness of `FastReal.compare` -/

namespace FastReal

/-- What each decided ordering asserts about the enclosed reals. -/
def OrderingHolds (o : Ordering) (r s : ℝ) : Prop :=
  match o with
  | .lt => r < s
  | .eq => r = s
  | .gt => s < r

/-- An exact ball (zero-mantissa radius) pins its enclosed real to the
midpoint exactly. -/
private lemma encloses_exact {b : Ball} {r : ℝ} (hb : b.Encloses r)
    (h0 : b.rad.man = 0) : r = ((b.mid.toRat : ℚ) : ℝ) := by
  have hz : b.rad.toRat = 0 := Dyadic.toRat_eq_zero_of_man_eq_zero h0
  rcases hb with ⟨hlo, hhi⟩
  rw [hz] at hlo hhi
  simp only [sub_zero, add_zero] at hlo hhi
  exact le_antisymm hhi hlo

private lemma loop_sound {x y : FastReal} {r s : ℝ}
    (hx : x.Encloses r) (hy : y.Encloses s) :
    ∀ (fuel i : ℕ) {o : Ordering},
      FastReal.compare.loop x y i fuel = some o → OrderingHolds o r s := by
  intro fuel
  induction fuel with
  | zero =>
    intro i o h
    simp [FastReal.compare.loop] at h
  | succ n ih =>
    intro i o h
    rw [FastReal.compare.loop] at h
    split_ifs at h with h1 h2 h3 h4 h5
    · -- separation: hi (x i) < lo (y i), so r < s
      injection h with h; subst h
      have hq : ((x i).mid.toRat + (x i).rad.toRat : ℚ) <
          ((y i).mid.toRat - (y i).rad.toRat : ℚ) := by
        have := Dyadic.toRat_lt_iff.mp h1
        simpa using this
      have hcast : (((x i).mid.toRat + (x i).rad.toRat : ℚ) : ℝ) <
          (((y i).mid.toRat - (y i).rad.toRat : ℚ) : ℝ) := by exact_mod_cast hq
      exact ((hx i).2.trans_lt hcast).trans_le (hy i).1
    · -- separation the other way: s < r
      injection h with h; subst h
      have hq : ((y i).mid.toRat + (y i).rad.toRat : ℚ) <
          ((x i).mid.toRat - (x i).rad.toRat : ℚ) := by
        have := Dyadic.toRat_lt_iff.mp h2
        simpa using this
      have hcast : (((y i).mid.toRat + (y i).rad.toRat : ℚ) : ℝ) <
          (((x i).mid.toRat - (x i).rad.toRat : ℚ) : ℝ) := by exact_mod_cast hq
      exact ((hy i).2.trans_lt hcast).trans_le (hx i).1
    all_goals try (
      -- the three exact-point leaves: reals are pinned to the midpoints
      have hx0 : (x i).rad.man = 0 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp h3).1
      have hy0 : (y i).rad.man = 0 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp h3).2
      have hr : r = (((x i).mid.toRat : ℚ) : ℝ) := encloses_exact (hx i) hx0
      have hs : s = (((y i).mid.toRat : ℚ) : ℝ) := encloses_exact (hy i) hy0
      injection h with h; subst h)
    · -- exact tie broken: mid_x < mid_y
      have hq := Dyadic.toRat_lt_iff.mp h4
      rw [hr, hs]
      show (((x i).mid.toRat : ℚ) : ℝ) < (((y i).mid.toRat : ℚ) : ℝ)
      exact_mod_cast hq
    · -- exact tie broken: mid_y < mid_x
      have hq := Dyadic.toRat_lt_iff.mp h5
      rw [hr, hs]
      show (((y i).mid.toRat : ℚ) : ℝ) < (((x i).mid.toRat : ℚ) : ℝ)
      exact_mod_cast hq
    · -- exact tie: equal denotations
      have hq := Dyadic.toRat_eq_of_not_lt h4 h5
      rw [hr, hs]
      show (((x i).mid.toRat : ℚ) : ℝ) = (((y i).mid.toRat : ℚ) : ℝ)
      exact_mod_cast hq
    · -- refine at the next precision
      exact ih (i + 1) h

/-- **Soundness of the fueled comparison.** A decided `compare` truthfully
orders any reals enclosed by its arguments — including exact ties. -/
theorem compare_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ} {o : Ordering}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : FastReal.compare x y fuel = some o) : OrderingHolds o r s := by
  unfold FastReal.compare at h
  exact loop_sound hx hy (fuel + 1) 0 h

theorem compare_lt_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : FastReal.compare x y fuel = some .lt) : r < s :=
  compare_sound hx hy h

theorem compare_eq_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : FastReal.compare x y fuel = some .eq) : r = s :=
  compare_sound hx hy h

theorem compare_gt_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : FastReal.compare x y fuel = some .gt) : s < r :=
  compare_sound hx hy h

end FastReal

/-! ## Soundness of the API tests -/

namespace API

/-- A decided `leF x y = some true` really means `r ≤ s`. -/
theorem leF_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : leF x y fuel = some true) : r ≤ s := by
  unfold leF at h
  cases hc : FastReal.compare x y fuel with
  | none => rw [hc] at h; simp at h
  | some o =>
    rw [hc] at h
    have hs := FastReal.compare_sound hx hy hc
    cases o with
    | lt => exact le_of_lt hs
    | eq => exact le_of_eq hs
    | gt => simp at h

/-- A decided `eqF x y = some true` really means `r = s`. -/
theorem eqF_sound {x y : FastReal} {r s : ℝ} {fuel : ℕ}
    (hx : x.Encloses r) (hy : y.Encloses s)
    (h : eqF x y fuel = some true) : r = s := by
  unfold eqF at h
  cases hc : FastReal.compare x y fuel with
  | none => rw [hc] at h; simp at h
  | some o =>
    rw [hc] at h
    have hs := FastReal.compare_sound hx hy hc
    cases o with
    | lt => simp at h
    | eq => exact hs
    | gt => simp at h

end API


end Computable.Fast
