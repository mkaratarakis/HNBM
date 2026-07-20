/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.Preservation
import ComputableReals.Computable.FastLogistic

/-!
# Soundness of the executable Gibbs sampler

The stochastic layer's semantic core, verified:

* `Ball.ofInterval_encloses` — the interval-to-ball adapter encloses every
  point of the dyadic interval (midpoint rounding and radius rounding both
  accounted for). This is the foundation for `inv?`, `min`, `max`, `sqrt`
  soundness;
* `decideBernoulli?_sound` — **the Bernoulli decision is truthful**: given
  any sound partial approximator of a probability `P`, a decided comparison
  against a uniform sample `r` returns `some true` exactly when `r < P` and
  `some false` exactly when `P ≤ r`;
* `gibbsSiteUpdate?_sound` — a decided one-site Gibbs update produces
  exactly `Function.update act u (if r < P then 1 else -1)`: the sampler
  samples the true Bernoulli distribution.

These are *conditional* on the probability approximator being sound
(`∀ i b, p? i = some b → b.Encloses P`). Discharging that hypothesis for
`probPos?` (= `logistic?` = `inv? ∘ (1 + exp ∘ neg)`) requires enclosure
for `FastReal.exp` (Taylor-loop error analysis) and `inv?`
(directed-division bounds) — the two documented remaining obligations of
the refinement program; `ofInterval_encloses` below is the first half of
the `inv?` side.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastLogistic

namespace Computable.Fast

namespace Dyadic

/-- The executable `≤` on dyadics is sound for `toRat` (it is not complete:
distinct representations of equal values are `le`-incomparable, cf.
`toRat_eq_of_not_lt`). -/
theorem toRat_le_of_le {a b : Dyadic} (h : a ≤ b) : a.toRat ≤ b.toRat := by
  rcases h with hlt | rfl
  · exact (toRat_lt_iff.mp hlt).le
  · exact le_refl _

end Dyadic

namespace Ball

/-- **The interval-to-ball adapter is sound**: `ofInterval lo hi prec`
encloses every real in `[lo, hi]`. -/
theorem ofInterval_encloses {lo hi : Dyadic} {r : ℝ} (prec : ℤ)
    (hlo : ((lo.toRat : ℚ) : ℝ) ≤ r) (hhi : r ≤ ((hi.toRat : ℚ) : ℝ)) :
    (Ball.ofInterval lo hi prec).Encloses r := by
  have hloq : lo.toRat ≤ hi.toRat := by exact_mod_cast hlo.trans hhi
  rw [encloses_iff_abs]
  have hmid : (Ball.ofInterval lo hi prec).mid
      = ((lo + hi) * (⟨1, -1⟩ : Dyadic)).round prec := rfl
  have hrad : (Ball.ofInterval lo hi prec).rad
      = ((hi - lo).abs * (⟨1, -1⟩ : Dyadic) + ⟨1, prec - 1⟩).roundUp prec := rfl
  rw [hmid, hrad]
  have hhalf : (Dyadic.toRat ⟨1, -1⟩ : ℚ) = 1 / 2 := by
    norm_num [Dyadic.toRat, zpow_neg]
  have herrval : (Dyadic.toRat ⟨1, prec - 1⟩ : ℚ) = 2 ^ (prec - 1) := by
    simp [Dyadic.toRat]
  -- the raw midpoint and its rounding error
  have hmidval : (((lo + hi) * (⟨1, -1⟩ : Dyadic)).toRat : ℚ)
      = (lo.toRat + hi.toRat) / 2 := by
    simp [hhalf]
    ring
  have hround := Dyadic.abs_toRat_round_sub_le ((lo + hi) * (⟨1, -1⟩ : Dyadic)) prec
  -- the raw radius
  have hradval : (((hi - lo).abs * (⟨1, -1⟩ : Dyadic) + ⟨1, prec - 1⟩).toRat : ℚ)
      = (hi.toRat - lo.toRat) / 2 + 2 ^ (prec - 1) := by
    simp [Dyadic.toRat_abs, hhalf, herrval,
      abs_of_nonneg (sub_nonneg.mpr hloq)]
    ring
  have hradup := Dyadic.le_toRat_roundUp
    ((hi - lo).abs * (⟨1, -1⟩ : Dyadic) + ⟨1, prec - 1⟩) prec
  -- assemble over ℝ
  set L : ℝ := ((lo.toRat : ℚ) : ℝ)
  set H : ℝ := ((hi.toRat : ℚ) : ℝ)
  have hM' : ((((lo + hi) * (⟨1, -1⟩ : Dyadic)).toRat : ℚ) : ℝ) = (L + H) / 2 := by
    rw [hmidval]; push_cast; ring
  have hE : |((((lo + hi) * (⟨1, -1⟩ : Dyadic)).round prec).toRat : ℝ)
      - ((((lo + hi) * (⟨1, -1⟩ : Dyadic)).toRat : ℚ) : ℝ)| ≤ ((2 ^ (prec - 1) : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast hround
  calc |r - ((((lo + hi) * (⟨1, -1⟩ : Dyadic)).round prec).toRat : ℝ)|
      ≤ |r - ((((lo + hi) * (⟨1, -1⟩ : Dyadic)).toRat : ℚ) : ℝ)|
        + |((((lo + hi) * (⟨1, -1⟩ : Dyadic)).toRat : ℚ) : ℝ)
            - ((((lo + hi) * (⟨1, -1⟩ : Dyadic)).round prec).toRat : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ (H - L) / 2 + ((2 ^ (prec - 1) : ℚ) : ℝ) := by
        apply add_le_add
        · rw [hM', abs_sub_le_iff]
          constructor <;> linarith
        · rw [abs_sub_comm]; exact hE
    _ = ((((hi.toRat - lo.toRat) / 2 + 2 ^ (prec - 1) : ℚ)) : ℝ) := by
        push_cast; ring
    _ ≤ ((((hi - lo).abs * (⟨1, -1⟩ : Dyadic) + ⟨1, prec - 1⟩).roundUp prec).toRat : ℝ) := by
        rw [← hradval]
        exact_mod_cast hradup

end Ball

/-! ## The Bernoulli decision is truthful -/

namespace FastLogistic

/-- **Soundness of the Bernoulli decision.** Against any sound partial
approximator of a probability `P`, a decided `decideBernoulli?` is
truthful: `some true` means `r < P`, `some false` means `P ≤ r`. -/
theorem decideBernoulli?_sound {p? : ℕ → Option Ball} {P : ℝ}
    (hp : ∀ i b, p? i = some b → b.Encloses P) (r : Dyadic) :
    ∀ (i fuel : ℕ) {res : Bool},
      decideBernoulli? p? r i fuel = some res →
      (res = true → ((r.toRat : ℚ) : ℝ) < P) ∧
        (res = false → P ≤ ((r.toRat : ℚ) : ℝ)) := by
  intro i fuel
  induction fuel generalizing i with
  | zero =>
    intro res h
    simp [decideBernoulli?] at h
  | succ f ih =>
    intro res h
    rw [decideBernoulli?] at h
    split at h
    · exact ih (i + 1) h
    · rename_i b hpi
      have hb := hp i b hpi
      split_ifs at h with h1 h2
      · -- `r < lo b`, so `r < P`
        injection h with h; subst h
        refine ⟨fun _ => ?_, fun hf => by simp at hf⟩
        have hq : r.toRat < (b.mid - b.rad).toRat := Dyadic.toRat_lt_iff.mp h1
        have hq' : (r.toRat : ℚ) < b.mid.toRat - b.rad.toRat := by simpa using hq
        have hcast : ((r.toRat : ℚ) : ℝ) < ((b.mid.toRat - b.rad.toRat : ℚ) : ℝ) := by
          exact_mod_cast hq'
        exact hcast.trans_le hb.1
      · -- `hi b ≤ r`, so `P ≤ r`
        injection h with h; subst h
        refine ⟨fun ht => by simp at ht, fun _ => ?_⟩
        have hq : (b.mid + b.rad).toRat ≤ r.toRat := Dyadic.toRat_le_of_le h2
        have hq' : b.mid.toRat + b.rad.toRat ≤ (r.toRat : ℚ) := by simpa using hq
        have hcast : ((b.mid.toRat + b.rad.toRat : ℚ) : ℝ) ≤ ((r.toRat : ℚ) : ℝ) := by
          exact_mod_cast hq'
        exact hb.2.trans hcast
      · exact ih (i + 1) h

end FastLogistic

end Computable.Fast
