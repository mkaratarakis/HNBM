/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.ExpSound
import HopfieldNet.CReals.Computable.EnergySound

/-!
# Gibbs sampling and descent certificates over computable reals

The network-specific half of the computable-reals soundness layer. The
generic half — enclosure semantics, `compare` soundness, and the verified
`exp`/`inv`/`logistic` — lives in the standalone `ComputableReals` library;
this file adds the pieces that mention a weight matrix, a network energy,
or a Gibbs chain, and therefore belong with the Hopfield/Boltzmann code.

* `FastLogistic.gibbsSiteUpdate?` / `gibbsSweep?` — executable one-site and
  sweep Gibbs updates of a `±1` activation vector, and
  `gibbsSiteUpdate?_sound`: a decided update *is* the classical Gibbs step;
* `FastLogistic.gibbsSiteUpdateV?` / `gibbsSweepV?` — the same built on the
  unconditionally verified `expV`, with `gibbsSweepV?_sound` showing the
  executable chain is the true Gibbs chain;
(The descent-certificate soundness theorem moved to `EnergySound.lean`,
which uses it.)

Split out of `Computable/{Refinement,ExpSound,FastLogistic,GibbsSound}.lean`
when the generic core was isolated into `ComputableReals`; the mathematics
is unchanged.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastEnergy

namespace Computable.Fast

namespace FastLogistic

/-- Twin of `TwoState.gibbsUpdate` as a sampler: one-site Gibbs update of a
`±1` activation vector, driven by a uniform dyadic sample `r ∈ [0,1)`.
Updates neuron `u` to `1` iff `r < P(ζ_pos)`, to `-1` otherwise (`none` if
the Bernoulli decision was not reached within fuel). -/
def gibbsSiteUpdate? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (θ : Fin n → FastReal) (κ β : FastReal) (act : Fin n → FastReal)
    (u : Fin n) (r : Dyadic) (fuel : ℕ := defaultFuel) :
    Option (Fin n → FastReal) := do
  let L := netF w act u - θ u
  let pos ← decideBernoulli? (probPos? κ β L) r 0 fuel
  pure (Function.update act u (if pos then 1 else -1))

/-- Twin of `TwoState.gibbsSweep`: sequential Gibbs sweep over a list of
`(site, uniform sample)` pairs, head applied first. -/
def gibbsSweep? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (θ : Fin n → FastReal) (κ β : FastReal)
    (steps : List (Fin n × Dyadic)) (act : Fin n → FastReal)
    (fuel : ℕ := defaultFuel) : Option (Fin n → FastReal) :=
  steps.foldlM (fun a step => gibbsSiteUpdate? w θ κ β a step.1 step.2 fuel) act


/-- **The one-site Gibbs sampler samples the true Bernoulli distribution.**
Conditional on the probability approximator being sound for the true
acceptance probability `P` (for `probPos?` this reduces to `exp`/`inv?`
enclosure — the remaining obligations), a decided update is *exactly* the
classical Gibbs step: flip to `1` iff the uniform sample fell below `P`. -/
theorem gibbsSiteUpdate?_sound {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (θ : Fin n → FastReal) (κ β : FastReal) (act : Fin n → FastReal)
    (u : Fin n) (r : Dyadic) (fuel : ℕ) {P : ℝ}
    (hprob : ∀ i b, probPos? κ β (FastEnergy.netF w act u - θ u) i = some b →
      b.Encloses P)
    {act' : Fin n → FastReal}
    (h : gibbsSiteUpdate? w θ κ β act u r fuel = some act') :
    act' = Function.update act u
      (if ((r.toRat : ℚ) : ℝ) < P then (1 : FastReal) else -1) := by
  classical
  unfold gibbsSiteUpdate? at h
  simp only [Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨pos, hd, hupd⟩ := h
  subst hupd
  have hs := decideBernoulli?_sound hprob r 0 fuel hd
  cases pos with
  | true => rw [if_pos (hs.1 rfl)]; simp
  | false => rw [if_neg (not_lt.mpr (hs.2 rfl))]; simp

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

/-- The verified Gibbs sweep over `(site, sample)` pairs. -/
def gibbsSweepV? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (θ : Fin n → FastReal) (κ β : FastReal)
    (steps : List (Fin n × Dyadic)) (act : Fin n → FastReal)
    (fuel : ℕ := defaultFuel) : Option (Fin n → FastReal) :=
  steps.foldlM (fun a step => gibbsSiteUpdateV? w θ κ β a step.1 step.2 fuel) act

open Classical in
/-- One step of the *classical* Gibbs chain driven by a uniform sample:
flip site `u` to `1` iff the sample fell below the true acceptance
probability of the current real state. -/
noncomputable def realGibbsStep {n : ℕ} (wR : Matrix (Fin n) (Fin n) ℝ)
    (θR : Fin n → ℝ) (κR βR : ℝ) (actR : Fin n → ℝ) (u : Fin n) (r : Dyadic) :
    Fin n → ℝ :=
  Function.update actR u
    (if ((r.toRat : ℚ) : ℝ) <
        (1 + Real.exp (-(κR * (FastEnergy.netR wR actR u - θR u) * βR)))⁻¹
     then 1 else -1)

/-- **The executable Gibbs chain is the true Gibbs chain.** A decided
verified sweep encloses, state by state, the classical Gibbs trajectory
driven by the same uniform samples — the sampler does not merely
approximate the kernel, it computes its decisions exactly. -/
theorem gibbsSweepV?_sound {n : ℕ}
    {w : Matrix (Fin n) (Fin n) FastReal} {wR : Matrix (Fin n) (Fin n) ℝ}
    {θ : Fin n → FastReal} {θR : Fin n → ℝ} {κ β : FastReal} {κR βR : ℝ}
    (hw : ∀ u v, (w u v).Encloses (wR u v)) (hθ : ∀ u, (θ u).Encloses (θR u))
    (hκ : κ.Encloses κR) (hβ : β.Encloses βR) {fuel : ℕ} :
    ∀ (steps : List (Fin n × Dyadic)) (act : Fin n → FastReal)
      (actR : Fin n → ℝ),
      (∀ v, (act v).Encloses (actR v)) →
      ∀ {act' : Fin n → FastReal},
        gibbsSweepV? w θ κ β steps act fuel = some act' →
        ∀ v, (act' v).Encloses
          ((steps.foldl
            (fun aR step => realGibbsStep wR θR κR βR aR step.1 step.2)
            actR) v) := by
  intro steps
  induction steps with
  | nil =>
    intro act actR ha act' h v
    simp only [gibbsSweepV?, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at h
    subst h
    simpa using ha v
  | cons step rest ih =>
    intro act actR ha act' h v
    simp only [gibbsSweepV?, List.foldlM_cons, Option.bind_eq_bind',
      Option.bind_eq_some_iff] at h
    obtain ⟨a₁, h₁, hrest⟩ := h
    have hupd := gibbsSiteUpdateV?_sound hw hθ hκ hβ ha step.1 step.2 fuel h₁
    subst hupd
    have ha₁ : ∀ v, ((Function.update act step.1
        (if ((step.2.toRat : ℚ) : ℝ) <
            (1 + Real.exp (-(κR * (FastEnergy.netR wR actR step.1 - θR step.1) * βR)))⁻¹
         then (1 : FastReal) else -1)) v).Encloses
        ((realGibbsStep wR θR κR βR actR step.1 step.2) v) := by
      intro v
      unfold realGibbsStep
      by_cases hv : v = step.1
      · subst hv
        rw [Function.update_self, Function.update_self]
        split_ifs
        · exact FastReal.encloses_one
        · exact FastReal.neg_encloses FastReal.encloses_one
      · rw [Function.update_of_ne hv, Function.update_of_ne hv]
        exact ha v
    have := ih _ _ ha₁ hrest v
    simpa [List.foldl_cons] using this

end FastLogistic


end Computable.Fast
