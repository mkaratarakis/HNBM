/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.Preservation

/-!
# End-to-end: certified energy descent is real energy descent

The last rung of the refinement tower. `Preservation.lean` gives enclosure
for single ring operations; here it is lifted through the folds of
`FastEnergy` (`netF`, `EθF`, `EwF`, `EF`) to their `ℝ`-valued twins
(`netR`, …, `ER`), culminating in

* `certified_descent_real` — if the weights, thresholds and states of a run
  enclose real counterparts, and `descentCertified?` returns `some true`
  on the `FastReal` energies, then the *real* energies `ER` form a
  non-increasing chain. No unproved hypotheses: the certificate is
  computed, the enclosures are built structurally.

The demo instantiates this for the 4-neuron Hebbian network of
`FastEnergy.lean`: `demo_real_descent` is a *theorem* that the real
Hebbian energies of the run's states descend (`4 ≥ 0 ≥ -4`), obtained
from the executable certificate via `decide` — no analysis performed by
hand.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastEnergy

set_option maxRecDepth 8192

namespace Computable.Fast

/-! ## Folds preserve enclosure -/

/-- Lift enclosure through `List.foldl`, given that each step does. -/
theorem FastReal.foldl_encloses {α : Type} (step : FastReal → α → FastReal)
    (stepR : ℝ → α → ℝ) :
    ∀ (l : List α),
      (∀ (x : FastReal) (r : ℝ) (a : α), a ∈ l → x.Encloses r →
        (step x a).Encloses (stepR r a)) →
      ∀ {init : FastReal} {rinit : ℝ}, init.Encloses rinit →
        (l.foldl step init).Encloses (l.foldl stepR rinit) := by
  intro l
  induction l with
  | nil => intro _ init rinit h; simpa using h
  | cons a t ih =>
    intro hstep init rinit h
    simp only [List.foldl_cons]
    exact ih (fun x r b hb hx => hstep x r b (List.mem_cons_of_mem a hb) hx)
      (hstep init rinit a List.mem_cons_self h)

namespace FastEnergy

/-! ## The `ℝ`-valued twins of the executable energy -/

variable {n : ℕ}

/-- `ℝ` twin of `netF`. -/
noncomputable def netR (w : Matrix (Fin n) (Fin n) ℝ) (act : Fin n → ℝ)
    (u : Fin n) : ℝ :=
  (List.finRange n).foldl (fun acc v => if v ≠ u then acc + w u v * act v else acc) 0

/-- `ℝ` twin of `EθF`. -/
noncomputable def EθR (θ act : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (fun acc u => acc + θ u * act u) 0

/-- `ℝ` twin of `EwF`. -/
noncomputable def EwR (w : Matrix (Fin n) (Fin n) ℝ) (act : Fin n → ℝ) : ℝ :=
  (-(1/2) : ℝ) * (List.finRange n).foldl (fun acc u => acc + act u * netR w act u) 0

/-- `ℝ` twin of the Hopfield energy `EF`. -/
noncomputable def ER (w : Matrix (Fin n) (Fin n) ℝ) (θ act : Fin n → ℝ) : ℝ :=
  EwR w act + EθR θ act

/-- The exact dyadic `-1/2` encloses the real `-1/2`. -/
theorem negHalf_encloses : negHalf.Encloses (-(1/2 : ℝ)) := by
  have h := FastReal.encloses_ofDyadic ⟨-1, -1⟩
  have hval : ((Dyadic.toRat ⟨-1, -1⟩ : ℚ) : ℝ) = -(1/2 : ℝ) := by
    simp [Dyadic.toRat, zpow_neg]
  rwa [hval] at h

variable {w : Matrix (Fin n) (Fin n) FastReal} {wR : Matrix (Fin n) (Fin n) ℝ}
variable {θ : Fin n → FastReal} {θR : Fin n → ℝ}
variable {act : Fin n → FastReal} {actR : Fin n → ℝ}

/-- The executable field encloses the real field. -/
theorem netF_encloses (hw : ∀ u v, (w u v).Encloses (wR u v))
    (ha : ∀ v, (act v).Encloses (actR v)) (u : Fin n) :
    (netF w act u).Encloses (netR wR actR u) := by
  apply FastReal.foldl_encloses _ _ _ _ FastReal.encloses_zero
  intro x r v _ hx
  by_cases hvu : v ≠ u
  · rw [if_pos hvu, if_pos hvu]
    exact FastReal.add_encloses hx (FastReal.mul_encloses (hw u v) (ha v))
  · rw [if_neg hvu, if_neg hvu]
    exact hx

/-- The executable threshold energy encloses the real one. -/
theorem EθF_encloses (hθ : ∀ u, (θ u).Encloses (θR u))
    (ha : ∀ v, (act v).Encloses (actR v)) :
    (EθF θ act).Encloses (EθR θR actR) := by
  apply FastReal.foldl_encloses _ _ _ _ FastReal.encloses_zero
  intro x r u _ hx
  exact FastReal.add_encloses hx (FastReal.mul_encloses (hθ u) (ha u))

/-- The executable weight energy encloses the real one. -/
theorem EwF_encloses (hw : ∀ u v, (w u v).Encloses (wR u v))
    (ha : ∀ v, (act v).Encloses (actR v)) :
    (EwF w act).Encloses (EwR wR actR) := by
  apply FastReal.mul_encloses negHalf_encloses
  apply FastReal.foldl_encloses _ _ _ _ FastReal.encloses_zero
  intro x r u _ hx
  exact FastReal.add_encloses hx
    (FastReal.mul_encloses (ha u) (netF_encloses hw ha u))

/-- **The executable Hopfield energy encloses the real Hopfield energy.** -/
theorem EF_encloses (hw : ∀ u v, (w u v).Encloses (wR u v))
    (hθ : ∀ u, (θ u).Encloses (θR u))
    (ha : ∀ v, (act v).Encloses (actR v)) :
    (EF w θ act).Encloses (ER wR θR actR) :=
  FastReal.add_encloses (EwF_encloses hw ha) (EθF_encloses hθ ha)

/-! ## The end-to-end theorem -/

/-- **Certified descent is real descent.** If weights, thresholds and every
state of a run enclose real counterparts, and the executable certificate
`descentCertified?` returns `some true` on the `FastReal` energies, then the
real energies form a non-increasing chain. -/
theorem certified_descent_real
    (hw : ∀ u v, (w u v).Encloses (wR u v))
    (hθ : ∀ u, (θ u).Encloses (θR u))
    {states : List (Fin n → FastReal)} {statesR : List (Fin n → ℝ)}
    (hs : List.Forall₂ (fun a aR => ∀ v, (a v).Encloses (aR v)) states statesR)
    {fuel : ℕ}
    (hcert : descentCertified? (states.map (fun a => EF w θ a)) fuel = some true) :
    List.IsChain (fun a b => b ≤ a) (statesR.map (fun aR => ER wR θR aR)) := by
  apply descentCertified?_sound _ hcert
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hs.imp (fun _ _ ha => EF_encloses hw hθ ha)

/-! ## The demo, fully discharged

The 4-neuron Hebbian run of `FastEnergy.lean` visits the states
`[1,-1,-1,1] → [-1,-1,-1,1] → [-1,1,-1,1]` with energies `4, 0, -4`.
Here the descent of the *real* energies is a theorem: the certificate is
evaluated by `decide`, the enclosures are built structurally from `±1`
literals — no real-number analysis is performed by hand. -/

/-- `ℝ` twin of the demo's Hebbian weights. -/
noncomputable def hebbWR {m n : ℕ} (ps : Fin m → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun u v =>
  if u = v then 0
  else (List.finRange m).foldl (fun acc j => acc + ps j u * ps j v) 0

/-- The Hebbian weight construction preserves enclosure. -/
theorem hebbW_encloses {m n : ℕ} {ps : Fin m → Fin n → FastReal}
    {psR : Fin m → Fin n → ℝ}
    (hp : ∀ j v, (ps j v).Encloses (psR j v)) (u v : Fin n) :
    (hebbW ps u v).Encloses (hebbWR psR u v) := by
  unfold hebbW hebbWR
  by_cases huv : u = v
  · rw [if_pos huv, if_pos huv]
    exact FastReal.encloses_zero
  · rw [if_neg huv, if_neg huv]
    apply FastReal.foldl_encloses _ _ _ _ FastReal.encloses_zero
    intro x r j _ hx
    exact FastReal.add_encloses hx (FastReal.mul_encloses (hp j u) (hp j v))

/-- The demo's stored patterns, over `ℝ`. -/
noncomputable def psR : Fin 2 → Fin 4 → ℝ := ![![1, 1, -1, -1], ![-1, 1, -1, 1]]

theorem ps_encloses : ∀ j v, (ps j v).Encloses (psR j v) := by
  intro j v
  fin_cases j <;> fin_cases v <;>
    first
      | exact FastReal.encloses_one
      | exact FastReal.neg_encloses FastReal.encloses_one

/-- The three states visited by the demo run, as `FastReal` literals. -/
def demoStates : List (Fin 4 → FastReal) :=
  [![1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, 1, -1, 1]]

/-- The same states over `ℝ`. -/
noncomputable def demoStatesR : List (Fin 4 → ℝ) :=
  [![1, -1, -1, 1], ![-1, -1, -1, 1], ![-1, 1, -1, 1]]

theorem demoStates_enclose :
    List.Forall₂ (fun a aR => ∀ v, (a v).Encloses (aR v)) demoStates demoStatesR := by
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil)) <;>
    intro v <;> fin_cases v <;>
      first
        | exact FastReal.encloses_one
        | exact FastReal.neg_encloses FastReal.encloses_one

/-- **The real Hebbian energies of the demo run descend** — obtained from
the executable certificate, with every hypothesis discharged. -/
theorem demo_real_descent :
    List.IsChain (fun a b => b ≤ a)
      (demoStatesR.map (fun aR => ER (hebbWR psR) (fun _ => 0) aR)) := by
  apply certified_descent_real (hebbW_encloses ps_encloses)
    (fun _ => FastReal.encloses_zero) demoStates_enclose
    (fuel := defaultFuel)
  decide

end FastEnergy

end Computable.Fast
