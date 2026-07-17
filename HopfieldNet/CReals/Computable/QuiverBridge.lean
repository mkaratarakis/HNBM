/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.EnergySound
import HopfieldNet.Quiver.HN.Core

/-!
# Certified runs refine the real Hopfield network

The capstone of the refinement tower: a *certified* run of the executable
`HopfieldFast` network (every activation comparison decided) simulates, step
for step, the classical `HopfieldNetwork ℝ` dynamics — and therefore every
runtime certificate becomes a theorem about the real Quiver network, with
no manual state transcription.

* `signStep_sound` — a decided fueled sign-threshold computes exactly the
  classical `HNfact` decision `if θ ≤ net then 1 else -1` (as an enclosure);
* `net_encloses` — the executable field encloses the real `HNfnet` (via the
  zero diagonal, `HNfnet_eq`);
* `up_encloses` / `trace_encloses` — single updates and whole update
  traces preserve enclosure, given decidedness (`decidedSteps`);
* `netR_eq_sum`, `ER_eq_E` — the fold-defined `ℝ` twins agree with
  Mathlib-style `∑` sums and with the Quiver energy `NeuralNetwork.State.E`;
* `certified_run_energy_descent` — **the final theorem**: for enclosed
  parameters and initial states, a run whose comparisons are all decided
  and whose `FastReal` energies carry a `some true` descent certificate
  yields a non-increasing chain of the *real Quiver energies* `State.E`
  along the corresponding `HopfieldNetwork ℝ` trajectory.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastEnergy Finset

namespace Computable.Fast.QuiverBridge

/-! ## Decided threshold steps compute the classical decision -/

/-- A decided `signStep` computes the classical `if θ ≤ net then 1 else -1`
decision, as an enclosure. -/
theorem signStep_sound {net θv : FastReal} {netR θR : ℝ} {curr : FastReal}
    {fuel : ℕ} (hnet : net.Encloses netR) (hθ : θv.Encloses θR)
    (hdec : (FastReal.compare net θv fuel).isSome) :
    (signStep curr net θv fuel).Encloses (if θR ≤ netR then (1 : ℝ) else -1) := by
  cases hc : FastReal.compare net θv fuel with
  | none => rw [hc] at hdec; simp at hdec
  | some o =>
    have hs := FastReal.compare_sound hnet hθ hc
    unfold signStep
    rw [hc]
    cases o with
    | lt =>
      rw [if_neg (not_le.mpr hs)]
      exact FastReal.neg_encloses FastReal.encloses_one
    | eq =>
      rw [if_pos hs.ge]
      exact FastReal.encloses_one
    | gt =>
      rw [if_pos hs.le]
      exact FastReal.encloses_one

/-! ## Folds versus `∑` -/

section Sums

variable {M : Type} [AddCommMonoid M] {n : ℕ}

private lemma foldl_add_eq_sum {α : Type} (f : α → M) :
    ∀ (l : List α) (init : M),
      l.foldl (fun acc v => acc + f v) init = init + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a t ih => intro init; simp [ih, add_assoc]

/-- A `finRange` fold of additions is a `∑`. -/
theorem finRange_foldl_add_eq_sum (f : Fin n → M) :
    (List.finRange n).foldl (fun acc v => acc + f v) 0 = ∑ v, f v := by
  rw [foldl_add_eq_sum, zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

/-- A guarded `finRange` fold of additions is a filtered `∑`. -/
theorem finRange_foldl_ite_add_eq_sum (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → M) :
    (List.finRange n).foldl (fun acc v => if p v then acc + f v else acc) 0
      = ∑ v ∈ Finset.univ.filter p, f v := by
  have hfun : (fun (acc : M) v => if p v then acc + f v else acc)
      = fun acc v => acc + (if p v then f v else 0) := by
    funext acc v
    split <;> simp
  rw [hfun, finRange_foldl_add_eq_sum]
  exact (Finset.sum_filter _ _).symm

end Sums

/-! ## The fold twins agree with the Quiver energy -/

section QuiverEnergy

variable {n : ℕ} [NeZero n]

private instance : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_neZero n⟩⟩

theorem netR_eq_sum (wR : Matrix (Fin n) (Fin n) ℝ) (actR : Fin n → ℝ) (u : Fin n) :
    netR wR actR u = ∑ v ∈ Finset.univ.filter (fun v => v ≠ u), wR u v * actR v :=
  finRange_foldl_ite_add_eq_sum _ _

theorem EθR_eq_sum (θR actR : Fin n → ℝ) :
    EθR θR actR = ∑ u, θR u * actR u :=
  finRange_foldl_add_eq_sum _

/-- The fold-defined real energy is the Quiver Hopfield energy
`NeuralNetwork.State.E`. -/
theorem ER_eq_E (pR : Params (HopfieldNetwork ℝ (Fin n)))
    (st : (HopfieldNetwork ℝ (Fin n)).State) :
    ER pR.w (fun u => θ' (pR.θ u)) st.act = st.E pR := by
  unfold ER NeuralNetwork.State.E
  congr 1
  · -- weight part
    unfold EwR NeuralNetwork.State.Ew
    rw [finRange_foldl_add_eq_sum]
    have hsum : ∑ u, st.act u * netR pR.w st.act u
        = ∑ u, ∑ v ∈ Finset.univ.filter (fun v => v ≠ u), pR.w u v * st.act u * st.act v := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [netR_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsum]
    ring_nf
  · -- threshold part
    unfold NeuralNetwork.State.Eθ
    exact EθR_eq_sum _ _

end QuiverEnergy

/-! ## Certified runs simulate the real dynamics -/

section Simulation

variable {n : ℕ} [NeZero n]

private instance : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_neZero n⟩⟩

/-- Enclosure of parameters: weights componentwise, thresholds via the
single `κ2 = 1` entry. -/
def ParamsEnclose (pF : Params (HopfieldFast n))
    (pR : Params (HopfieldNetwork ℝ (Fin n))) : Prop :=
  (∀ u v, (pF.w u v).Encloses (pR.w u v)) ∧
    ∀ u, ((pF.θ u).get 0).Encloses (θ' (pR.θ u))

/-- The real Hopfield weights vanish on the diagonal (no self-loops). -/
theorem wR_diag_zero (pR : Params (HopfieldNetwork ℝ (Fin n))) (u : Fin n) :
    pR.w u u = 0 := by
  apply pR.hw u u
  rintro ⟨⟨h⟩, -⟩
  exact h rfl

/-- The executable field encloses the real `HNfnet` field. -/
theorem net_encloses {pF : Params (HopfieldFast n)}
    {pR : Params (HopfieldNetwork ℝ (Fin n))} (hp : ParamsEnclose pF pR)
    {s : (HopfieldFast n).State} {sR : (HopfieldNetwork ℝ (Fin n)).State}
    (hs : ∀ v, (s.act v).Encloses (sR.act v)) (u : Fin n) :
    (s.net pF u).Encloses (sR.net pR u) := by
  have hnetR : sR.net pR u
      = (List.finRange n).foldl (fun acc v => acc + pR.w u v * sR.act v) 0 := by
    show HNfnet u (pR.w u) (fun v => sR.out v) = _
    rw [HNfnet_eq u (pR.w u) _ (wR_diag_zero pR u), finRange_foldl_add_eq_sum]
    rfl
  rw [hnetR]
  show ((List.finRange n).foldl (fun acc v => acc + pF.w u v * s.act v) 0).Encloses _
  apply FastReal.foldl_encloses _ _ _ _ FastReal.encloses_zero
  intro x r v _ hx
  exact FastReal.add_encloses hx (FastReal.mul_encloses (hp.1 u v) (hs v))

/-- A decided single-site update preserves enclosure of the whole state. -/
theorem up_encloses {pF : Params (HopfieldFast n)}
    {pR : Params (HopfieldNetwork ℝ (Fin n))} (hp : ParamsEnclose pF pR)
    {s : (HopfieldFast n).State} {sR : (HopfieldNetwork ℝ (Fin n)).State}
    (hs : ∀ v, (s.act v).Encloses (sR.act v)) (u : Fin n)
    (hdec : (FastReal.compare (s.net pF u) ((pF.θ u).get 0) defaultFuel).isSome) :
    ∀ v, (((s.Up pF u).act v)).Encloses ((sR.Up pR u).act v) := by
  intro v
  show (if v = u then _ else s.act v).Encloses (if v = u then _ else sR.act v)
  by_cases hv : v = u
  · rw [if_pos hv, if_pos hv]
    exact signStep_sound (net_encloses hp hs u) (hp.2 u) hdec
  · rw [if_neg hv, if_neg hv]
    exact hs v

/-- Executable decidedness certificate for a whole asynchronous run: every
threshold comparison along `order` returns `some _`. -/
def decidedSteps (p : Params (HopfieldFast n)) :
    (HopfieldFast n).State → List (Fin n) → Bool
  | _, [] => true
  | s, u :: rest =>
    (FastReal.compare (s.net p u) ((p.θ u).get 0) defaultFuel).isSome &&
      decidedSteps p (s.Up p u) rest

/-- **Certified runs simulate the real dynamics**: given enclosed
parameters and initial states and a decided run, every state along the
trace (prefix folds, initial state included) encloses the corresponding
state of the `HopfieldNetwork ℝ` trajectory. -/
theorem trace_encloses {pF : Params (HopfieldFast n)}
    {pR : Params (HopfieldNetwork ℝ (Fin n))} (hp : ParamsEnclose pF pR) :
    ∀ (order : List (Fin n)) (s : (HopfieldFast n).State)
      (sR : (HopfieldNetwork ℝ (Fin n)).State),
      (∀ v, (s.act v).Encloses (sR.act v)) →
      decidedSteps pF s order = true →
      List.Forall₂ (fun a aR => ∀ v, (a v).Encloses (aR v))
        ((order.inits).map (fun pre => (pre.foldl (fun st u => st.Up pF u) s).act))
        ((order.inits).map (fun pre => (pre.foldl (fun st u => st.Up pR u) sR).act)) := by
  intro order
  induction order with
  | nil =>
    intro s sR hs _
    exact List.Forall₂.cons hs List.Forall₂.nil
  | cons a t ih =>
    intro s sR hs hdec
    have hparts := (Bool.and_eq_true _ _).mp (by simpa [decidedSteps] using hdec)
    simp only [List.inits_cons, List.map_cons, List.map_map, List.foldl_nil,
      Function.comp_def, List.foldl_cons]
    exact List.Forall₂.cons hs
      (ih (s.Up pF a) (sR.Up pR a) (up_encloses hp hs a hparts.1) hparts.2)

/-- **The final theorem.** For enclosed parameters and initial states, a
run whose threshold comparisons are all decided (`decidedSteps`) and whose
`FastReal` energies carry a `some true` descent certificate yields a
non-increasing chain of the real Quiver energies `NeuralNetwork.State.E`
along the corresponding `HopfieldNetwork ℝ` trajectory. -/
theorem certified_run_energy_descent {pF : Params (HopfieldFast n)}
    {pR : Params (HopfieldNetwork ℝ (Fin n))} (hp : ParamsEnclose pF pR)
    {s : (HopfieldFast n).State} {sR : (HopfieldNetwork ℝ (Fin n)).State}
    (hs : ∀ v, (s.act v).Encloses (sR.act v)) (order : List (Fin n))
    (hdec : decidedSteps pF s order = true)
    (hcert : descentCertified?
      (((order.inits).map
        (fun pre => (pre.foldl (fun st u => st.Up pF u) s).act)).map
        (fun a => EF pF.w (fun u => (pF.θ u).get 0) a)) defaultFuel = some true) :
    List.IsChain (fun a b => b ≤ a)
      ((order.inits).map
        (fun pre => (pre.foldl (fun st u => st.Up pR u) sR).E pR)) := by
  have h := certified_descent_real hp.1 hp.2 (trace_encloses hp order s sR hs hdec) hcert
  rw [List.map_map] at h
  have hfun : (fun pre => ((pre.foldl (fun st u => st.Up pR u) sR)).E pR)
      = fun pre : List (Fin n) =>
          ER pR.w (fun u => θ' (pR.θ u)) ((pre.foldl (fun st u => st.Up pR u) sR).act) :=
    funext fun pre => (ER_eq_E pR _).symm
  rw [hfun]
  simpa [Function.comp_def] using h

end Simulation

end Computable.Fast.QuiverBridge
