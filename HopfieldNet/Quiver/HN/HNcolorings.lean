/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.Quiver.HN.HNtest
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.FinEnum
import Mathlib.Data.List.GetD

/-!
# Computing graph colorings with a Hopfield network

This file is a *runnable* demonstration that the discrete deterministic Hopfield
network (over `ℚ`, hence computable — see `HNtest.lean`) can be used for graph
coloring, framed as **energy-based associative memory**:

* A proper `K`-coloring of a graph on `N` nodes is encoded as a one-hot `{±1}`
  activation pattern over `N × K` neurons: for each node exactly one
  "node-uses-color-`c`" neuron is `+1`, the rest `-1`.
* `Hebbian` makes a chosen proper coloring a **stable state / energy minimum**
  (an attractor) of the network.
* Running the deterministic dynamics (`HopfieldNet_stabilize`) from a *corrupted*
  configuration performs energy descent and **recovers** the coloring.
* `isProperColoring` is a *computable* checker (decodes the one-hot pattern and
  tests the edge constraints), so we can `#eval`-verify that the recovered state
  really is a proper coloring.

We work out a concrete instance: the 4-cycle `C₄` (`0-1-2-3-0`), which is
2-colorable (`N = 4`, `K = 2`, so `N*K = 8` neurons). Neuron index
`i = 2*node + color`; `act i = 1` means "node uses that color".

## Scope / honesty

This demonstrates the *recall / verification* use, which the proved `ℚ`
machinery supports directly. Solving an *arbitrary* coloring instance from
scratch by pure deterministic descent is only a **heuristic** (it can get stuck
in spurious local minima); the principled solver for that is the stochastic
Boltzmann machine with annealing. What is unconditionally true and shown here:
proper colorings are stable states of the encoding, and energy descent recovers
them. -/

open Mathlib Finset NeuralNetwork

namespace HNColoring

/-! ### The instance: the 4-cycle `C₄`, 2 colors (8 neurons)

The graph itself is mathlib's `SimpleGraph.cycleGraph 4 : SimpleGraph (Fin 4)`
(adjacency `a - b = 1 ∨ b - a = 1` in `Fin 4`, i.e. `0-1-2-3-0`); it comes with a
`DecidableRel · .Adj` instance, so the edge constraints are checkable. -/

/-- The graph to color: the 4-cycle, taken from mathlib. -/
abbrev G : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

/-- A proper 2-coloring of `C₄`: nodes `0,2 ↦ color 0`; nodes `1,3 ↦ color 1`.
As a one-hot `{±1}` pattern over the `8` neurons
`(n0c0, n0c1, n1c0, n1c1, n2c0, n2c1, n3c0, n3c1)`. -/
def coloringPattern : Fin 8 → ℚ := ![1, -1,  -1, 1,  1, -1,  -1, 1]

/-- The proper coloring as a Hopfield-network state (the target attractor). -/
def colorState : (HopfieldNetwork ℚ (Fin 8)).State where
  act := coloringPattern
  hp := by intro u; unfold HopfieldNetwork; simp only; revert u; decide

/-- A *corrupted* input: the proper coloring with neuron `0` flipped
(`+1 ↦ -1`). Now node `0` has no color selected — not a valid coloring. -/
def noisyStart : (HopfieldNetwork ℚ (Fin 8)).State where
  act := ![-1, -1,  -1, 1,  1, -1,  -1, 1]
  hp := by intro u; unfold HopfieldNetwork; simp only; revert u; decide

/-- Hebbian weights that make `colorState` an energy minimum (attractor). -/
def colorParams : Params (HopfieldNetwork ℚ (Fin 8)) :=
  Hebbian (fun _ : Fin 1 => colorState)

/-- Energy descent from the corrupted input: the recovered stable state. -/
def recalled : (HopfieldNetwork ℚ (Fin 8)).State :=
  HopfieldNet_stabilize colorParams noisyStart (useq_Fin 8) (useq_Fin_fair 8)

/-! ### Computable decoding and proper-coloring checker -/

/-- Decode the color of node `v` from a `{±1}` activation list:
returns `0` or `1` if node `v` is one-hot, else `-1` (invalid / not one-hot). -/
def colorOf (L : List ℚ) (v : Nat) : Int :=
  let a := L.getD (2 * v) 0
  let b := L.getD (2 * v + 1) 0
  if a = 1 ∧ b = -1 then 0
  else if a = -1 ∧ b = 1 then 1
  else -1

/-- Computable check: a state's activation list encodes a proper coloring of `G`
— every node is one-hot, and every `G`-adjacent pair gets different colors.
The edge constraint is read directly off mathlib's `G.Adj` (decidable). -/
def isProperColoring (L : List ℚ) : Bool :=
  let cols : List Int := (List.range 4).map (colorOf L)
  cols.all (fun x => decide (x ≠ -1)) &&
    (List.finRange 4).all (fun u => (List.finRange 4).all (fun v =>
      if G.Adj u v then decide (cols.getD u.val (-2) ≠ cols.getD v.val (-2)) else true))

/-! ### Pretty-printing and the actual computations -/

instance : Repr ((HopfieldNetwork ℚ (Fin 8)).State) where
  reprPrec s _ := "act: " ++ repr (List.ofFn s.act)

-- The corrupted input is *not* a proper coloring (node 0 has no color).
#eval isProperColoring (List.ofFn noisyStart.act)   -- expect: false

-- The network recovers a configuration ...
#eval recalled                                      -- expect: the coloring pattern

-- ... which *is* a proper coloring, verified computably.
#eval isProperColoring (List.ofFn recalled.act)     -- expect: true

-- The recovered proper coloring sits at lower energy than the corrupted input
-- (energy descent did its job).
#eval recalled.E colorParams                        -- energy of the recovered state
#eval noisyStart.E colorParams                      -- energy of the corrupted input

end HNColoring

/-! ## A generic coloring attempt for *any* finite graph

Given any `Gph : SimpleGraph V` on a finite vertex set and a number of colors
`K`, we build a Hopfield network on the `V × Fin K` neurons whose energy
penalizes (i) two colors active on the same node and (ii) the same color on two
adjacent nodes, then run synchronous-by-site sweeps of the deterministic update
and decode the result.

This is a **heuristic**: deterministic energy descent can stall in a spurious
local minimum, so `attemptColoring` is not guaranteed to return a proper
coloring. `isProperColoring?` reports, computably, whether a given attempt
actually succeeded. -/

namespace HNColoringGen

open NeuralNetwork SimpleGraph

set_option linter.unusedSectionVars false

/-- A nonempty palette: `NeZero K` makes `0 : Fin K` available. -/
instance instNonemptyFin {K : ℕ} [NeZero K] : Nonempty (Fin K) := ⟨0⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Symmetric, zero-diagonal coupling encoding the coloring constraints:
`-A` between two colors of the *same node* (one-hot pressure), `-B` between the
*same color* on two *adjacent* nodes (proper-coloring pressure). -/
def cw (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ)
    (p q : V × Fin K) : ℚ :=
  (if p ≠ q ∧ p.1 = q.1 then -A else 0) +
  (if p.2 = q.2 ∧ Gph.Adj p.1 q.1 then -B else 0)

lemma cw_symm (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ)
    (p q : V × Fin K) : cw Gph K A B p q = cw Gph K A B q p := by
  have e1 : (p ≠ q ∧ p.1 = q.1) ↔ (q ≠ p ∧ q.1 = p.1) :=
    ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2.symm⟩⟩
  have e2 : (p.2 = q.2 ∧ Gph.Adj p.1 q.1) ↔ (q.2 = p.2 ∧ Gph.Adj q.1 p.1) :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  unfold cw
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]

lemma cw_diag (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ)
    (p : V × Fin K) : cw Gph K A B p p = 0 := by
  unfold cw
  rw [if_neg (by simp), if_neg (by simp [SimpleGraph.irrefl])]; ring

/-- The Hopfield parameters encoding `Gph`-coloring with `K` colors. -/
def colorParams (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) [Nonempty V] [NeZero K]
    (A B : ℚ) : Params (HopfieldNetwork ℚ (V × Fin K)) where
  h_arrows := fun _ _ _ => trivial
  w := cw Gph K A B
  σ := fun _ => Vector.emptyWithCapacity 0
  θ := fun _ => ⟨#[0], by simp only [List.size_toArray, List.length_cons, List.length_nil,
    zero_add]⟩
  hw := by
    intro u v h
    have huv : u = v := HopfieldNetwork.eq_of_not_pwMat u v h
    subst huv
    exact cw_diag Gph K A B u
  hw' := by
    ext i j
    simp only [Matrix.transpose_apply]
    exact cw_symm Gph K A B j i

/-! ### Executable dynamics on a materialized configuration

`colorParams` above is a genuine `Params (HopfieldNetwork …)`: it shows the
encoding is a real Hopfield network (symmetric, zero-diagonal couplings). For
*execution* we run that network's own dynamics — couplings `cw`, threshold rule
`act := if 0 ≤ net then 1 else -1` — on a flat `(neuron, activation)` table that
is fully materialized at every step (so `#eval` stays fast; iterating the
closure-based `State.Up` is exponential to evaluate). Updates are **synchronous**
(all sites at once), the natural mode for parallel/photonic hardware. -/

/-- A materialized configuration: each neuron paired with its `{±1}` activation. -/
abbrev Cfg (V : Type) (K : ℕ) := List ((V × Fin K) × ℚ)

/-- Look up a neuron's activation. -/
def actOf (K : ℕ) (cfg : Cfg V K) (p : V × Fin K) : ℚ :=
  ((cfg.find? (fun pr => decide (pr.1 = p))).map Prod.snd).getD 0

/-- Local field at `p`: `∑_{q ≠ p} w_{pq} · act_q` with `w = cw` (the HN couplings). -/
def netP (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ)
    (cfg : Cfg V K) (p : V × Fin K) : ℚ :=
  (cfg.map (fun pr => if pr.1 = p then 0 else cw Gph K A B p pr.1 * pr.2)).sum

/-- One synchronous sweep applying the Hopfield threshold rule at every neuron. -/
def sweepCfg (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ)
    (cfg : Cfg V K) : Cfg V K :=
  cfg.map (fun pr => (pr.1, if 0 ≤ netP Gph K A B cfg pr.1 then 1 else -1))

/-- All nodes start on color `0` (a hard symmetric start). -/
def initMono (K : ℕ) [FinEnum V] [NeZero K] : Cfg V K :=
  (FinEnum.toList (V × Fin K)).map (fun u => (u, if u.2 = 0 then 1 else -1))

/-- Symmetry-breaking start: node of rank `r` begins on color `r % K`. -/
def initRainbow (K : ℕ) [FinEnum V] [NeZero K] : Cfg V K :=
  (FinEnum.toList (V × Fin K)).map
    (fun u => (u, if u.2.val = (FinEnum.equiv u.1).val % K then 1 else -1))

/-- The coloring attempt: `T` synchronous sweeps from `init`. -/
def attemptColoring (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) (A B : ℚ) (T : ℕ)
    (init : Cfg V K) : Cfg V K :=
  (sweepCfg Gph K A B)^[T] init

/-- Computable proper-coloring check: every node one-hot, adjacent nodes share no
active color. Pure `List` operations, fast under `#eval`. -/
def isProperColoring? (Gph : SimpleGraph V) [DecidableRel Gph.Adj] (K : ℕ) [FinEnum V]
    (cfg : Cfg V K) : Bool :=
  let nodes := FinEnum.toList V
  let colors := FinEnum.toList (Fin K)
  nodes.all (fun v => (colors.filter (fun c => decide (actOf K cfg (v, c) = 1))).length == 1) &&
  nodes.all (fun u => nodes.all (fun v =>
    if Gph.Adj u v then
      colors.all (fun c => !(decide (actOf K cfg (u, c) = 1) && decide (actOf K cfg (v, c) = 1)))
    else true))

/-! ### Demonstrations on mathlib graphs

These `#eval`s show both the power and the limits of deterministic descent —
exactly why the stochastic Boltzmann machine is the principled solver:

* **`true`** — 2-coloring of `C₄` from a symmetry-broken start: succeeds.
* **`false` (bad start)** — same graph from the all-same start: stuck in a
  spurious minimum. A heuristic depends on initialization.
* **`false` (K ≥ 3)** — for `K ≥ 3` the `{±1}` one-hot winner-take-all leaves an
  off-color with local field `0`, so spurious colors switch on; deterministic
  `{±1}` descent does not reliably handle `K ≥ 3`. Escaping these failure modes
  needs annealing (the Boltzmann machine), not a sharper threshold. -/

open SimpleGraph in
-- 4-cycle, 2 colors, symmetry-broken start: succeeds → true.
#eval isProperColoring? (cycleGraph 4) 2 (attemptColoring (cycleGraph 4) 2 3 1 8 (initRainbow 2))

open SimpleGraph in
-- 4-cycle, 2 colors, all-same start: stuck → false.
#eval isProperColoring? (cycleGraph 4) 2 (attemptColoring (cycleGraph 4) 2 3 1 8 (initMono 2))

open SimpleGraph in
-- Triangle K₃ (= cycleGraph 3), 3 colors: K ≥ 3 failure mode → false.
#eval isProperColoring? (cycleGraph 3) 3 (attemptColoring (cycleGraph 3) 3 3 1 8 (initRainbow 3))

open SimpleGraph in
-- 5-cycle (odd), 3 colors: K ≥ 3 failure mode → false.
#eval isProperColoring? (cycleGraph 5) 3 (attemptColoring (cycleGraph 5) 3 3 1 8 (initRainbow 3))

end HNColoringGen
