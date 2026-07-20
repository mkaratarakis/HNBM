/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic
import Mathlib.Tactic.FinCases

/-!
# The 3-neuron network test, executable over computable reals

The `FastReal` twin of `HopfieldNet/Quiver/NeuralNetwork/test.lean`: the same
3-neuron network (weight matrix `![![0,0,4], ![1,0,0], ![-2,3,0]]` as the
source of truth for both weights and topology, inputs `{0,1}`, output `{2}`,
binary `{0,1}` activations with threshold `1`), the same initial state
`[1,0,0]`, and the same two asynchronous update sequences with their full
per-step traces — but with weights and net inputs computed in ball arithmetic
over dyadics instead of `ℚ`.

Activations stay in `ℤ` exactly as in the `ℚ` file (so states print exactly
and `decide` proofs still work); only `fnet`'s arithmetic and the threshold
comparison move to `FastReal`. Since `≤` on computable reals is undecidable,
the `ℚ` activation `if input ≥ θ.get 0 then 1 else 0` becomes the fueled
`stepFact`, which keeps the current activation if the comparison is undecided
within fuel. The second run hits the **exact tie** `net = θ = 1` when neuron
`1` fires: interval refinement alone could never decide it; the exact-point
branch of `FastReal.compare` does. `decidedRun` certifies that no comparison
in either run took the fuel-exhaustion fallback.
-/

open Finset Computable.Fast Computable.Fast.API

-- `#eval` code generation unfolds the `FastReal` ball arithmetic, which is
-- much deeper than the `ℚ` original's.
set_option maxRecDepth 4096

namespace Computable.Fast.API.NNtest

/-- Fueled twin of the `ℚ` activation `if input ≥ θ then 1 else 0`: `1` if
`θ ≤ input`, `0` if `input < θ`, current activation if undecided within
fuel. -/
def stepFact (curr : ℤ) (input θ : FastReal) (fuel : ℕ := defaultFuel) : ℤ :=
  match FastReal.compare input θ fuel with
  | some Ordering.lt => 0
  | some _ => 1
  | none => curr

/-- We keep the Matrix as the source of truth for both weights and topology. -/
def test.M : Matrix (Fin 3) (Fin 3) FastReal :=
  Matrix.of ![![0,0,4], ![1,0,0], ![(-2),3,0]]

/-- We construct the NeuralNetwork instance. Note that we define 'Hom' here
  to satisfy the Quiver extension. -/
def test : NeuralNetwork FastReal (Fin 3) ℤ := {
  -- We define an arrow existing only if the matrix value is non-zero.
  Hom := fun u v => PLift (test.M u v ≠ 0)

  -- B. Architecture (Sets)
  Ui := {0,1}
  Uo := {2}
  Uh := ∅

  -- C. Proofs of Architecture
  hUi := Set.Nonempty.ne_empty ⟨0, Set.mem_insert 0 {1}⟩
  hUo := Set.Nonempty.ne_empty ⟨2, rfl⟩
  hU := by ext x; fin_cases x <;> simp
  hhio := Set.empty_inter _
  κ1 := fun _ => 0
  κ2 := fun _ => 1
  -- `∑ v, w v * pred v` in the `ℚ` file; `FastReal` has no `AddCommMonoid`
  -- instance, so the sum is a fold.
  fnet := fun _ w pred _ => (List.finRange 3).foldl (fun acc v => acc + w v * pred v) 0
  fact := fun _ curr input θ => stepFact curr input (θ.get 0)
  fout := fun _ act => FastReal.ofDyadic ⟨act, 0⟩
  pact := fun _ => True
  pw := fun _ _ _ => True -- We accept any arrow defined by our Hom
  hpact := by intros; trivial
  pwMat := fun u v => (test.M u v ≠ 0)
  pm := fun _ => True
  m := fun _ => 0
}

def wθ : Params test where
  h_arrows := fun _ _ _ => trivial
  w := test.M
  θ := fun _ => ⟨#[1], rfl⟩
  σ := fun _ => Vector.emptyWithCapacity 0
  hw := fun u v h => by
    unfold test at h
    simp only [ne_eq, not_not] at h
    exact h
  hw' := trivial

-- Helper for printing
instance : Repr test.State where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

-- Initial State
def test.extu : test.State := {
  act := ![1,0,0],
  hp := fun _ => trivial
}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

-- Proof that initial state respects input neuron constraints
lemma test.onlyUi : test.extu.onlyUi := by {
  constructor
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu
}

-- Show the state after *each* asynchronous neuron update (not only the final state).

def test.seq : List (Fin 3) := [2,0,1,2,0,1,2]

/-- States after running `workPhase` on every prefix of `test.seq`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace : List test.State :=
  (test.seq.inits).map (fun pref =>
    NeuralNetwork.State.workPhase wθ test.extu test.onlyUi pref
  )

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled : List ((Fin 3) × test.State) :=
  List.zip test.seq (test.workPhaseTrace.drop 1)

-- Each step: (neuron updated, resulting state)
#eval test.workPhaseTraceLabeled

-- The workphase for the asynchronous update of the sequence of neurons u3, u2, u1, u3, u2, u1, u3

def test.seq' : List (Fin 3) := [2,1,0,2,1,0,2]

/-- States after running `workPhase` on every prefix of `test.seq'`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace' : List test.State :=
  (test.seq'.inits).map (fun pref =>
    NeuralNetwork.State.workPhase wθ test.extu test.onlyUi pref
  )

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled' : List ((Fin 3) × test.State) :=
  List.zip test.seq' (test.workPhaseTrace'.drop 1)

#eval test.workPhaseTraceLabeled'

/-! ## Decidedness certificates -/

/-- Run the updates in `order` while checking that every threshold
comparison was decided (`some _`) — i.e. that the fuel-exhaustion fallback of
`stepFact` was never taken. -/
def decidedRun (s : test.State) (order : List (Fin 3)) : Bool × test.State :=
  order.foldl
    (fun acc u =>
      let net := acc.2.net wθ u
      (acc.1 && (FastReal.compare net ((wθ.θ u).get ⟨0, Nat.zero_lt_one⟩) defaultFuel).isSome,
        acc.2.Up wθ u))
    (true, s)

-- Every comparison during both runs was decided — including the exact tie
-- `net = θ = 1` in the second run.
#eval (decidedRun test.extu test.seq).1   -- expect `true`
#eval (decidedRun test.extu test.seq').1  -- expect `true`

end Computable.Fast.API.NNtest
