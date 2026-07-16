/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.FinCases

/-!
# A 3-neuron network test, executable over computable reals

A threshold network over a *specification* model of computable reals (a
quotient of regular Cauchy sequences, such as `Computable.CReal`) cannot be
executed: its activation needs `Decidable (0 ≤ input)`, which is undecidable
there. This file is the executable twin over `FastReal`, ported from the
`HopfieldNet` repository's `CReals/API/NNtest.lean` to the Quiver-based
`NeuralNetwork` structure of this repository.

Note that the second update of the first run hits the **exact tie**
`net = 0`: interval refinement alone could never decide it; the exact-point
branch of `FastReal.compare` does.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast.API.NNtest

/-- Weight matrix of the 3-neuron example network. -/
def M : Matrix (Fin 3) (Fin 3) FastReal :=
  Matrix.of ![![0, 0, 4], ![1, 0, 0], ![(-2), 3, 0]]

/-- The executable 3-neuron network: `{0,1}` activations via the fueled
binary threshold `binaryStep`. `pact` is trivial because this structure's
`hpact` quantifies over an arbitrary current activation (the fuel-exhaustion
fallback of `binaryStep` returns it); the runs below certify the fallback is
never taken. -/
abbrev NNtestF : NeuralNetwork FastReal (Fin 3) FastReal where
  Hom u v := PLift (M u v ≠ 0)
  Ui := {0, 1}
  Uo := {2}
  Uh := ∅
  hU := by ext x; fin_cases x <;> simp
  hUi := Set.Nonempty.ne_empty ⟨0, Set.mem_insert 0 {1}⟩
  hUo := Set.Nonempty.ne_empty ⟨2, rfl⟩
  hhio := Set.empty_inter _
  κ1 _ := 0
  κ2 _ := 1
  fnet _ w pred _ := w 0 * pred 0 + w 1 * pred 1 + w 2 * pred 2
  fact _ curr net _ := binaryStep curr net
  fout _ act := act
  m act := act
  pact _ := True
  pw _ _ _ := True
  pm _ := True
  hpact := by intros; trivial

/-- Parameters: weights `M`; the threshold (comparison against `0`) is baked
into `binaryStep`; `σ` and `θ` are unused. -/
def pF : Params NNtestF where
  h_arrows _ _ _ := trivial
  w := M
  σ _ := Vector.emptyWithCapacity 0
  θ _ := ⟨#[1], rfl⟩
  hw u v h := not_not.mp (fun hne => h ⟨⟨hne⟩, trivial⟩)
  hw' := trivial

/-- Initial state `[1, 0, 0]`. -/
def s0 : NNtestF.State where
  act := ![1, 0, 0]
  hp _ := trivial

lemma s0_onlyUi : s0.onlyUi := by
  refine ⟨0, fun u hu => ?_⟩
  fin_cases u
  · exact absurd (by simp) hu
  · exact absurd (by simp) hu
  · rfl

/-- Run the updates in `order` while checking that every activation
comparison was decided (`some _`) — i.e. that the `none` fallback of
`binaryStep` was never taken. -/
def decidedRun (s : NNtestF.State) (order : List (Fin 3)) : Bool × NNtestF.State :=
  order.foldl
    (fun acc u =>
      let net := acc.2.net pF u
      (acc.1 && (FastReal.compare net 0 defaultFuel).isSome, acc.2.Up pF u))
    (true, s)

/-! ## The runs -/

-- Asynchronous updates `u3, u1, u2, u3, u1, u2, u3` (balls, then as integers):
#eval List.ofFn (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 0, 1, 2, 0, 1, 2]).act
#eval actsToInts (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 0, 1, 2, 0, 1, 2]).act

-- Asynchronous updates `u3, u2, u1, u3, u2, u1, u3` (balls, then as integers):
#eval List.ofFn (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 1, 0, 2, 1, 0, 2]).act
#eval actsToInts (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 1, 0, 2, 1, 0, 2]).act

-- Decidedness certificates: every comparison during the runs was decided.
#eval (decidedRun s0 [2, 0, 1, 2, 0, 1, 2]).1  -- expect `true`
#eval (decidedRun s0 [2, 1, 0, 2, 1, 0, 2]).1  -- expect `true`

/-! ## Exact ties, demonstrated directly -/

#eval FastReal.compare ((2 : FastReal) - 2) 0 5   -- expect `some Ordering.eq`
#eval FastReal.compare ((1 : FastReal) + 1) 2 5   -- expect `some Ordering.eq`
#eval FastReal.compare (1 : FastReal) 2 5         -- expect `some Ordering.lt`

end Computable.Fast.API.NNtest
