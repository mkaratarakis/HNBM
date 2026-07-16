/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.FinCases

/-!
# The Hopfield-network test (`HNtest`), executable over computable reals

The `ℚ` test builds a 4-neuron Hopfield network with Hebbian weights from
the patterns `[1,1,-1,-1]` and `[-1,1,-1,1]`, stabilizes the initial state
`[1,-1,-1,1]` under the cyclic update sequence and reports the stable state
(`[-1,1,-1,1]`) and the number of steps to convergence (`2`).

This file performs the same computation over `FastReal`, on the Quiver-based
`NeuralNetwork` structure of this repository. Since a decidable order on
computable reals cannot exist, stabilization is fuel-based (`API.stabilizeF`)
and returns a certificate that stability was *decided* (every comparison
returned `some _`), not assumed.

Unlike `ℚ`'s `HopfieldNetwork` (whose `pact` is `act = 1 ∨ act = -1`), `pact`
here is trivial: this structure's `hpact` quantifies over an arbitrary
current activation, which the fuel-exhaustion fallback of `signStep` returns.
The runs below certify the fallback is never taken, so all activations do
remain `±1` — as facts about the run, not as a type-level invariant.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast.API.HNtest

/-- Hopfield network over `FastReal` on `n` neurons: complete graph, `±1`
activations, fueled sign-threshold activation `signStep` with threshold
`θ` (the single entry of the `κ2 = 1` parameter vector). -/
abbrev HopfieldFast (n : ℕ) [NeZero n] : NeuralNetwork FastReal (Fin n) FastReal where
  Hom u v := PLift (u ≠ v)
  Ui := Set.univ
  Uo := Set.univ
  Uh := ∅
  hU := by simp
  hUi := Ne.symm Set.empty_ne_univ
  hUo := Ne.symm Set.empty_ne_univ
  hhio := Set.empty_inter _
  κ1 _ := 0
  κ2 _ := 1
  fnet _ w pred _ := (List.finRange n).foldl (fun acc v => acc + w v * pred v) 0
  fact _ curr net θv := signStep curr net (θv.get 0)
  fout _ act := act
  m act := act
  pact _ := True
  pw _ _ _ := True
  pm _ := True
  hpact := by intros; trivial

/-- Hebbian weight matrix over `FastReal`: `w u v = ∑ j, ps j u * ps j v`
off the diagonal, `0` on it (as in the `ℚ` `Hebbian`, whose diagonal
subtraction zeroes self-weights). -/
def hebbW {m n : ℕ} (ps : Fin m → Fin n → FastReal) :
    Matrix (Fin n) (Fin n) FastReal := fun u v =>
  if u = v then 0
  else (List.finRange m).foldl (fun acc j => acc + ps j u * ps j v) 0

/-- Hebbian parameters (thresholds `0`) for `HopfieldFast n`. -/
def hebbParams {m n : ℕ} [NeZero n] (ps : Fin m → Fin n → FastReal) :
    Params (HopfieldFast n) where
  h_arrows _ _ _ := trivial
  w := hebbW ps
  σ _ := Vector.emptyWithCapacity 0
  θ _ := ⟨#[0], rfl⟩
  hw u v h := by
    have huv : u = v := not_not.mp (fun hne => h ⟨⟨hne⟩, trivial⟩)
    subst huv
    unfold hebbW
    rw [if_pos rfl]
    rfl
  hw' := trivial

/-- The two stored patterns of the `ℚ` test: `[1,1,-1,-1]` and `[-1,1,-1,1]`. -/
def ps : Fin 2 → Fin 4 → FastReal := ![![1, 1, -1, -1], ![-1, 1, -1, 1]]

/-- The test parameters: Hebbian weights from `ps`. -/
def pH : Params (HopfieldFast 4) := hebbParams ps

/-- Initial state `[1,-1,-1,1]`, as in the `ℚ` test. -/
def extu : (HopfieldFast 4).State where
  act := ![1, -1, -1, 1]
  hp _ := trivial

/-! ## The computations

The `ℚ` originals are
`#eval HopfieldNet_stabilize test_params extu (useq_Fin 4) …` (stable state
`[-1, 1, -1, 1]`) and `#eval HopfieldNet_conv_time_steps …` (`2`).
-/

/-- The stabilization run: `(final state, steps, certified-stable)`. -/
def run : (HopfieldFast 4).State × ℕ × Bool := stabilizeF pH 64 extu

-- The stable state, as integers: expect `some [-1, 1, -1, 1]`.
#eval actsToInts run.1.act

-- The stable state, as balls.
#eval List.ofFn run.1.act

-- Steps to convergence (twin of `HopfieldNet_conv_time_steps`): expect `2`.
#eval run.2.1

-- Certificate: stability was *decided* (no comparison ran out of fuel): expect `true`.
#eval run.2.2

-- Sanity: the initial state is provably not stable, decidedly so.
#eval isStableF pH extu  -- expect `some false`

-- Each stored pattern is a fixed point of the dynamics: expect `some true` twice.
#eval isStableF pH ⟨![1, 1, -1, -1], fun _ => trivial⟩
#eval isStableF pH ⟨![-1, 1, -1, 1], fun _ => trivial⟩

end Computable.Fast.API.HNtest
