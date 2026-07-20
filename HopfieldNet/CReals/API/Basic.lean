/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.Quiver.NeuralNetwork.Main
import ComputableReals.Decision

/-!
# Minimal API: neural-network computations over computable reals

This folder is the minimal executable surface for running the repository's
neural-network tests over **computable reals** (`Computable.Fast.FastReal`,
ball arithmetic over dyadics) instead of `ℚ`.

Comparison of computable reals is undecidable, so a `Decidable (θ ≤ net)`
instance — what the `ℚ` dynamics use — cannot exist. Instead:

* activations are computed with the total, fuel-based `FastReal.compare`:
  balls either separate (strict inequality), are exact radius-`0` points and
  get compared exactly (this decides *ties* such as `net = θ`), or fuel runs
  out and the neuron keeps its current activation;
* every run can be accompanied by an executable **decidedness certificate**
  showing the fuel-exhaustion fallback was never taken (`isStableF`,
  `stabilizeF` report this, `NNtest.decidedRun` checks it per update);
* with integer/dyadic weights and `{0,1}` or `{±1}` activations, every net
  input is an exact dyadic, so every comparison — ties included — is decided
  at the first probe.

`Basic.lean` provides the shared helpers and a generic fueled stabilization
loop for any `NeuralNetwork FastReal (Fin n) FastReal` (the Quiver-based
structure of this repository, instantiated with `FastReal` weights *and*
activations); `NNtest.lean` and `HNtest.lean` port the two test suites.
-/

open Computable.Fast

namespace Computable.Fast.API

variable {n : ℕ} {NN : NeuralNetwork FastReal (Fin n) FastReal}

/-- Fueled stability test: `some true` iff every neuron's update provably
keeps its activation (all comparisons decided). `none` propagation means the
answer is honest — we never claim stability from an undecided comparison. -/
def isStableF (p : Params NN) (s : NN.State) (fuel : ℕ := defaultFuel) :
    Option Bool :=
  (List.finRange n).foldl
    (fun acc u => do
      let b ← acc
      let e ← eqF ((s.Up p u).act u) (s.act u) fuel
      pure (b && e))
    (some true)

/-- Fueled stabilization along the cyclic update sequence `0, 1, …, n-1, 0, …`
(the twin of `ℚ`'s `HopfieldNet_stabilize` with `useq_Fin`).

Returns `(final state, steps taken, certified)`. `certified = true` means the
loop stopped because `isStableF` returned `some true` — i.e. the state is
provably stable with every comparison decided; `false` means `maxSteps` ran
out first. The step count is the twin of `HopfieldNet_conv_time_steps`. -/
def stabilizeF [NeZero n] (p : Params NN) (maxSteps : ℕ) (s : NN.State)
    (steps : ℕ := 0) (fuel : ℕ := defaultFuel) : NN.State × ℕ × Bool :=
  match maxSteps with
  | 0 => (s, steps, false)
  | maxSteps' + 1 =>
    if isStableF p s fuel = some true then
      (s, steps, true)
    else
      stabilizeF p maxSteps'
        (s.Up p ⟨steps % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩)
        (steps + 1) fuel

end Computable.Fast.API
