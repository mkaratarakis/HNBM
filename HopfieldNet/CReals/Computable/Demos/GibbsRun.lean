/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.FastLogistic

/-!
# Demo: a multi-sweep Gibbs chain on a *trained* Hopfield/Boltzmann network

Everything here **runs** (`#eval`) — it drives the executable positive-temperature
Gibbs sampler of `FastLogistic` on the Hebbian weight matrix trained (by the Hebb
rule) on the two patterns `[1,1,-1,-1]` and `[-1,1,-1,1]` (`FastEnergy.hebbW ps`).

What the demo verifies, all by evaluation:

* **Denoising / recall.** Starting from a *corrupted* stored pattern, a chain of
  full Gibbs sweeps at low temperature (large `β`) walks back to the stored
  pattern, and the Hopfield energy along the sampled chain settles to the
  pattern's minimum `-4`.
* **Temperature matters.** At `β = 0` (infinite temperature) every site is a fair
  coin, so the same start under the same samples is driven purely by the samples,
  not the weights — the sampler is honest about this.
* **Soundness backing.** These are the very `gibbsSweep?`/`probPos?` combinators
  whose `…Sound` twins in `Computable/ExpSound.lean` prove the sampled chain
  *is* the classical `ℝ`-valued Gibbs chain, sample for sample.
-/

open Computable.Fast Computable.Fast.API
open Computable.Fast.FastEnergy Computable.Fast.FastLogistic

set_option maxRecDepth 4096

namespace Computable.Fast.Demos.GibbsRun

/-- One full sweep over sites `0,…,n-1`, each driven by the *same* dyadic
sample `r`. -/
def sweepAll {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β : FastReal) (r : Dyadic) (act : Fin n → FastReal)
    (fuel : ℕ := defaultFuel) : Option (Fin n → FastReal) :=
  gibbsSweep? w θ κ β ((List.finRange n).map (fun u => (u, r))) act fuel

/-- Run `sweeps` full sweeps (sample `r` per site) and return the state *trace*:
the initial state, then the state after each sweep. -/
def gibbsTrace? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β : FastReal) (r : Dyadic) (fuel : ℕ) :
    ℕ → (Fin n → FastReal) → Option (List (Fin n → FastReal))
  | 0, act => some [act]
  | k + 1, act => do
    let act' ← sweepAll w θ κ β r act fuel
    let tl ← gibbsTrace? w θ κ β r fuel k act'
    pure (act :: tl)

/-- The trace, rendered as integer `±1` states for readable output. -/
def traceInts {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β : FastReal) (r : Dyadic) (sweeps : ℕ) (act : Fin n → FastReal) :
    Option (List (List Int)) := do
  let tr ← gibbsTrace? w θ κ β r (2 * n + 4) sweeps act
  tr.mapM actsToInts

/-- Hopfield energy along a trace (thresholds `0`). -/
def traceEnergies {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal)
    (tr : List (Fin n → FastReal)) : List FastReal :=
  tr.map (fun s => EF w (fun _ => 0) s)

/-! ## The computations

`W = hebbW ps` is the Hebbian matrix trained on `[1,1,-1,-1]` and `[-1,1,-1,1]`;
`κ = 2` (the `±1` two-state scale), thresholds `0`. -/

/-- Corrupted copy of stored pattern `[-1,1,-1,1]` with site 0 flipped. -/
def corrupted : Fin 4 → FastReal := ![1, 1, -1, 1]

-- 1. Low-temperature recall (β = 4). Four sweeps, sample r = 1/2 at every site.
--    The field is integer-valued (±2, ±4), so at β = 4 the logistic saturates
--    and r = 1/2 follows the field deterministically: the corrupted input walks
--    to the stored pattern `[-1,1,-1,1]`.
#eval traceInts (hebbW ps) (fun _ => 0) 2 4 ⟨1, -1⟩ 4 corrupted

-- 2. The energy along that sampled chain settles to the pattern minimum -4.
#eval (gibbsTrace? (hebbW ps) (fun _ => 0) 2 4 ⟨1, -1⟩ 12 4 corrupted).map
  (fun tr => (traceEnergies (hebbW ps) tr).map (fun e => (e 24).mid.toFloat))

-- 3. Infinite temperature (β = 0): every P(ζ_pos) = 1/2 exactly, so the sample
--    r = 1/4 (< 1/2) forces every site to +1 regardless of the weights.
#eval traceInts (hebbW ps) (fun _ => 0) 2 0 ⟨1, -2⟩ 3 corrupted

-- 4. Cross-check: the corrupted start has energy 0, the recovered pattern -4.
#eval (EF (hebbW ps) (fun _ => 0) corrupted 24).mid.toFloat          -- expect  0
#eval (EF (hebbW ps) (fun _ => 0) ![(-1), 1, -1, 1] 24).mid.toFloat  -- expect -4

end Computable.Fast.Demos.GibbsRun
