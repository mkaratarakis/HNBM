/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.FastEnergy

/-!
# Executable logistic and Gibbs updates (`FastReal`)

The computable twin of the stochastic layer of
`HopfieldNet/Quiver/NeuralNetwork/TwoState.lean` (which this file does
**not** modify):

* `logisticProb x = 1 / (1 + exp (-x))`  →  `logistic?`, via `FastReal.exp`
  and the partial reciprocal `FastReal.inv?` (the denominator is provably
  `> 1`, so the reciprocal is decided at every sufficient precision, but we
  keep the honest `Option`);
* `probPos f p T s u = logisticProb (κ * L * β)`  →  `probPos?`, with the
  scale `κ` and inverse temperature `β` passed as `FastReal` data (`κ = 2`
  for `±1` networks, by `TwoState.scale_binary`);
* `gibbsUpdate` (a `PMF`)  →  `gibbsSiteUpdate?`. A `PMF` cannot be
  executed; what *can* is the sampler it induces: given a uniform dyadic
  sample `r ∈ [0,1)`, update to `ζ_pos = 1` iff `r < P(ζ_pos)`. Deciding
  `r < p` against the logistic's shrinking enclosures is
  `decideBernoulli?`; since `p` is transcendental and `r` dyadic, `r ≠ p`,
  so the comparison is decided at some finite precision — total in
  practice, `Option` by honesty;
* `gibbsSweep` (sequential sweep) → `gibbsSweep?`, folding site updates
  over a list of `(site, sample)` pairs.

The zero-temperature limit of `gibbsUpdate` (`TwoState.zeroTempDet`,
`if θ ≤ net then updPos else updNeg`) already has its executable twin in
`API/Basic.lean` (`signStep`); this file provides the positive-temperature
stochastic dynamics.
-/

open Computable.Fast Computable.Fast.API Computable.Fast.FastEnergy

set_option maxRecDepth 4096

namespace Computable.Fast.FastLogistic

/-- Denominator of the logistic: `1 + exp (-x) > 1`. -/
def logisticDenom (x : FastReal) : FastReal := 1 + FastReal.exp (-x)

/-- Twin of `TwoState.logisticProb x = 1 / (1 + Real.exp (-x))`: a partial
approximator returning an enclosure of the probability at each requested
precision. -/
def logistic? (x : FastReal) : ℕ → Option Ball :=
  FastReal.inv? (logisticDenom x)

/-- Twin of `TwoState.probPos`: `P(ζ_u = ζ_pos) = logistic (κ * L * β)`,
where `L = net - θ` is the local field, `κ` the two-state scale, `β` the
inverse temperature. -/
def probPos? (κ β L : FastReal) : ℕ → Option Ball :=
  logistic? (κ * L * β)

/-- Decide a Bernoulli outcome against a partial probability approximator:
probe `p?` at increasing precisions `i, i+1, …` (spending `fuel`) until the
enclosure of `p` separates from the sample `r` — `some true` iff `r < p`
(take `ζ_pos`), `some false` iff `p ≤ r`, `none` if fuel ran out. -/
def decideBernoulli? (p? : ℕ → Option Ball) (r : Dyadic) :
    ℕ → ℕ → Option Bool
  | _, 0 => none
  | i, fuel + 1 =>
    match p? i with
    | none => decideBernoulli? p? r (i + 1) fuel
    | some b =>
      if r < b.lo then some true
      else if b.hi ≤ r then some false
      else decideBernoulli? p? r (i + 1) fuel

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

/-! ## The computations

Sanity values (`ℝ` counterparts in parentheses):
* `logistic 0 = 1/2` exactly;
* `logistic (-4) ≈ 0.01799`, `logistic 4 ≈ 0.98201`.
-/

-- Enclosures of `logistic 0 = 1/2` and `logistic (±4)`.
#eval logistic? (0 : FastReal) 20
#eval logistic? (-4 : FastReal) 20
#eval logistic? (4 : FastReal) 20

-- Bernoulli decisions against `p = logistic 0 = 1/2`:
-- `r = 1/4 < 1/2` and `r = 3/4 ≥ 1/2`, both decided.
#eval decideBernoulli? (logistic? 0) ⟨1, -2⟩ 0 defaultFuel  -- expect `some true`
#eval decideBernoulli? (logistic? 0) ⟨3, -2⟩ 0 defaultFuel  -- expect `some false`

/-! Gibbs dynamics on the 4-neuron Hebbian demo network of `FastEnergy`
(`κ = 2` for `±1` activations, thresholds `0`). At site `0` of the initial
state `[1,-1,-1,1]` the field is `net = -2`, so
`P(ζ_pos) = logistic (-4β)` — small at `β = 1`: with `r = 1/4` the update
goes negative, matching the deterministic (zero-temperature) run. -/

-- One Gibbs update at site 0, `β = 1`, `r = 1/4`:
-- expect `some [-1, -1, -1, 1]` (as integers).
#eval (gibbsSiteUpdate? (hebbW ps) (fun _ => 0) 2 1 ![1, -1, -1, 1] 0 ⟨1, -2⟩).bind
  actsToInts

-- A full sweep at `β = 1` with samples `1/4` everywhere reproduces the
-- deterministic trajectory to the stored pattern: expect `some [-1, 1, -1, 1]`.
#eval (gibbsSweep? (hebbW ps) (fun _ => 0) 2 1
  ([0, 1, 2, 3].map (fun u => ((u : Fin 4), (⟨1, -2⟩ : Dyadic))))
  ![1, -1, -1, 1]).bind actsToInts

-- At infinite temperature (`β = 0`) every probability is exactly `1/2`:
-- the sample alone decides, and the tie `p = 1/2` against dyadic `r` is
-- still decided exactly. `r = 1/4 < 1/2` forces `+1` at site 0.
#eval (gibbsSiteUpdate? (hebbW ps) (fun _ => 0) 2 0 ![1, -1, -1, 1] 0 ⟨1, -2⟩).bind
  actsToInts  -- expect `some [1, -1, -1, 1]`

end Computable.Fast.FastLogistic
