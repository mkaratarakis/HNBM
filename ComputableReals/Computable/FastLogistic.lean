import ComputableReals.Decision
/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

/-!
# Executable logistic and Bernoulli decisions (`FastReal`)

The executable stochastic layer over computable reals:

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

open Computable.Fast Computable.Fast.API

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


end Computable.Fast.FastLogistic
