/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CRealsFast

/-!
# Fueled decision procedures on computable reals

Order comparison on computable reals is undecidable, so there is no
`Decidable (x ≤ y)` instance to lean on. This module provides the total,
fuel-based replacements built on `FastReal.compare`, which either

* separates the two enclosing balls (a strict inequality),
* observes that both balls are exact radius-`0` points and compares them
  exactly (this is what decides *ties*), or
* exhausts its fuel and answers `none`.

Every consumer therefore gets an `Option`, and an answer of `none` is
reported rather than guessed. The soundness theorems for these are in
`ComputableReals/Computable/Refinement.lean`: a decided `leF`/`eqF` really
does imply the corresponding relation between the enclosed reals.

The threshold steps `binaryStep`/`signStep` are the generic `{0,1}` and
`{±1}` activation shapes; they keep the current value when a comparison is
undecided, so a caller that needs totality gets it without the procedure
ever lying about an order it could not establish.
-/

open Computable.Fast

namespace Computable.Fast.API

/-- Default fuel for fueled comparisons. Irrelevant for exact (radius-`0`)
inputs, which are decided at the first probe. -/
def defaultFuel : ℕ := 60

/-- Fueled equality test: `some true`/`some false` if decided, `none` if the
balls neither separate nor become exact points within fuel. -/
def eqF (x y : FastReal) (fuel : ℕ := defaultFuel) : Option Bool :=
  (FastReal.compare x y fuel).map (· == Ordering.eq)

/-- Fueled `x ≤ y` test. -/
def leF (x y : FastReal) (fuel : ℕ := defaultFuel) : Option Bool :=
  (FastReal.compare x y fuel).map (· != Ordering.gt)

/-- Binary `{0,1}` threshold step: `1` if `0 ≤ net`, `0` if `net < 0`,
current value if undecided within fuel. -/
def binaryStep (curr net : FastReal) (fuel : ℕ := defaultFuel) : FastReal :=
  match FastReal.compare net 0 fuel with
  | some Ordering.lt => 0
  | some _ => 1
  | none => curr

/-- Sign `{±1}` threshold step against a threshold `θ`: `1` if `θ ≤ net`,
`-1` if `net < θ`, current value if undecided within fuel. -/
def signStep (curr net θ : FastReal) (fuel : ℕ := defaultFuel) : FastReal :=
  match FastReal.compare net θ fuel with
  | some Ordering.lt => -1
  | some _ => 1
  | none => curr

/-- Render a vector of computable reals as integers (via fueled sign), for
readable `#eval` output: `some [1, -1, ...]`, or `none` if some sign is
undecided. -/
def actsToInts {n : ℕ} (act : Fin n → FastReal) (fuel : ℕ := defaultFuel) :
    Option (List Int) :=
  (List.finRange n).mapM (fun u => FastReal.sign (act u) fuel)

end Computable.Fast.API
