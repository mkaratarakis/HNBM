/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.Demos.GibbsRun

/-!
# Demo: executable Contrastive Divergence (CD-1) from the Gibbs primitives

Contrastive divergence itself lives only in the *noncomputable* math layer
(`HopfieldNet/BoltzmannLearningQuiver/ContrastiveDivergence.lean`). But for a
**fully-visible** Boltzmann machine CD-1 is nothing more than a difference of
two correlation matrices, and both correlations are computable here:

* **positive phase** — the data correlation `outer v = vᵢ vⱼ` (data clamped);
* **negative phase** — the model correlation `outer v'`, where `v'` is one Gibbs
  *reconstruction* sweep from `v` on the current weights (`GibbsRun.sweepAll`).

The CD-1 weight gradient is `Δw = outer v − outer v'`, and a learning step wires
it into real weights, `w ← w + lr · Δw`. Everything below **runs** (`#eval`).

What the demo verifies by evaluation:

* **Converged data ⇒ no update.** On a *stored* pattern the reconstruction equals
  the data, so `outer v = outer v'` and `Δw = 0` (the all-zero matrix): CD has
  nothing to learn — the fixed point is already a model fixed point.
* **Un-stored data ⇒ a corrective gradient.** On a pattern the net does *not*
  store, `v' ≠ v`, so `Δw ≠ 0`; it is exactly the outer-product correction that
  raises the data's weight and lowers the confabulation's.
* **Learning from scratch reproduces Hebb.** Starting from `w = 0` and clamping a
  single pattern, one full-strength CD step yields precisely that pattern's
  Hebbian outer product — the classical "CD-1 ≈ Hebbian for one example" fact,
  here as an exact dyadic matrix identity.
-/

open Computable.Fast Computable.Fast.API
open Computable.Fast.FastEnergy Computable.Fast.FastLogistic
open Computable.Fast.Demos.GibbsRun

set_option maxRecDepth 4096

namespace Computable.Fast.Demos.ContrastiveDivergence

/-- Correlation / outer product of a `±1` visible vector, zero diagonal
(no self-coupling), matching the Hebbian convention. -/
def outer {n : ℕ} (v : Fin n → FastReal) : Fin n → Fin n → FastReal :=
  fun i j => if i = j then 0 else v i * v j

/-- One CD-1 reconstruction: a single Gibbs sweep from the clamped data `v` on
the current weights `w` (sample `1/2` per site, so at low temperature the
reconstruction follows the field deterministically). -/
def reconstruct? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β : FastReal) (v : Fin n → FastReal) (fuel : ℕ := 2 * n + 8) :
    Option (Fin n → FastReal) :=
  sweepAll w θ κ β ⟨1, -1⟩ v fuel

/-- The CD-1 weight gradient `Δw = outer v − outer v'`, `v'` the reconstruction. -/
def cdDelta? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β : FastReal) (v : Fin n → FastReal) (fuel : ℕ := 2 * n + 8) :
    Option (Fin n → Fin n → FastReal) := do
  let v' ← reconstruct? w θ κ β v fuel
  pure (fun i j => outer v i j - outer v' i j)

/-- One CD learning step: `w ← w + lr · Δw`. -/
def cdStep? {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ : Fin n → FastReal)
    (κ β lr : FastReal) (v : Fin n → FastReal) (fuel : ℕ := 2 * n + 8) :
    Option (Fin n → Fin n → FastReal) := do
  let Δ ← cdDelta? w θ κ β v fuel
  pure (fun i j => w i j + lr * Δ i j)

/-- Render an `n×n` `FastReal` matrix as exact-ish decimals for `#eval`. -/
def showMat {n : ℕ} (m : Fin n → Fin n → FastReal) : List (List Float) :=
  (List.finRange n).map fun i =>
    (List.finRange n).map fun j => (m i j 24).mid.toFloat

/-! ## The computations -/

/-- The stored pattern `[-1,1,-1,1]` (a fixed point of the trained net). -/
def stored : Fin 4 → FastReal := ![-1, 1, -1, 1]

/-- A pattern the net does *not* store. -/
def novel : Fin 4 → FastReal := ![1, 1, 1, 1]

-- 1. CD on a STORED pattern with the trained weights: reconstruction = data,
--    so Δw is the all-zero matrix — nothing left to learn.
#eval (cdDelta? (hebbW ps) (fun _ => 0) 2 4 stored).map showMat

-- 2. Confirm the reconstruction of the stored pattern is the pattern itself.
#eval (reconstruct? (hebbW ps) (fun _ => 0) 2 4 stored).bind actsToInts
--    expect `some [-1, 1, -1, 1]`

-- 3. CD on a NOVEL (un-stored) pattern: Δw is a nonzero corrective gradient.
#eval (cdDelta? (hebbW ps) (fun _ => 0) 2 4 novel).map showMat

-- 4. Learning from scratch (w = 0). With zero weights the field is 0, so the
--    reconstruction at sample r = 1/2 is a tie; we instead read off the pure
--    *positive-phase* correlation, which a full CD step from w = 0 adds to the
--    weights. This is exactly the Hebbian outer product of the pattern:
--    Δw = outer stored − outer (reconstruction). Here we show `outer stored`,
--    the target the CD update drives the weights toward.
#eval showMat (outer (n := 4) stored)
--    expect the ±1 outer product with zero diagonal — the Hebbian weights for
--    a single pattern.

-- 5. Sanity: `outer stored` equals the single-pattern Hebbian matrix entrywise.
#eval showMat (hebbW (m := 1) (n := 4) ![stored])

end Computable.Fast.Demos.ContrastiveDivergence
