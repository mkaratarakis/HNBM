/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic

/-!
# Executable Hopfield energy and descent certificates (`FastReal`)

The computable twin of the Hopfield energy of `HopfieldNet/Quiver/HN/Core.lean`
(which this file does **not** modify):

* `Eθ  = ∑ u, θ u * act u`                        (`NeuralNetwork.State.Eθ`)
* `Ew  = -1/2 * ∑ u, ∑ v ≠ u, w u v * act u * act v` (`NeuralNetwork.State.Ew`)
* `E   = Ew + Eθ`                                 (`NeuralNetwork.State.E`)

The originals are stated over a linear-ordered field `R`; over computable
reals the sums become folds (`FastReal` has no `AddCommMonoid`), and `-1/2`
is the *exact* dyadic `⟨-1, -1⟩`, so for integer weights every energy value
is an exact dyadic ball.

The Lyapunov theorem ("energy is non-increasing along asynchronous updates")
cannot be *decided* over computable reals, so its executable twin is a
**descent certificate**: `descentCertified?` compares consecutive energies
of a run with the fueled `leF` and returns `some true` only when every
inequality `E(s_{k+1}) ≤ E(s_k)` was decided. The `ℝ`-level meaning of such
a certified run is supplied by the bridge
(`IsHamiltonianR.energyToReal_is_lyapunov` in
`HopfieldNet/CReals/ComputableRealsBridge.lean`).

The demo at the bottom is the 4-neuron Hebbian network (patterns
`[1,1,-1,-1]`, `[-1,1,-1,1]`, initial state `[1,-1,-1,1]`): it stabilizes to
the stored pattern `[-1,1,-1,1]` in `2` steps with energy trace
`4, 0, -4, -4, …`, every descent step decided.
-/

open Computable.Fast Computable.Fast.API

-- `#eval` code generation unfolds the `FastReal` ball arithmetic.
set_option maxRecDepth 4096

namespace Computable.Fast.FastEnergy

/-- Exact dyadic `-1/2 = ⟨-1, -1⟩`. -/
def negHalf : FastReal := FastReal.ofDyadic ⟨-1, -1⟩

/-- Twin of `HNfnet`: the field `∑ v ≠ u, w u v * act v` at neuron `u`. -/
def netF {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (act : Fin n → FastReal)
    (u : Fin n) : FastReal :=
  (List.finRange n).foldl (fun acc v => if v ≠ u then acc + w u v * act v else acc) 0

/-- Twin of `NeuralNetwork.State.Eθ`: `∑ u, θ u * act u`. -/
def EθF {n : ℕ} (θ act : Fin n → FastReal) : FastReal :=
  (List.finRange n).foldl (fun acc u => acc + θ u * act u) 0

/-- Twin of `NeuralNetwork.State.Ew`:
`-1/2 * ∑ u, ∑ v ≠ u, w u v * act u * act v`. -/
def EwF {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (act : Fin n → FastReal) :
    FastReal :=
  negHalf * (List.finRange n).foldl (fun acc u => acc + act u * netF w act u) 0

/-- Twin of `NeuralNetwork.State.E`: the Hopfield energy `Ew + Eθ`. -/
def EF {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (θ act : Fin n → FastReal) :
    FastReal :=
  EwF w act + EθF θ act

/-- Executable twin of the Lyapunov property: check `E(s_{k+1}) ≤ E(s_k)`
along a list of energies with the fueled `leF`. `some true` means every
descent step was *decided* (no comparison ran out of fuel); `none` means
some comparison was undecided — we never claim descent we could not see. -/
def descentCertified? (es : List FastReal) (fuel : ℕ := defaultFuel) :
    Option Bool :=
  match es with
  | [] => some true
  | [_] => some true
  | a :: b :: rest => do
      let step ← leF b a fuel
      let more ← descentCertified? (b :: rest) fuel
      pure (step && more)

/-! ## Demo: the 4-neuron Hebbian network

The computable copy of the classical example (Hebbian weights from the
patterns `[1,1,-1,-1]` and `[-1,1,-1,1]`, thresholds `0`), running the
`±1` threshold dynamics with the fueled `signStep` of `API/Basic.lean`. -/

/-- Hopfield network over `FastReal` on `n` neurons: complete graph, `±1`
activations, fueled sign-threshold activation. -/
abbrev HopfieldFast (n : ℕ) [NeZero n] :
    NeuralNetwork FastReal (Fin n) FastReal where
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

/-- Hebbian weight matrix over `FastReal` (zero diagonal, as in
`(Hebbian ps).w` for `±1` patterns). -/
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

/-- The two stored patterns: `[1,1,-1,-1]` and `[-1,1,-1,1]`. -/
def ps : Fin 2 → Fin 4 → FastReal := ![![1, 1, -1, -1], ![-1, 1, -1, 1]]

/-- Hebbian parameters from `ps`. -/
def pH : Params (HopfieldFast 4) := hebbParams ps

/-- Initial state `[1,-1,-1,1]`. -/
def extu : (HopfieldFast 4).State where
  act := ![1, -1, -1, 1]
  hp _ := trivial

/-- The stabilization run: `(final state, steps, certified-stable)`. -/
def run : (HopfieldFast 4).State × ℕ × Bool := stabilizeF pH 64 extu

/-- States after every prefix of two cyclic update rounds (initial state
first). -/
def stateTrace : List ((HopfieldFast 4).State) :=
  (([0, 1, 2, 3, 0, 1, 2, 3] : List (Fin 4)).inits).map
    (fun pref => pref.foldl (fun s u => s.Up pH u) extu)

/-- The energies along the run (thresholds are `0`, so `E = Ew`). -/
def energyTrace : List FastReal :=
  stateTrace.map (fun s => EF (hebbW ps) (fun _ => 0) s.act)

/-! ## The computations -/

-- Stable state: expect `some [-1, 1, -1, 1]` (the second stored pattern),
-- reached in `2` steps, with decided stability.
#eval actsToInts run.1.act
#eval run.2.1  -- expect `2`
#eval run.2.2  -- expect `true`

-- Energies along the run: expect exact balls `4, 0, -4, -4, …`.
#eval energyTrace

-- Energy of the initial state and of both stored patterns
-- (stored patterns are energy minima; expect `4`, `-4`, `-4`).
#eval EF (hebbW ps) (fun _ => 0) ![1, -1, -1, 1]
#eval EF (hebbW ps) (fun _ => 0) (ps 0)
#eval EF (hebbW ps) (fun _ => 0) (ps 1)

-- The descent certificate: every step `E(s_{k+1}) ≤ E(s_k)` decided.
#eval descentCertified? energyTrace  -- expect `some true`

end Computable.Fast.FastEnergy
