/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic

/-!
# Non-orthogonal Hebbian learning, executable over computable reals

The `FastReal` twin of `HopfieldNet/Quiver/HN/test.lean`, which exercises the
**non-orthogonal** Hebbian decomposition: for patterns `pᵢ ∈ {±1}^U`, the
Hebbian field on pattern `pⱼ` splits as

- **signal**: `(|U| - m) pⱼ`
- **interference**: `disturbanceTerm ps j`

with no orthogonality assumption.

`HopfieldNetwork R U` requires `[Field R] [LinearOrder R]
[IsStrictOrderedRing R]`, which computable reals cannot provide (`FastReal`
is ball arithmetic — it has no `AddCommMonoid`, let alone a decidable
order), so the `ℚ` file's `State`s and `Matrix` algebra are re-expressed as
plain `Fin 4 → FastReal` activation vectors and folds; `±1`-ness of the
patterns is by construction rather than a `pact` proof.

The `ℚ` file's *theorem* `test_nonorthogonal_decomposition` (an instance of
`patterns_pairwise_non_orthogonal`) cannot be transplanted as a theorem —
its statement lives in the ordered-field world. Its twin here is an
executable **certificate**: both sides of the decomposition are computed
over `FastReal` and compared componentwise with the fueled `eqF`. The
equalities are *decided* (not approximated): with `±1` patterns and integer
weights every ball stays an exact dyadic point, so the exact-point branch of
`FastReal.compare` settles each comparison at the first probe.
-/

open Computable.Fast Computable.Fast.API

-- `#eval` code generation unfolds the `FastReal` ball arithmetic, which is
-- much deeper than the `ℚ` original's.
set_option maxRecDepth 4096

namespace Computable.Fast.API.HNtest

/-! ### `Matrix` algebra over `FastReal`, as folds -/

/-- Twin of `Matrix.dotProduct`. -/
def dotF {n : ℕ} (x y : Fin n → FastReal) : FastReal :=
  (List.finRange n).foldl (fun acc v => acc + x v * y v) 0

/-- Twin of `Matrix.mulVec`. -/
def mulVecF {n : ℕ} (w : Matrix (Fin n) (Fin n) FastReal) (x : Fin n → FastReal) :
    Fin n → FastReal :=
  fun u => dotF (w u) x

/-- Twin of `(Hebbian ps).w = ∑ k, pₖ pₖᵀ - m • 1`, componentwise: for `±1`
patterns the diagonal is `∑ k, pₖ(u)² - m = 0`, and off the diagonal the
`- m • 1` term vanishes, leaving `∑ k, pₖ(u) pₖ(v)`. -/
def hebbW {m n : ℕ} (ps : Fin m → Fin n → FastReal) :
    Matrix (Fin n) (Fin n) FastReal := fun u v =>
  if u = v then 0
  else (List.finRange m).foldl (fun acc k => acc + ps k u * ps k v) 0

/-- Twin of `disturbanceTerm`: the interference
`∑ i ≠ j, pᵢ(u) ⬝ ⟪pᵢ, pⱼ⟫` felt by pattern `pⱼ` at neuron `u`. -/
def disturbanceTermF {m n : ℕ} (ps : Fin m → Fin n → FastReal) (j : Fin m) :
    Fin n → FastReal := fun u =>
  (List.finRange m).foldl
    (fun acc i => if i ≠ j then acc + ps i u * dotF (ps i) (ps j) else acc) 0

/-! ### The two non-orthogonal patterns -/

-- Two genuinely non-orthogonal patterns in `{±1}^(Fin 4)` over `FastReal`.
def pat0 : Fin 4 → FastReal := fun _ => 1

def pat1 : Fin 4 → FastReal := fun i => if i = 0 then -1 else 1

-- Package patterns as a `Fin 2 → (Fin 4 → FastReal)` family.
def ps_nonorth : Fin 2 → Fin 4 → FastReal := ![pat0, pat1]

-- The overlap is non-zero (here it is `2`).
#eval dotF pat0 pat1

-- A concrete interference value (non-zero, here `2`).
#eval disturbanceTermF ps_nonorth (1 : Fin 2) (0 : Fin 4)

/-! ### The decomposition, certified executably -/

/-- Executable twin of the `ℚ` theorem `test_nonorthogonal_decomposition`:
`(Hebbian ps).w *ᵥ p₁ = (card (Fin 4) - 2) • p₁ + disturbanceTerm ps 1`,
checked componentwise with the fueled `eqF`. `some true` means every
component was *decided* equal (no comparison ran out of fuel). -/
def test_nonorthogonal_decomposition : Option Bool :=
  (List.finRange 4).foldl
    (fun acc u => do
      let b ← acc
      let e ← eqF (mulVecF (hebbW ps_nonorth) pat1 u)
        (((4 : FastReal) - 2) * pat1 u + disturbanceTermF ps_nonorth (1 : Fin 2) u)
      pure (b && e))
    (some true)

-- The decomposition holds, decidedly so: expect `some true`.
#eval test_nonorthogonal_decomposition

-- The Hebbian field on `p₁` (twin of `#eval (Hebbian ps).w.mulVec p₁`;
-- the `ℚ` value is `![0, 4, 4, 4]`).
#eval mulVecF (hebbW ps_nonorth) pat1

end Computable.Fast.API.HNtest
