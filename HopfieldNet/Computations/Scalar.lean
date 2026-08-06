/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# The scalar interface for executable neurodynamics

`NeuralNetwork R U ζ` constrains its scalar only by `[Zero R]`, so the specification is
already backend-agnostic. This file supplies the one piece the *executable* dynamics
additionally need, and it is deliberately narrow.

## Why comparison is the abstraction boundary

The candidate backends — `ℤ`, `ℚ`, `Float`, and the ball-arithmetic `FastReal` — differ in
speed everywhere, but they differ in *behaviour* in exactly one place: whether a comparison
succeeds at all.

* On `ℤ` and `ℚ` comparison is exact and total.
* On `FastReal` it is **genuinely partial**: separating two computable reals can require an
  unbounded search, so a fuelled comparison must be allowed to answer "don't know".
* On `Float` it is *also* partial, for a different reason — `NaN` is unordered, and
  incomparable with everything including itself.

So the honest common interface is a comparison returning `Option Ordering`. Algorithms are
written once against it; a backend that happens to be total discharges the `none` branch
for free via `IsTotalCmp`.

## The boundary at zero matters

The discrete activation of the Hopfield/neurodynamic literature is

`σ(u) = 0 if u ≤ 0`, `1 if u > 0`,

so `u = 0` maps to `0`. This is easy to get wrong by one case, and getting it wrong yields a
different dynamical system rather than a slightly different one — on integer weights, exact
ties at zero are common rather than negligible. `stepBinary` below implements the convention
above, and `stepBinary_eq_ite` pins it down against a specification that mentions no
comparison at all.
-/

namespace HopfieldNet.Computations

universe u

/-- A comparison that is allowed to fail.

`none` means *undecided*, not *equal*. It is the honest answer for a fuelled comparison of
computable reals that ran out of fuel, and for `Float` comparisons involving `NaN`. -/
class PartialCmp (R : Type u) where
  /-- Compare two scalars, or answer `none` if undecided. -/
  cmp : R → R → Option Ordering

export PartialCmp (cmp)

/-- Backends whose comparison never fails.

This is a `Prop`-valued mixin rather than a subclass, so there is no instance diamond with
`PartialCmp`. -/
class IsTotalCmp (R : Type u) [PartialCmp R] : Prop where
  /-- Comparison always succeeds. -/
  isSome : ∀ x y : R, (cmp x y).isSome

/-! ### Instances -/

/-- Any linear order gives an exact, total comparison. This covers `ℤ` and `ℚ`. -/
instance (priority := 100) instPartialCmpOfLinearOrder (R : Type u) [LinearOrder R] :
    PartialCmp R := ⟨fun x y => some (compare x y)⟩

instance (priority := 100) instIsTotalCmpOfLinearOrder (R : Type u) [LinearOrder R] :
    IsTotalCmp R := ⟨fun _ _ => rfl⟩

/-- `Float` comparison is partial: `NaN` is unordered, so no case applies and the answer is
`none`. `Float` is therefore deliberately *not* an `IsTotalCmp` instance — it is fit to use
as a fast unverified oracle, not as a source of truth. -/
instance : PartialCmp Float where
  cmp x y := if x < y then some .lt else if y < x then some .gt
             else if x == y then some .eq else none

/-! ### Derived tests -/

section Derived
variable {R : Type u} [PartialCmp R]

/-- `x ≤ y`, undecided as `none`. -/
def leb (x y : R) : Option Bool := (cmp x y).map (fun o => o != Ordering.gt)

/-- `x < y`, undecided as `none`. -/
def ltb (x y : R) : Option Bool := (cmp x y).map (fun o => o == Ordering.lt)

/-- `x = y`, undecided as `none`. -/
def eqb (x y : R) : Option Bool := (cmp x y).map (fun o => o == Ordering.eq)

/-- Comparison as a total function, on backends where it cannot fail. -/
def cmp! [IsTotalCmp R] (x y : R) : Ordering := (cmp x y).get (IsTotalCmp.isSome x y)

end Derived

/-! ### Activations -/

section Step
variable {R : Type u} [PartialCmp R] [Zero R] [One R]

/-- The binary activation `σ(u) = 0` if `u ≤ 0`, `1` if `u > 0`.

`fallback` is returned only when the comparison is undecided; on a total backend it is
unreachable, which is the content of `stepBinary_indep_fallback`. -/
def stepBinary (fallback : R) (net : R) : R :=
  match cmp net 0 with
  | some Ordering.gt => 1
  | some _ => 0
  | none => fallback

/-- The sign activation `±1` against a threshold `θ`: `1` if `θ ≤ net`, `-1` otherwise. -/
def stepSign [Neg R] (fallback : R) (net θ : R) : R :=
  match cmp net θ with
  | some Ordering.lt => -1
  | some _ => 1
  | none => fallback

end Step

/-! ### Correctness on total backends -/

section Total
variable {R : Type u} [LinearOrder R] [Zero R] [One R]

omit [Zero R] [One R] in
/-- On a linear order the partial comparison is just `compare`, wrapped in `some`. -/
theorem cmp_eq_some_compare (x y : R) : cmp x y = some (compare x y) := rfl

/-- On a linearly ordered backend the activation is exactly the textbook `σ`, with no
mention of comparison and no fallback. This is the statement that pins the convention at
`net = 0` down to `0`. -/
@[simp] theorem stepBinary_eq_ite (fallback net : R) :
    stepBinary fallback net = if 0 < net then 1 else 0 := by
  unfold stepBinary
  rw [cmp_eq_some_compare]
  rcases h : compare net (0 : R) with _ | _ | _
  · show (0 : R) = _
    rw [compare_lt_iff_lt] at h
    exact (if_neg (not_lt.2 h.le)).symm
  · show (0 : R) = _
    rw [compare_eq_iff_eq] at h
    subst h
    exact (if_neg (lt_irrefl _)).symm
  · show (1 : R) = _
    rw [compare_gt_iff_gt] at h
    exact (if_pos h).symm

/-- At exactly zero the activation is `0`, matching `σ(u) = 0` for `u ≤ 0`.

Stated separately because this is the case that is easy to get backwards, and where an
off-by-one-case error changes the dynamical system rather than merely perturbing it. -/
theorem stepBinary_zero (fallback : R) : stepBinary fallback (0 : R) = 0 := by
  simp

/-- The fallback is unreachable on a total backend: the dynamics do not depend on it. -/
theorem stepBinary_indep_fallback (f g net : R) :
    stepBinary f net = stepBinary g net := by
  simp

end Total

/-! ### Smoke tests -/

section Tests

-- The activation on `ℤ`, at and around the boundary. Expect `[0, 0, 1]`.
#eval ([-1, 0, 1] : List ℤ).map (stepBinary 37)

-- `Float` comparison is partial: `NaN` compares to `none`, everything else to `some`.
#eval (cmp (0.0 / 0.0 : Float) 1.0, cmp (1.0 : Float) 2.0)

-- Exact comparison on `ℚ`, where a float would round.
#eval cmp ((1 : ℚ) / 3) (333333333333 / 1000000000000)

end Tests

end HopfieldNet.Computations
