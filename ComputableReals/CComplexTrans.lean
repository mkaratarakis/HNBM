/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CComplexAbs

/-!
# Transcendental functions on the specification model `CComplex`

`CComplex` is a `Field` with an absolute value, but until now it carried no
analytic functions: no `exp`, `log`, `sin`, `cos`, `sqrt` or `arg`. This
file supplies them, so that statements about computable complex analysis
can be *phrased* in the specification model rather than only in `ℂ`.

## How they are defined, and why

They are transported along the ring isomorphism
`CComplexBridge.complexRingEquiv : CComplex ≃+* ℂ`, i.e.
`exp z := ofComplex (Complex.exp (toComplex z))`. This makes them
noncomputable — as are `Inv` and `Field` on `CComplex` already — and it
makes every bridge lemma (`toComplex_exp` and friends) hold definitionally.

An *intrinsic* construction (Taylor series on `CReal.Pre`, as `CRealExp`
does for the real exponential) is not currently possible: `CReal` has a
total `sqrt`, but its `exp` is restricted to arguments carrying
`ExpRangeData`, its `log` only to `|x| ≤ 1/2`, and it has no trigonometric
functions at all. Building total `CReal.exp`, `CReal.cos` and `CReal.sin`
is the prerequisite, and is left as future work.

This is not as weak as it sounds. The *executable* side already has
intrinsic, unconditionally verified implementations — `FastComplex.expV`,
`cosV`, `sinV`, and `phaseV` — whose soundness theorems are stated against
Mathlib's `Complex.exp`, `Complex.cos`, `Complex.sin`. Since the
definitions here target the same Mathlib functions, the executable and
specification sides are talking about exactly the same objects; that
correspondence is made explicit in
`ComputableReals/Computable/CComplexRefine.lean`.
-/

open Computable

namespace Computable

namespace CComplex


/-! ## Definitions -/

/-- The complex exponential on the specification model. -/
noncomputable def exp (z : CComplex) : CComplex :=
  ofComplex (Complex.exp (toComplex z))

/-- The principal complex logarithm on the specification model. -/
noncomputable def log (z : CComplex) : CComplex :=
  ofComplex (Complex.log (toComplex z))

/-- The complex cosine on the specification model. -/
noncomputable def cos (z : CComplex) : CComplex :=
  ofComplex (Complex.cos (toComplex z))

/-- The complex sine on the specification model. -/
noncomputable def sin (z : CComplex) : CComplex :=
  ofComplex (Complex.sin (toComplex z))

/-- The principal square root on the specification model. -/
noncomputable def sqrt (z : CComplex) : CComplex :=
  ofComplex (toComplex z ^ (1 / 2 : ℂ))

/-- The principal argument, as a `CReal`. -/
noncomputable def arg (z : CComplex) : CReal :=
  CReal.FromReal.ofReal (Complex.arg (toComplex z))

/-! ## Bridge lemmas

Each function commutes with `toComplex` by construction, which is what lets
theorems be transported in either direction.
-/

@[simp] theorem toComplex_exp (z : CComplex) :
    toComplex (exp z) = Complex.exp (toComplex z) := by
  simp [exp]

@[simp] theorem toComplex_log (z : CComplex) :
    toComplex (log z) = Complex.log (toComplex z) := by
  simp [log]

@[simp] theorem toComplex_cos (z : CComplex) :
    toComplex (cos z) = Complex.cos (toComplex z) := by
  simp [cos]

@[simp] theorem toComplex_sin (z : CComplex) :
    toComplex (sin z) = Complex.sin (toComplex z) := by
  simp [sin]

@[simp] theorem toComplex_sqrt (z : CComplex) :
    toComplex (sqrt z) = toComplex z ^ (1 / 2 : ℂ) := by
  simp [sqrt]

@[simp] theorem toReal_arg (z : CComplex) :
    CReal.toReal (arg z) = Complex.arg (toComplex z) := by
  simp [arg, CReal.toReal_ofReal]

/-! ## Transported identities

Every identity holds because `toComplex` is injective and commutes with
each function; `toComplex_injective` plus `simp` discharges them uniformly.
-/

@[simp] theorem exp_zero : exp 0 = 1 := by
  apply toComplex_injective; simp

theorem exp_add (z w : CComplex) : exp (z + w) = exp z * exp w := by
  apply toComplex_injective; simp [Complex.exp_add]

@[simp] theorem exp_ne_zero (z : CComplex) : exp z ≠ 0 := fun h =>
  Complex.exp_ne_zero (toComplex z) (by simpa using congrArg toComplex h)

@[simp] theorem cos_zero : cos 0 = 1 := by
  apply toComplex_injective; simp

@[simp] theorem sin_zero : sin 0 = 0 := by
  apply toComplex_injective; simp

theorem sin_sq_add_cos_sq (z : CComplex) : sin z * sin z + cos z * cos z = 1 := by
  apply toComplex_injective
  simp only [toComplex_mul, toComplex_add, toComplex_sin, toComplex_cos,
    toComplex_one]
  have h := Complex.sin_sq_add_cos_sq (toComplex z)
  rw [← h]; ring

theorem cos_neg (z : CComplex) : cos (-z) = cos z := by
  apply toComplex_injective; simp [Complex.cos_neg]

theorem sin_neg (z : CComplex) : sin (-z) = -sin z := by
  apply toComplex_injective; simp [Complex.sin_neg]

theorem exp_log {z : CComplex} (hz : z ≠ 0) : exp (log z) = z := by
  apply toComplex_injective
  simp only [toComplex_exp, toComplex_log]
  exact Complex.exp_log (fun h => hz (toComplex_injective (by simpa using h)))

/-- The principal square root really is a square root. -/
theorem sq_sqrt (z : CComplex) : sqrt z * sqrt z = z := by
  apply toComplex_injective
  simp only [toComplex_mul, toComplex_sqrt]
  by_cases h : toComplex z = 0
  · rw [h, Complex.zero_cpow (by norm_num), mul_zero]
  · rw [← Complex.cpow_add _ _ h]
    norm_num

end CComplex

end Computable
