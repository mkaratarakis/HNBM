/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.TrigSound
import ComputableReals.Computable.FastComplexDivSound

/-!
# Verified transcendental functions on `FastComplex`

`FastComplex` ships total `exp`, `phase`, `fromPolar`, `sin`, `cos` and
`sqrt` built on the *runtime* real primitives (`FastReal.exp`,
`FastReal.cos`, `FastReal.sin`), which carry no soundness theorems. This
file supplies the verified twins, built instead on the unconditionally
sound `FastReal.expV`, `cosV`, `sinV` and `sqrt`, together with their
enclosure theorems against Mathlib's `Complex` functions.

The naming convention follows `expV`: a trailing `V` marks the verified
variant, and the unadorned name remains the (faster, unproven) runtime one.

* `expV` — the complex exponential, `exp z` for arbitrary `z : ℂ`;
* `phaseV'` / `fromPolarV` — the photonics primitives `e^{iθ}` and
  `r·e^{iθ}` (`phaseV` itself is proved in `TrigSound`);
* `cosV` / `sinV` — complex trigonometric functions via the exponential;
* `smul_encloses` — scaling a complex by a real.

Together with `FastMatrixSound`, these are what let a concrete optical
component discharge the `Encloses` hypothesis of `unitaryUpTo_sound`.
-/

open Computable.Fast

namespace Computable.Fast

namespace FastComplex

/-! ## Scaling by a real -/

/-- Scaling a `FastComplex` by a `FastReal` preserves enclosure. -/
theorem smul_encloses {x : FastReal} {r : ℝ} {z : FastComplex} {c : ℂ}
    (hx : x.Encloses r) (hz : z.Encloses c) :
    (FastComplex.smul x z).Encloses ((r : ℂ) * c) := by
  refine ⟨?_, ?_⟩
  · show (x * z.re).Encloses (((r : ℂ) * c).re)
    have : (((r : ℂ) * c).re) = r * c.re := by simp
    rw [this]
    exact FastReal.mul_encloses hx hz.1
  · show (x * z.im).Encloses (((r : ℂ) * c).im)
    have : (((r : ℂ) * c).im) = r * c.im := by simp
    rw [this]
    exact FastReal.mul_encloses hx hz.2

/-! ## The verified complex exponential

`Complex.exp z = exp (re z) · (cos (im z) + i · sin (im z))`, which is
exactly Mathlib's `Complex.exp_re` / `Complex.exp_im`. Assembling the
verified real `expV`, `cosV` and `sinV` therefore gives an unconditionally
sound complex exponential.
-/

/-- The verified complex exponential. -/
def expV (z : FastComplex) : FastComplex :=
  let r := FastReal.expV z.re
  { re := r * FastReal.cosV z.im, im := r * FastReal.sinV z.im }

/-- **Unconditional soundness of the complex exponential.** -/
theorem expV_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (expV z).Encloses (Complex.exp c) := by
  refine ⟨?_, ?_⟩
  · show (FastReal.expV z.re * FastReal.cosV z.im).Encloses (Complex.exp c).re
    rw [Complex.exp_re]
    exact FastReal.mul_encloses (FastReal.expV_sound hz.1) (FastReal.cosV_sound hz.2)
  · show (FastReal.expV z.re * FastReal.sinV z.im).Encloses (Complex.exp c).im
    rw [Complex.exp_im]
    exact FastReal.mul_encloses (FastReal.expV_sound hz.1) (FastReal.sinV_sound hz.2)

/-! ## Photonics primitives -/

/-- The verified polar constructor `r · e^{iθ}`. -/
def fromPolarV (r θ : FastReal) : FastComplex :=
  { re := r * FastReal.cosV θ, im := r * FastReal.sinV θ }

/-- **The verified polar constructor is sound**: `fromPolarV r θ` encloses
`r · e^{iθ}`. -/
theorem fromPolarV_sound {r θ : FastReal} {rR θR : ℝ}
    (hr : r.Encloses rR) (hθ : θ.Encloses θR) :
    (fromPolarV r θ).Encloses ((rR : ℂ) * Complex.exp ((θR : ℂ) * Complex.I)) := by
  refine ⟨?_, ?_⟩
  · show (r * FastReal.cosV θ).Encloses _
    have : (((rR : ℂ) * Complex.exp ((θR : ℂ) * Complex.I)).re) = rR * Real.cos θR := by
      simp [Complex.exp_ofReal_mul_I_re]
    rw [this]
    exact FastReal.mul_encloses hr (FastReal.cosV_sound hθ)
  · show (r * FastReal.sinV θ).Encloses _
    have : (((rR : ℂ) * Complex.exp ((θR : ℂ) * Complex.I)).im) = rR * Real.sin θR := by
      simp [Complex.exp_ofReal_mul_I_im]
    rw [this]
    exact FastReal.mul_encloses hr (FastReal.sinV_sound hθ)

/-! ## Complex trigonometric functions

`cos z = (e^{iz} + e^{-iz}) / 2` and `sin z = (e^{iz} - e^{-iz}) / (2i)`.
Rather than re-deriving the series, we obtain both from `expV` through
Mathlib's own identities, so soundness is inherited.
-/

/-- Multiplication by `I`, executably. -/
def mulI (z : FastComplex) : FastComplex :=
  { re := FastReal.neg z.im, im := z.re }

theorem mulI_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (mulI z).Encloses (Complex.I * c) := by
  refine ⟨?_, ?_⟩
  · show (FastReal.neg z.im).Encloses ((Complex.I * c).re)
    have : ((Complex.I * c).re) = -c.im := by simp
    rw [this]
    exact FastReal.neg_encloses hz.2
  · show z.re.Encloses ((Complex.I * c).im)
    have : ((Complex.I * c).im) = c.re := by simp
    rw [this]
    exact hz.1

/-- Halving, executably (exact: multiplication by the dyadic `2⁻¹`). -/
def half (z : FastComplex) : FastComplex :=
  FastComplex.smul (FastReal.ofDyadic ⟨1, -1⟩) z

theorem half_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (half z).Encloses (c / 2) := by
  have hd : (FastReal.ofDyadic ⟨1, -1⟩ : FastReal).Encloses ((1 : ℝ) / 2) := by
    have h := FastReal.encloses_ofDyadic (d := (⟨1, -1⟩ : Dyadic))
    have hv : ((Dyadic.toRat ⟨1, -1⟩ : ℚ) : ℝ) = (1 : ℝ) / 2 := by
      norm_num [Dyadic.toRat]
    rwa [hv] at h
  have := smul_encloses hd hz
  have hc : (((1 : ℝ) / 2 : ℝ) : ℂ) * c = c / 2 := by
    push_cast; ring
  rwa [hc] at this

/-- The verified complex cosine, `cos z = (e^{iz} + e^{-iz}) / 2`. -/
def cosV (z : FastComplex) : FastComplex :=
  half (expV (mulI z) + expV (FastComplex.neg (mulI z)))

/-- **Soundness of the verified complex cosine.** -/
theorem cosV_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (cosV z).Encloses (Complex.cos c) := by
  have h1 : (expV (mulI z)).Encloses (Complex.exp (Complex.I * c)) :=
    expV_sound (mulI_encloses hz)
  have h2 : (expV (FastComplex.neg (mulI z))).Encloses (Complex.exp (-(Complex.I * c))) :=
    expV_sound (neg_encloses (mulI_encloses hz))
  have hsum := half_encloses (add_encloses h1 h2)
  have hcos : (Complex.exp (Complex.I * c) + Complex.exp (-(Complex.I * c))) / 2
      = Complex.cos c := by
    rw [Complex.cos]
    ring_nf
  rwa [hcos] at hsum

/-- The verified complex sine, `sin z = (e^{-iz} - e^{iz})·i / 2`. -/
def sinV (z : FastComplex) : FastComplex :=
  half (mulI (expV (FastComplex.neg (mulI z)) - expV (mulI z)))

/-- **Soundness of the verified complex sine.** -/
theorem sinV_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (sinV z).Encloses (Complex.sin c) := by
  have h1 : (expV (FastComplex.neg (mulI z))).Encloses (Complex.exp (-(Complex.I * c))) :=
    expV_sound (neg_encloses (mulI_encloses hz))
  have h2 : (expV (mulI z)).Encloses (Complex.exp (Complex.I * c)) :=
    expV_sound (mulI_encloses hz)
  have hd := sub_encloses h1 h2
  have hm := mulI_encloses hd
  have hh := half_encloses hm
  have hsin : Complex.I * (Complex.exp (-(Complex.I * c)) - Complex.exp (Complex.I * c)) / 2
      = Complex.sin c := by
    rw [Complex.sin]
    ring_nf
  rwa [hsin] at hh

end FastComplex

end Computable.Fast
