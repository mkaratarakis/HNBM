/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.FastComplexSound
import HopfieldNet.CReals.Computable.InvSound

/-!
# Soundness of executable division — real and complex

Closes the "complex division" coverage gap. `FastReal.div?` is
`x·(y⁻¹)` in ball arithmetic (partial: `none` unless the denominator is
certified apart from `0`); the complex `inv?`/`div?` route through it
componentwise (`z⁻¹ = z̄/|z|²`, `z/w = z·w̄/|w|²`).

* `FastReal.div?_sound` — a decided real division encloses `a/d`
  (`none` on the result already certifies `d`'s apartness, so no `d ≠ 0`
  hypothesis is needed — Lean's `x/0 = 0` makes the target lemmas hold
  even in the degenerate case);
* `FastComplex.inv?_sound` — a decided complex reciprocal encloses
  `c⁻¹` componentwise (via `Complex.inv_re`/`inv_im`);
* `FastComplex.div?_sound` — a decided complex division encloses `c/d`
  componentwise (via the `c·d̄/|d|²` identity).

With these the executable complex field is enclosure-verified for
`+`, `−`, `*`, `⁻¹`, `/`, `conj`, `pow`, `normSq`, `abs` — a complete
verified computable-complex arithmetic.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast

namespace FastReal

/-- A decided real division encloses the quotient. -/
theorem div?_sound {x y : FastReal} {a d : ℝ} (hx : x.Encloses a) (hy : y.Encloses d)
    {n : ℕ} {b : Ball} (h : FastReal.div? x y n = some b) : b.Encloses (a / d) := by
  simp only [FastReal.div?, Ball.div?, Option.bind_eq_bind', Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨invy, hinv, hb⟩ := h
  have hinvy : invy.Encloses d⁻¹ := Ball.inv?_sound (hy _) hinv
  subst hb
  rw [div_eq_mul_inv]
  exact Ball.mul_encloses _ (hx _) hinvy

end FastReal

namespace FastComplex

/-- A decided complex reciprocal encloses `c⁻¹` componentwise. -/
theorem inv?_sound {z : FastComplex} {c : ℂ} (hz : z.Encloses c)
    {n : ℕ} {r i : Ball} (h : FastComplex.inv? z n = some (r, i)) :
    r.Encloses c⁻¹.re ∧ i.Encloses c⁻¹.im := by
  simp only [FastComplex.inv?, Option.bind_eq_bind', Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rr, hrr, ii, hii, hr, hi⟩ := h
  subst hr; subst hi
  have hns : (FastComplex.normSq z).Encloses (Complex.normSq c) := normSq_encloses hz
  refine ⟨?_, ?_⟩
  · rw [Complex.inv_re]
    exact FastReal.div?_sound hz.1 hns hrr
  · rw [Complex.inv_im]
    have := FastReal.div?_sound (FastReal.neg_encloses hz.2) hns hii
    rwa [show (-c.im) / Complex.normSq c = -c.im / Complex.normSq c from rfl] at this

/-- The real part of `c/d` equals `(c·d̄).re / |d|²` (holds even at `d = 0`
by Lean's `x/0 = 0`). -/
private lemma div_re_eq (c d : ℂ) :
    (c / d).re = (c * (starRingEnd ℂ) d).re / Complex.normSq d := by
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma div_im_eq (c d : ℂ) :
    (c / d).im = (c * (starRingEnd ℂ) d).im / Complex.normSq d := by
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A decided complex division encloses `c/d` componentwise. -/
theorem div?_sound {z w : FastComplex} {c d : ℂ}
    (hz : z.Encloses c) (hw : w.Encloses d)
    {n : ℕ} {r i : Ball} (h : FastComplex.div? z w n = some (r, i)) :
    r.Encloses (c / d).re ∧ i.Encloses (c / d).im := by
  simp only [FastComplex.div?, Option.bind_eq_bind', Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rr, hrr, ii, hii, hr, hi⟩ := h
  subst hr; subst hi
  have hnum : (FastComplex.mul z (FastComplex.conj w)).Encloses (c * (starRingEnd ℂ) d) :=
    mul_encloses hz (conj_encloses hw)
  have hns : (FastComplex.normSq w).Encloses (Complex.normSq d) := normSq_encloses hw
  refine ⟨?_, ?_⟩
  · rw [div_re_eq]
    exact FastReal.div?_sound hnum.1 hns hrr
  · rw [div_im_eq]
    exact FastReal.div?_sound hnum.2 hns hii

/-! ## Demos -/

-- `1 / I = -I`: `(0, -1)` componentwise, at precision 20 — sound enclosure.
#eval FastComplex.inv? FastComplex.I 20

-- `(3 + 4I) / (1 + 2I) = 2.2 + (-0.4)I`.
#eval FastComplex.div? ⟨FastReal.ofDyadic ⟨3, 0⟩, FastReal.ofDyadic ⟨4, 0⟩⟩
  ⟨1, FastReal.ofDyadic ⟨2, 0⟩⟩ 20

end FastComplex

end Computable.Fast
