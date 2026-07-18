/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.Computable.SqrtSound
import HopfieldNet.CReals.FastComplex
import Mathlib.Analysis.Complex.Norm

/-!
# Soundness of the executable complex numbers

The complex analogue of the real refinement tower. `FastComplex` is a
`re`/`im` pair of `FastReal`s, so its enclosure relation is componentwise:

`z.Encloses c := z.re.Encloses c.re ∧ z.im.Encloses c.im`.

Since `ℂ` carries no order, there is no `compare`; the executable decision
procedure is componentwise *equality* (`eqCF`, built from the real `eqF`),
and its soundness (`eqCF_sound`) is the complex counterpart of
`FastReal.compare_sound`.

Every ring operation reduces to the already-verified `FastReal` enclosure
lemmas:

* `add`/`neg`/`sub`/`mul`/`conj`/`pow`_encloses — the field structure;
* `normSq_encloses` — `re² + im²` encloses `Complex.normSq`;
* `abs_encloses` — `√(re² + im²)` encloses the norm `‖c‖` (via
  `SqrtSound.FastReal.sqrt_sound` and `Complex.norm_def`), the payoff of
  the sqrt work.

Together with the existing `CComplex ≃+* ℂ` bridge, an executed
`FastComplex` computation now transfers as a theorem about honest
Mathlib complex numbers.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast

namespace FastComplex

/-- Componentwise enclosure of a Mathlib complex by a `FastComplex`. -/
def Encloses (z : FastComplex) (c : ℂ) : Prop :=
  z.re.Encloses c.re ∧ z.im.Encloses c.im

/-! ## Grounding -/

theorem encloses_zero : (0 : FastComplex).Encloses 0 :=
  ⟨FastReal.encloses_zero, FastReal.encloses_zero⟩

theorem encloses_one : (1 : FastComplex).Encloses 1 := by
  refine ⟨?_, ?_⟩
  · show (FastReal.ofDyadic ⟨1, 0⟩).Encloses (1 : ℂ).re
    rw [Complex.one_re]
    have := FastReal.encloses_one
    have hv : (1 : FastReal) = FastReal.ofDyadic ⟨1, 0⟩ := rfl
    rwa [hv] at this
  · show (0 : FastReal).Encloses (1 : ℂ).im
    rw [Complex.one_im]; exact FastReal.encloses_zero

theorem encloses_I : FastComplex.I.Encloses Complex.I := by
  refine ⟨?_, ?_⟩
  · show (0 : FastReal).Encloses Complex.I.re
    rw [Complex.I_re]; exact FastReal.encloses_zero
  · show (1 : FastReal).Encloses Complex.I.im
    rw [Complex.I_im]; exact FastReal.encloses_one

theorem encloses_ofReal {x : FastReal} {r : ℝ} (h : x.Encloses r) :
    (FastComplex.ofFastReal x).Encloses (r : ℂ) := by
  refine ⟨?_, ?_⟩
  · show x.Encloses (r : ℂ).re; rwa [Complex.ofReal_re]
  · show (0 : FastReal).Encloses (r : ℂ).im
    rw [Complex.ofReal_im]; exact FastReal.encloses_zero

/-! ## Ring operations -/

theorem add_encloses {z w : FastComplex} {c d : ℂ}
    (hz : z.Encloses c) (hw : w.Encloses d) : (z + w).Encloses (c + d) := by
  refine ⟨?_, ?_⟩
  · show (z.re + w.re).Encloses (c + d).re
    rw [Complex.add_re]; exact FastReal.add_encloses hz.1 hw.1
  · show (z.im + w.im).Encloses (c + d).im
    rw [Complex.add_im]; exact FastReal.add_encloses hz.2 hw.2

theorem neg_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (-z).Encloses (-c) := by
  refine ⟨?_, ?_⟩
  · show (FastReal.neg z.re).Encloses (-c).re
    rw [Complex.neg_re]; exact FastReal.neg_encloses hz.1
  · show (FastReal.neg z.im).Encloses (-c).im
    rw [Complex.neg_im]; exact FastReal.neg_encloses hz.2

theorem sub_encloses {z w : FastComplex} {c d : ℂ}
    (hz : z.Encloses c) (hw : w.Encloses d) : (z - w).Encloses (c - d) := by
  refine ⟨?_, ?_⟩
  · show (z.re - w.re).Encloses (c - d).re
    rw [Complex.sub_re]; exact FastReal.sub_encloses hz.1 hw.1
  · show (z.im - w.im).Encloses (c - d).im
    rw [Complex.sub_im]; exact FastReal.sub_encloses hz.2 hw.2

theorem mul_encloses {z w : FastComplex} {c d : ℂ}
    (hz : z.Encloses c) (hw : w.Encloses d) : (z * w).Encloses (c * d) := by
  refine ⟨?_, ?_⟩
  · show (z.re * w.re - z.im * w.im).Encloses (c * d).re
    rw [Complex.mul_re]
    exact FastReal.sub_encloses (FastReal.mul_encloses hz.1 hw.1)
      (FastReal.mul_encloses hz.2 hw.2)
  · show (z.re * w.im + z.im * w.re).Encloses (c * d).im
    rw [Complex.mul_im]
    exact FastReal.add_encloses (FastReal.mul_encloses hz.1 hw.2)
      (FastReal.mul_encloses hz.2 hw.1)

theorem conj_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (FastComplex.conj z).Encloses ((starRingEnd ℂ) c) := by
  refine ⟨?_, ?_⟩
  · show z.re.Encloses ((starRingEnd ℂ) c).re
    rw [Complex.conj_re]; exact hz.1
  · show (FastReal.neg z.im).Encloses ((starRingEnd ℂ) c).im
    rw [Complex.conj_im]; exact FastReal.neg_encloses hz.2

theorem pow_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    ∀ n : ℕ, (z ^ n).Encloses (c ^ n)
  | 0 => by
    show (FastComplex.pow z 0).Encloses (c ^ 0)
    rw [pow_zero]; exact encloses_one
  | n + 1 => by
    show (FastComplex.mul (FastComplex.pow z n) z).Encloses (c ^ (n + 1))
    rw [pow_succ]
    exact mul_encloses (pow_encloses hz n) hz

/-! ## Modulus -/

theorem normSq_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (z.normSq).Encloses (Complex.normSq c) := by
  show (z.re * z.re + z.im * z.im).Encloses (Complex.normSq c)
  rw [Complex.normSq_apply]
  exact FastReal.add_encloses (FastReal.mul_encloses hz.1 hz.1)
    (FastReal.mul_encloses hz.2 hz.2)

/-- **The executable modulus encloses the true norm** — the payoff of the
verified square root. -/
theorem abs_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    (z.abs).Encloses ‖c‖ := by
  show (FastReal.sqrt (FastReal.add (FastReal.mul z.re z.re)
    (FastReal.mul z.im z.im))).Encloses ‖c‖
  have hinner : (FastReal.add (FastReal.mul z.re z.re) (FastReal.mul z.im z.im)).Encloses
      (c.re * c.re + c.im * c.im) :=
    FastReal.add_encloses (FastReal.mul_encloses hz.1 hz.1)
      (FastReal.mul_encloses hz.2 hz.2)
  have hnn : (0 : ℝ) ≤ c.re * c.re + c.im * c.im :=
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h := FastReal.sqrt_sound hinner hnn
  rwa [show Real.sqrt (c.re * c.re + c.im * c.im) = ‖c‖ from by
    rw [Complex.norm_def, Complex.normSq_apply]] at h

/-! ## Equality certificates (`ℂ` has no order) -/

/-- Componentwise fueled equality test: `some true` only if both the real
and imaginary parts are decided equal. -/
def eqCF (z w : FastComplex) (fuel : ℕ := defaultFuel) : Option Bool := do
  let a ← eqF z.re w.re fuel
  let b ← eqF z.im w.im fuel
  pure (a && b)

/-- **Soundness of the complex equality certificate**: a decided
`eqCF z w = some true` proves the enclosed complexes are equal. -/
theorem eqCF_sound {z w : FastComplex} {c d : ℂ} {fuel : ℕ}
    (hz : z.Encloses c) (hw : w.Encloses d)
    (h : eqCF z w fuel = some true) : c = d := by
  unfold eqCF at h
  simp only [Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨ha', hb'⟩ := Bool.and_eq_true _ _ |>.mp hab
  subst ha'; subst hb'
  have hre : c.re = d.re := API.eqF_sound hz.1 hw.1 ha
  have him : c.im = d.im := API.eqF_sound hz.2 hw.2 hb
  exact Complex.ext hre him

/-! ## Demos -/

-- `(1 + I)(1 - I) = 2`, decided componentwise: expect `some true`.
#eval eqCF ((1 + FastComplex.I) * (1 - FastComplex.I)) 2

-- `I² = -1`: expect `some true`.
#eval eqCF (FastComplex.I * FastComplex.I) (-1)

-- `|3 + 4I| = 5`: expect a ball tightly around `5`.
#eval FastComplex.abs ⟨FastReal.ofDyadic ⟨3, 0⟩, FastReal.ofDyadic ⟨4, 0⟩⟩

end FastComplex

end Computable.Fast
