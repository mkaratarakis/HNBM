/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CComplexTrans
import ComputableReals.Computable.FastComplexTransSound

/-!
# The refinement triangle: `FastComplex` ⇝ `CComplex`

There are two models of the computable complex numbers in this library and,
until now, no statement relating them directly:

* `CComplex` — the specification model, a `Field` with a ring isomorphism
  `CComplex ≃+* ℂ` (`CComplexBridge.complexRingEquiv`);
* `FastComplex` — the executable model, whose soundness theorems are stated
  as enclosure of a Mathlib `ℂ`.

Both are anchored to `ℂ`, so the triangle closes: an executable value
encloses a *specification* value exactly when it encloses that value's image
in `ℂ`. That is the definition of `EnclosesC` below, and everything else in
this file is the observation that each operation respects it — the
executable arithmetic refines the specification arithmetic, and the verified
transcendental functions refine the specification's transcendental
functions.

The practical consequence: a theorem proved about `CComplex` (where you have
a field, and can rewrite freely) transfers to a statement about what the
executable engine actually computes, without ever unfolding a ball.
-/

open Computable Computable.Fast

namespace Computable.Fast

namespace FastComplex

/-- An executable complex number **encloses a specification complex number**
when it encloses its image in `ℂ`. -/
def EnclosesC (z : FastComplex) (w : Computable.CComplex) : Prop :=
  z.Encloses (Computable.CComplex.toComplex w)

/-! ## Arithmetic refines arithmetic -/

theorem enclosesC_zero : (0 : FastComplex).EnclosesC 0 := by
  simpa [EnclosesC] using encloses_zero

theorem enclosesC_one : (1 : FastComplex).EnclosesC 1 := by
  simpa [EnclosesC] using encloses_one

theorem add_enclosesC {z w : FastComplex} {a b : Computable.CComplex}
    (hz : z.EnclosesC a) (hw : w.EnclosesC b) : (z + w).EnclosesC (a + b) := by
  simpa [EnclosesC] using add_encloses hz hw

theorem mul_enclosesC {z w : FastComplex} {a b : Computable.CComplex}
    (hz : z.EnclosesC a) (hw : w.EnclosesC b) : (z * w).EnclosesC (a * b) := by
  simpa [EnclosesC] using mul_encloses hz hw

theorem neg_enclosesC {z : FastComplex} {a : Computable.CComplex}
    (hz : z.EnclosesC a) : (FastComplex.neg z).EnclosesC (-a) := by
  simpa [EnclosesC] using neg_encloses hz

theorem sub_enclosesC {z w : FastComplex} {a b : Computable.CComplex}
    (hz : z.EnclosesC a) (hw : w.EnclosesC b) : (z - w).EnclosesC (a - b) := by
  simpa [EnclosesC] using sub_encloses hz hw

theorem pow_enclosesC {z : FastComplex} {a : Computable.CComplex} (n : ℕ)
    (hz : z.EnclosesC a) : (z ^ n).EnclosesC (a ^ n) := by
  simpa [EnclosesC] using pow_encloses hz n

/-! ## The verified transcendental functions refine the specification's

Each of these says: what the engine computes for `exp`/`cos`/`sin` really
does enclose the specification model's `exp`/`cos`/`sin` of the enclosed
argument. Both sides are anchored to the same Mathlib function, so the
proofs are one rewrite each — which is the point. The content was in
establishing the two anchors.
-/

/-- The verified complex exponential refines `CComplex.exp`. -/
theorem expV_enclosesC {z : FastComplex} {a : Computable.CComplex}
    (hz : z.EnclosesC a) : (expV z).EnclosesC (Computable.CComplex.exp a) := by
  simpa [EnclosesC] using expV_sound hz

/-- The verified complex cosine refines `CComplex.cos`. -/
theorem cosV_enclosesC {z : FastComplex} {a : Computable.CComplex}
    (hz : z.EnclosesC a) : (cosV z).EnclosesC (Computable.CComplex.cos a) := by
  simpa [EnclosesC] using cosV_sound hz

/-- The verified complex sine refines `CComplex.sin`. -/
theorem sinV_enclosesC {z : FastComplex} {a : Computable.CComplex}
    (hz : z.EnclosesC a) : (sinV z).EnclosesC (Computable.CComplex.sin a) := by
  simpa [EnclosesC] using sinV_sound hz

/-! ## Transfer

`EnclosesC` is definitionally enclosure of the image, so a specification
statement and an executable one are interchangeable.
-/

theorem enclosesC_iff {z : FastComplex} {a : Computable.CComplex} :
    z.EnclosesC a ↔ z.Encloses (Computable.CComplex.toComplex a) := Iff.rfl

/-- Any Mathlib complex is the image of a specification complex, so an
enclosure statement can always be read in the specification model. -/
theorem enclosesC_of_encloses {z : FastComplex} {c : ℂ} (hz : z.Encloses c) :
    z.EnclosesC (Computable.CComplex.ofComplex c) := by
  unfold EnclosesC
  rwa [Computable.CComplex.toComplex_ofComplex]

end FastComplex

end Computable.Fast
