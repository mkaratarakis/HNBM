/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.Quiver.HN.HNquivHebbian
import ComputableReals.CRealCCLOF

/-!
# Computable reals bridge (principled theorem-transfer layer)

This module makes the "noncomputable stuff" available over computable reals,
in the only direction that is possible in principle:

* **Theorems over `CReal`, for free.** `CRealCCLOF` equips `Computable.CReal`
  with (noncomputable, classical) `Field`, `LinearOrder`,
  `IsStrictOrderedRing` instances — exactly the hypotheses of the generic
  Quiver development. Hence `HopfieldNetwork CReal U`, `Hebbian`, and every
  theorem about them *instantiate at `CReal` by substitution* (see the
  examples at the bottom). These instances are classical, so this layer
  proves but does not execute.

* **`ℝ`-semantics for `CReal` results.** `HasToReal`/`HasToRealOrder`
  package the ring hom `Computable.CReal.toRealRingHom : CReal →+* ℝ` and
  its order-compatibility, so scalar-valued quantities (energies, fields)
  push forward to `ℝ` where Mathlib's analysis applies —
  `IsHamiltonianR.energyToReal_is_lyapunov` is the template.

* **Execution stays in `CReals/API/`.** The executable layer (`FastReal`
  folds, fueled comparisons, decidedness certificates) computes; this file
  gives those computations their `ℝ`-level meaning. A computable
  `ℝ → CReal` cannot exist (Mathlib's `ℝ` erases moduli of convergence into
  `Prop`), which is why the bridge is a one-way ring hom and not a
  computability transport.
-/

open Finset Matrix NeuralNetwork State Fintype Computable

namespace NeuralNetwork

variable {R U ζ : Type}

/-- A scalar type that can be mapped into `ℝ` as a ring homomorphism. -/
class HasToReal (R : Type) [NonAssocSemiring R] where
  toRealRingHom : R →+* ℝ

/-- Optional strengthening: the map to `ℝ` is monotone for the order on `R`.
This is what you need to transport Lyapunov (energy non-increase)
inequalities. -/
class HasToRealOrder (R : Type) [NonAssocSemiring R] [LE R] extends HasToReal R where
  mono_toReal : ∀ {a b : R}, a ≤ b → toRealRingHom a ≤ toRealRingHom b

namespace HasToRealOrder

variable [NonAssocSemiring R] [LE R] [HasToRealOrder R]

lemma toReal_mono {a b : R} (h : a ≤ b) :
    HasToReal.toRealRingHom (R := R) a ≤ HasToReal.toRealRingHom (R := R) b :=
  HasToRealOrder.mono_toReal (R := R) h

end HasToRealOrder

/-- Instance: `Computable.CReal` maps to `ℝ` via the existing ring hom. -/
instance : HasToReal CReal where
  toRealRingHom := CReal.toRealRingHom

/-- Instance: the `Computable.CReal` order is compatible with `toReal`. -/
instance : HasToRealOrder CReal where
  mono_toReal := fun hab => CReal.toReal_mono hab

/-- Trivial instance: `ℝ` maps to itself. -/
instance : HasToReal ℝ where
  toRealRingHom := RingHom.id ℝ

instance : HasToRealOrder ℝ where
  mono_toReal := fun hab => by simpa using hab

/-- Hamiltonian structure where the energy is valued in a scalar `R`
(e.g. `CReal`), but can be pushed to `ℝ` via `HasToReal`. This is the most
direct way to keep the *model* in `R` while reusing `ℝ`-theory. -/
class IsHamiltonianR [NonAssocSemiring R] [LE R] (NN : NeuralNetwork R U ζ)
    [DecidableEq U] where
  energy : Params NN → NN.State → R
  energy_is_lyapunov :
    ∀ (p : Params NN) (s : NN.State) (u : U), energy p (s.Up p u) ≤ energy p s

namespace IsHamiltonianR

variable [NonAssocSemiring R] [LE R] [HasToRealOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U ζ) [IsHamiltonianR NN]

/-- The induced `ℝ`-valued energy function obtained by pushing through
`toReal`. -/
def energyToReal (p : Params NN) : NN.State → ℝ :=
  fun s => (HasToReal.toRealRingHom (R := R)) (IsHamiltonianR.energy (NN := NN) p s)

/-- The Lyapunov property survives the push-forward: an energy that is
non-increasing over `R` induces a non-increasing `ℝ`-valued energy. -/
lemma energyToReal_is_lyapunov (p : Params NN) (s : NN.State) (u : U) :
    energyToReal NN p (s.Up p u) ≤ energyToReal NN p s := by
  dsimp [energyToReal]
  exact HasToRealOrder.toReal_mono (R := R)
    (IsHamiltonianR.energy_is_lyapunov (NN := NN) p s u)

end IsHamiltonianR

end NeuralNetwork

/-!
## The noncomputable theory, instantiated at `CReal`

`CRealCCLOF` provides everything `HopfieldNetwork R U` demands, so the whole
generic development specializes to computable reals by mere substitution —
no porting required. (The instances are classical: this layer is for
theorems; execution is `CReals/API/`'s job.)
-/

section CRealInstantiation

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

/-- The Hopfield network over computable reals: type-checks because `CReal`
carries `Field`, `LinearOrder`, `IsStrictOrderedRing` (from `CRealCCLOF`). -/
noncomputable example : NeuralNetwork CReal U CReal := HopfieldNetwork CReal U

/-- The non-orthogonal Hebbian decomposition
`(Hebbian ps).w *ᵥ pⱼ = (card U - m) • pⱼ + disturbanceTerm ps j` — the
theorem whose executable twin is certified in `CReals/API/HNtest.lean` —
holds over `CReal` by instantiation. -/
noncomputable def hebbianDecomposition_creal {m : ℕ}
    (ps : Fin m → (HopfieldNetwork CReal U).State) (j : Fin m) :=
  patterns_pairwise_non_orthogonal ps j

/-- For pairwise-orthogonal patterns, the Hebbian field on a stored pattern
is the pure signal `(card U - m) * pⱼ`, over `CReal` by instantiation. -/
noncomputable def hebbianOrthogonalField_creal {m : ℕ}
    (ps : Fin m → (HopfieldNetwork CReal U).State)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0) :=
  patterns_pairwise_orthogonal ps (fun h => horth h)

end CRealInstantiation
