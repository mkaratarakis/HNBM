# `CReals/Computable` — the refinement tower

A complete, `sorry`-free bridge from the repository's **executable** ball
arithmetic (`Computable.Fast.FastReal`, `ℕ → Ball` over dyadics — and its
complex extension `FastComplex`/`FastMatrix`) to the **classical**
real- and complex-number theory it refines. Every runtime certificate the
executable layer emits is upgraded here to a *theorem* about the honest
`ℝ`- and `ℂ`-valued objects — with no unproved obligations remaining.

All results in this folder depend only on the three standard Mathlib
axioms: `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`native_decide`).

## The one-way bridge, and why

`Computable.CReal ≃+* ℝ` (and `CComplex ≃+* ℂ`) exists as a ring/order
isomorphism, but a *computable* `ℝ → CReal` cannot: Mathlib's `ℝ` erases
its Cauchy moduli into `Prop`. So the architecture computes on the
`FastReal`/`FastComplex` side and transfers **theorems** to `ℝ`/`ℂ` via
enclosure — never the reverse. The one irreducible cost of undecidability
is the fueled `Option` layer: some comparisons honestly return `none`, and
no result here ever claims otherwise.

## Files, bottom to top

| File | Role |
|---|---|
| `FastEnergy.lean` | Executable Hopfield energy (`EF`) + fueled descent certificates; the 4-neuron Hebbian demo. |
| `FastLogistic.lean` | Executable logistic / `probPos` / one-site Gibbs sampler (a `PMF` replaced by a dyadic-sample-driven decision). |
| `Refinement.lean` | `Ball.Encloses` / `FastReal.Encloses`; **`compare_sound`** — a decided fueled comparison truthfully orders any enclosed reals (separation *and* exact-tie branches); descent certificates ⇒ real non-increasing chains. |
| `Preservation.lean` | Enclosure is preserved by `neg`/`add`/`sub`/`mul`; certified dyadic rounding bounds (`round` ≤ ½ ulp, `roundUp` monotone). |
| `EnergySound.lean` | Enclosure lifts through folds; `EF_encloses`; **`certified_descent_real`** and the fully-discharged `demo_real_descent` (proved by kernel `decide`). |
| `QuiverBridge.lean` | `signStep_sound`; `ER_eq_E` (the fold energy **is** `NeuralNetwork.State.E`); **`certified_run_energy_descent`** — certified runs of `HopfieldFast` refine the classical `HopfieldNetwork ℝ` trajectory. |
| `GibbsSound.lean` | `ofInterval_encloses`; **`decideBernoulli?_sound`** and `gibbsSiteUpdate?_sound` — the sampler samples the true Bernoulli distribution (conditional on a sound probability approximator). |
| `InvSound.lean` | Directed division bounds; **`Ball.inv?_sound`**; `logistic?_sound` modulo `exp`. |
| `ExpSound.lean` | `taylor_sound` + `Ball.exp_sound` (conditional on the `expExits` certificate); the honest finding that `Ball.exp`'s tolerance is vacuous at practical precisions; the repair **`expV`** with *unconditional* `expV_sound`; and the closing theorems `gibbsSiteUpdateV?_sound` / `gibbsSweepV?_sound` — the verified Gibbs chain **is** the classical Gibbs chain, sample for sample. |
| `SqrtSound.lean` | Directed dyadic-root bounds (`sqrt_toRat_le` / `le_sqrtUp_toRat`) via `Nat.sqrt` bracketing; **`FastReal.sqrt_sound`** — the executable √ encloses `Real.sqrt` (unconditional; no series tail). Completes the primitive set. |
| `FastComplexSound.lean` | Componentwise `FastComplex.Encloses`; `add`/`mul`/`conj`/`pow`_encloses; `normSq_encloses`; **`abs_encloses`** (√(re²+im²) encloses `‖c‖`); `eqCF_sound` — the `ℂ` equality certificate (no order on `ℂ`). |
| `FastMatrixSound.lean` | Entrywise `FastMatrix.Encloses`; `sumFin`/`mul`/`conjTranspose`_encloses; `certSmallC_sound`; **`unitaryUpTo_sound`** — a `true` unitarity certificate proves the `ℂ`-matrix is unitary to `2^{-tol}`. Demo: a Hadamard beam splitter certifies `true`. |

## What is proved, in one line each

- **Deterministic dynamics** (`QuiverBridge.certified_run_energy_descent`):
  a decided run of the executable Hopfield network yields a provably
  non-increasing chain of the *real* Quiver energies along the
  corresponding `HopfieldNetwork ℝ` trajectory.
- **Stochastic dynamics** (`ExpSound.gibbsSweepV?_sound`): a decided
  verified Gibbs sweep encloses, state by state, the classical Gibbs
  trajectory driven by the same uniform samples.
- **Complex unitarity** (`FastMatrixSound.unitaryUpTo_sound`): a `true`
  executable unitarity certificate proves the enclosed Mathlib `ℂ`-matrix
  satisfies `|(M·Mᴴ − 1)ᵢⱼ| < 2^{-tol}` entrywise — rigorous optics.

The first two are unconditional; the third is conditional only on the
input matrix enclosing `M` (which holds by construction for literal
amplitudes and the verified `√`). Every hypothesis is an enclosure built
structurally from numeric literals and ring operations.

## Coverage: the verified executable primitive set

`compare`, `+`, `−`, `neg`, `*` (`Refinement`/`Preservation`); `inv?`
(`InvSound`); `exp` (`ExpSound`, via `expV`); `√` (`SqrtSound`) — over
`ℝ`. Complex `+`/`−`/`*`/`conj`/`pow`/`normSq`/`abs` and matrix
`mul`/`conjTranspose` over `ℂ` (`FastComplexSound`/`FastMatrixSound`).

## The honest asterisk

`Ball.exp`'s tolerance `2^(prec−4)` sits *below* its per-operation rounding
error `2^(prec−1)`, so its tolerance exit never fires at working precisions
and the conditional `exp_sound` is vacuous there (its numerics are fine; its
guarantee is not). `expV` — three lines, originals untouched — adds the
geometric tail on both exits and is unconditionally sound. The verified
stochastic layer is built on `expV`.
