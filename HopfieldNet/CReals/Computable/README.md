# `CReals/Computable` — the refinement tower

A complete, `sorry`-free bridge from the repository's **executable** ball
arithmetic (`Computable.Fast.FastReal`, `ℕ → Ball` over dyadics) to the
**classical** real-number theory it refines. Every runtime certificate the
executable layer emits is upgraded here to a *theorem* about the honest
`ℝ`-valued dynamics — with no unproved obligations remaining.

All results in this folder depend only on the three standard Mathlib
axioms: `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`native_decide`).

## The one-way bridge, and why

`Computable.CReal ≃+* ℝ` exists as a ring/order isomorphism, but a
*computable* `ℝ → CReal` cannot: Mathlib's `ℝ` erases its Cauchy moduli
into `Prop`. So the architecture computes on the `FastReal` side and
transfers **theorems** to `ℝ` via enclosure — never the reverse. The one
irreducible cost of undecidability is the fueled `Option` layer: some
comparisons honestly return `none`, and no result here ever claims
otherwise.

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

## What is proved, in one line each

- **Deterministic dynamics** (`QuiverBridge.certified_run_energy_descent`):
  a decided run of the executable Hopfield network yields a provably
  non-increasing chain of the *real* Quiver energies along the
  corresponding `HopfieldNetwork ℝ` trajectory.
- **Stochastic dynamics** (`ExpSound.gibbsSweepV?_sound`): a decided
  verified Gibbs sweep encloses, state by state, the classical Gibbs
  trajectory driven by the same uniform samples.

Both are unconditional: every hypothesis is an enclosure built structurally
from numeric literals and ring operations.

## The honest asterisk

`Ball.exp`'s tolerance `2^(prec−4)` sits *below* its per-operation rounding
error `2^(prec−1)`, so its tolerance exit never fires at working precisions
and the conditional `exp_sound` is vacuous there (its numerics are fine; its
guarantee is not). `expV` — three lines, originals untouched — adds the
geometric tail on both exits and is unconditionally sound. The verified
stochastic layer is built on `expV`.
