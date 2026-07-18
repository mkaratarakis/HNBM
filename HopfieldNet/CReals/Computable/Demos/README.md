# `CReals/Computable/Demos` — runnable Boltzmann-machine computations

Self-contained `#eval` demonstrations that **actually run** the executable
(`FastReal`-backed) Hopfield/Boltzmann dynamics. Every number below is produced
by evaluation at build time — open a file, hit build, read the `info:` output.
These are the same combinators whose `…Sound` twins (`Computable/*Sound.lean`)
prove the runs refine the classical `ℝ`-valued dynamics, so the outputs are not
just plausible — they are certified to track the true chain.

## `GibbsRun.lean` — multi-sweep Gibbs sampling on a trained network

Drives `FastLogistic.gibbsSweep?` on the Hebbian weights trained on the patterns
`[1,1,-1,-1]` and `[-1,1,-1,1]`. Verified by evaluation:

| computation | result |
|---|---|
| low-`T` recall (`β=4`) from corrupted `[1,1,-1,1]` | `[1,1,-1,1] → [-1,1,-1,1] → …` (recovers the stored pattern, then fixed) |
| energy along the sampled chain | `[0, -4, -4, -4, -4]` (settles to the pattern minimum) |
| infinite-`T` (`β=0`), sample `r=1/4` | `[1,1,1,1]` (sample-driven, ignores the weights) |
| energy of corrupted vs. recovered | `0` vs. `-4` |

## `ContrastiveDivergence.lean` — executable CD-1

CD-1 for a fully-visible Boltzmann machine, built from the Gibbs primitives
(there is no executable CD elsewhere — the math-layer
`BoltzmannLearningQuiver/ContrastiveDivergence.lean` is noncomputable). The
weight gradient is `Δw = outer v − outer v'`, with `v'` one Gibbs reconstruction
sweep. Verified by evaluation:

| computation | result |
|---|---|
| `Δw` on a **stored** pattern | the all-zero matrix (converged — nothing to learn) |
| reconstruction of a stored pattern | the pattern itself (a model fixed point) |
| `Δw` on a **novel** pattern `[1,1,1,1]` | `[[0,0,2,2],[0,0,2,2],[2,2,0,0],[2,2,0,0]]` (a corrective gradient) |
| positive-phase correlation `outer v` | equals the single-pattern Hebbian matrix (CD-1 ≈ Hebb for one example) |

## What runs, and what cannot

The **dynamics** (Gibbs sampling, energy descent, CD correlations) run because
they live on the dyadic ball layer. The **measure-theoretic theory** (the Gibbs
`PMF`, CD convergence, detailed balance) stays noncomputable by nature —
Mathlib's `ℝ` erases the moduli a sampler would need. The bridge is one-way:
compute on `FastReal`, transfer *theorems* to `ℝ`. The only visible cost of
undecidability is the honest `Option` — a certified value is `some …`, and a
comparison that could not be decided within fuel is `none`, never a guess.
