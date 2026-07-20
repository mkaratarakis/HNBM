# ComputableReals

A standalone Lean 4 development of **computable real (and complex) arithmetic**:
a fast executable engine, a verified specification model, and — the part that
matters — proofs connecting the two.

This branch isolates the prototype from the Hopfield/Boltzmann code it grew up
inside. Nothing here imports `HopfieldNet`; the library builds on Mathlib alone
and the directory plus its three-line `lakefile.lean` stanza can be lifted into
a fresh repository verbatim.

```
lake build ComputableReals
```

45 modules, ~15,000 lines, **zero `sorry`s**.

## The three layers

**1. The engine — what runs.** `CRealsFast.lean` implements ball arithmetic
(dyadic midpoint ± radius, Arb-style) over GMP-backed `Int`, exposing
`FastReal = ℕ → Ball` with `exp`, `log`, `sqrt`, `sin`, `cos`, `atan`, `π`, and
a total, fuel-based `FastReal.compare`. Comparison is *undecidable* on
computable reals, so `compare` returns an `Option`: it either separates the two
balls, observes that both are exact radius-`0` points and compares them exactly
(this is what decides **ties**), or exhausts fuel and answers `none`. It never
hangs and never guesses. `Decision.lean` builds the generic fueled predicates
(`eqF`, `leF`, threshold steps) on top.

Measured accuracy: π, e and √2 come out **correct to 200 digits**, sin/cos/atan
and log to 60, in roughly two seconds. Enclosure is honest — `√2 · √2` returns
an interval straddling 2 rather than claiming exactness.

**2. The specification — what you prove against.** `CRealPre2/` and
`CRealPre2.lean` build `CReal` as a quotient of regular Cauchy sequences of
rationals, with the full ordered-field structure, a
`ConditionallyCompleteLinearOrder` instance (`CRealCCLOF.lean`), transcendental
functions (`CRealExp`, `CRealLog`, `CRealSigmoid`, `CRealSqrt`), and a bridge
`CReal →+* ℝ` (`CRealRealEquiv.lean`) for transferring theorems into Mathlib's
analysis. `CRealAQ*.lean` and `CRealsFastBackend.lean` give the
"approximate rationals" backend model with proved per-operation error bounds
and a ring equivalence to `CReal`. `SOTA.lean` is the façade tying it together.

**3. The soundness bridge — `Computable/`.** This is what makes the engine
trustworthy rather than merely accurate. `Refinement.lean` defines the
enclosure relation `Encloses` and proves the key theorem — a decided
`FastReal.compare` really implies the corresponding order on the enclosed
reals, so a decided comparison is a *proof*, not just a program's opinion.
`Preservation.lean`, `SqrtSound.lean`, `InvSound.lean`, `ExpSound.lean`,
`TrigSound.lean`, `GibbsSound.lean` and the `FastComplex*Sound.lean` files carry
enclosure through each operation. Note `ExpSound.expV`: an *unconditional*
verified exponential, repairing the fact that `Ball.exp`'s tolerance exit never
fires at practical precisions.

Complex arithmetic (`CComplex*.lean`, `FastComplex*.lean`) mirrors the same
three-layer structure.

## What was deliberately left out

The Hopfield/Boltzmann application layer stays in the `computable-complex`
branch: `FastEnergy.lean`, `EnergySound.lean`, `QuiverBridge.lean`,
`ComputableRealsBridge.lean`, `API/` (the `NeuralNetwork`-typed helpers and the
NN/HN test twins), `FastMatrixSound.lean`, and `Computable/Demos/`.

Four files there were *mixed* — generic soundness lemmas interleaved with
network-specific applications — and were split rather than dropped:

| file | kept | removed |
|---|---|---|
| `Refinement.lean` | Dyadic order, `Encloses`, `compare` soundness, `leF`/`eqF` soundness | `FastEnergy` descent certificates |
| `ExpSound.lean` | Taylor/squaring bounds, `expV`, verified logistic | Gibbs site/sweep samplers |
| `FastLogistic.lean` | `logistic?`, `probPos?`, `decideBernoulli?` | Gibbs updates over weight matrices |
| `GibbsSound.lean` | `ofInterval_encloses`, `decideBernoulli?_sound` | `gibbsSiteUpdate?_sound` |

Splitting these exposed a real coupling bug worth knowing about: on the source
branch the soundness stack's foundation, `Refinement.lean`, imported
`FastEnergy → API.Basic → NeuralNetwork`, so the *entire* verified layer
transitively depended on Hopfield code — purely an artifact of authoring order,
not mathematics. Here that edge is gone, and the generic core depends on
nothing but Mathlib.

## Known gap

`CRealAQDyadicEquiv.lean` (surjectivity of the dyadic backend) is present but
**not** imported by the root module, because it does not compile. It arrived
broken; its `Dyadic.ulp` and `pow_le_pow_of_le_left` bitrot is now repaired
(the first by reusing the equivalent bound already proved in
`CRealPreDyadic.lean`), taking it from 14 errors to 4. What remains is an
**ambiguous `≈`** at `repOfPre_toPre_equiv`: two `Setoid` instances on
`CReal.Pre` are simultaneously in scope, which looks like fallout from closing
the `RatCast`/`Field` instance diamond. Resolving that is a design decision
about which instance should win, so it is left flagged rather than patched.
