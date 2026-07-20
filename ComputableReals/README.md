# ComputableReals

A standalone Lean 4 development of **computable real (and complex) arithmetic**:
a fast executable engine, a verified specification model, and — the part that
matters — proofs connecting the two.

Nothing here imports `HopfieldNet`: the library builds on Mathlib alone, so
this directory plus its three-line `lakefile.lean` stanza can be lifted into a
repository of its own verbatim. That is the intended path — the Hopfield and
Boltzmann material that uses it stays behind in `HopfieldNet/CReals/`.

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

## Relationship to the Hopfield/Boltzmann layer

This library is generic: nothing in it mentions a neural network, and it
imports only Mathlib. The application layer that *does* — network energies,
Gibbs chains, the Quiver `NeuralNetwork` instance — lives in
[`HopfieldNet/CReals/`](../HopfieldNet/CReals) and imports this library.
There is exactly one copy of every file; nothing is duplicated between the
two trees.

Four files were originally *mixed*, with generic soundness lemmas
interleaved with network-specific applications. They were split rather than
dropped, and the theorems kept their names:

| generic half (here) | network half (`HopfieldNet/CReals/`) |
|---|---|
| `Refinement.lean` — Dyadic order, `Encloses`, `compare`/`leF`/`eqF` soundness | `descentCertified?_sound` → `Computable/EnergySound.lean` |
| `ExpSound.lean` — Taylor/squaring bounds, `expV`, verified logistic | Gibbs samplers → `Computable/NNGibbs.lean` |
| `FastLogistic.lean` — `logistic?`, `probPos?`, `decideBernoulli?` | Gibbs updates → `Computable/NNGibbs.lean` |
| `GibbsSound.lean` — `ofInterval_encloses`, `decideBernoulli?_sound` | `gibbsSiteUpdate?_sound` → `Computable/NNGibbs.lean` |

Splitting them exposed a real coupling defect: `Refinement.lean`, the
foundation of the soundness layer, used to import
`FastEnergy → API.Basic → NeuralNetwork`, so the *entire* verified stack
transitively depended on Hopfield code — an artifact of authoring order, not
mathematics. That edge is gone, and this library now depends on nothing but
Mathlib, which is what makes it extractable.

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
