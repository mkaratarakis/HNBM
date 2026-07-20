# ComputableReals

A standalone Lean 4 development of **computable real (and complex) arithmetic**:
a fast executable engine, a verified specification model, and — the part that
matters — proofs connecting the two.

Depends on Mathlib and nothing else.

```
lake exe cache get   # fetch Mathlib build artifacts (first time)
lake build
```

47 modules, ~15,000 lines, **zero `sorry`s**.

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

## Complex arithmetic and the optics stack

Complex numbers mirror the same three layers: `CComplex*.lean` on the
specification side, `FastComplex*.lean` on the executable side, and
`Computable/FastComplexSound.lean`, `FastComplexDivSound.lean` and
`TrigSound.lean` connecting them (the last gives verified `sin`/`cos` and
hence the phase factor `e^{iφ}`).

On top of that sits the linear-algebra layer that photonics needs:

- `FastComplexMatrix.lean` — executable complex matrices with `mul`,
  `mulVec`, `conjTranspose`, the Kronecker product `kron`, and the
  certificate `unitaryUpTo`, which checks `U†U = I` to a given precision and
  answers honestly (`false` when it cannot certify).
- `Computable/FastMatrixSound.lean` — the enclosure relation for matrices
  and the theorems carrying it through the operations, so a `unitaryUpTo`
  certificate is a statement about the true complex matrix rather than about
  floating-point residue.
- `FastComplexMatrixExamples.lean` — a beam splitter and a phase shifter,
  their composition `UPU φ`, and Kronecker products of unitaries, all
  certified unitary; plus a deliberate negative test (`2·U` is not unitary,
  certificate `false`).

A beam splitter composed with a phase shifter, verified unitary and
evaluated at arbitrary precision, is a two-mode interferometer — the base
case for the optics work this library is intended to support.

## Provenance

Extracted from the `HopfieldNet`/`HNBM` development, where this material grew
up alongside Hopfield-network and Boltzmann-machine formalization. The
application layer that uses it stayed behind there; everything here is
generic and imports only Mathlib. Theorem names were preserved through the
split, so results stay citable across both repositories.

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
