# ComputableReals

A standalone Lean 4 development of **computable real (and complex) arithmetic**:
a fast executable engine, a verified specification model, and — the part that
matters — proofs connecting the two.

Depends on Mathlib and nothing else.

```
lake exe cache get   # fetch Mathlib build artifacts (first time)
lake build
```

53 modules, ~16,000 lines, **zero `sorry`s**.

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
  and vectors, carried through `mul`, `mulVec` (propagating a state through a
  device), `kron` (composing modes), `conjTranspose`, `trace`, `transpose`
  and the linear operations, so a `unitaryUpTo` certificate is a statement
  about the true complex matrix rather than about floating-point residue.
- `CComplexTrans.lean` — `exp`, `log`, `sin`, `cos`, `sqrt` and `arg` on the
  specification model. These are transported along `CComplex ≃+* ℂ` and so
  are noncomputable; an intrinsic construction awaits total `CReal.exp`,
  `CReal.cos` and `CReal.sin`, which do not exist yet.
- `FastComplexMatrixExamples.lean` — a beam splitter and a phase shifter,
  their composition `UPU φ`, and Kronecker products of unitaries, all
  certified unitary; plus a deliberate negative test (`2·U` is not unitary,
  certificate `false`).

### Certified components

`Computable/ComponentsSound.lean` closes the loop. `unitaryUpTo_sound` needs
an `Encloses` hypothesis, and until recently nothing discharged it for an
actual component — the `#eval`s said "the certificate fired", not "this beam
splitter is unitary". Now:

- `beamSplitterV` encloses `bsM`, and `bsM * bsMᴴ = 1` **exactly**;
- `phaseShifterV φ` encloses `psM φ`, and `psM φ * (psM φ)ᴴ = 1` **exactly**;
- `mzV φ` (a Mach–Zehnder-style `BS · P(φ) · BS`) encloses `mzM φ`, unitary
  as a product of unitaries.

Because the enclosed matrices are exactly unitary, these conclusions carry no
tolerance at all: the executable object you can `#eval` is paired with a
theorem about the complex matrix it denotes, and composition needs no new
numerical reasoning — `mul_encloses` carries the enclosure through.

### Verified vs runtime primitives

As with `exp`/`expV` on the reals, the complex layer distinguishes the fast
unproven primitives from the verified ones.
`Computable/FastComplexTransSound.lean` supplies `expV`, `cosV`, `sinV` and
`fromPolarV`, built on the verified real `expV`/`cosV`/`sinV` and proved
against Mathlib's `Complex.exp`, `cos` and `sin`. Prefer the `V` forms when a
theorem is wanted; the unadorned ones are faster and remain unproven.

### The complex square root

`Computable/SqrtComplexSound.lean`. This is the first genuinely
*branch-dependent* function here, and the branch cannot always be chosen
computably: the principal root of `a + bi` takes its imaginary sign from the
sign of `b`, and deciding `b < 0` is undecidable when `b = 0`. A total
verified complex `sqrt` therefore cannot exist, for the same reason a
decidable order cannot.

`sqrtV?` is the fueled version: it asks `compare` for the sign of the
imaginary part and, when that is decided — which includes the exact-zero
case, since radius-`0` balls compare exactly — returns the principal root;
otherwise `none`. `sqrtV?_sound` proves the answer encloses `principalSqrt`,
and `principalSqrt_sq` proves that really is a square root
(`principalSqrt c * principalSqrt c = c`), so `sqrtV?_sq` gives the
end-to-end statement: what the engine returns encloses a genuine square root
of the enclosed value.

Soundness is stated against the closed form rather than `c ^ (1/2 : ℂ)`
deliberately — `cpow` unfolds through `Complex.log` and hence `arg`, neither
of which is verified here (see **Known gaps**).

### Logarithm and argument

`Computable/LogArgSound.lean`. These were the last unverified functions, and
both were blocked at the *real* layer — `FastReal.log?` and `FastReal.atan`
run but carry no soundness theorems, and re-deriving them as series with
error bounds would repeat the whole of `ExpSound`.

They are instead certified as *inverses* of functions that are already
verified, which needs no series analysis at all:

> to prove `L ≤ log r ≤ H` it suffices to check `exp L ≤ r ≤ exp H`,
> because `exp` is monotone.

So the search for a bracket need not be verified — only the final check.
`logBracket` inverts `expV`; `arctanBracket` inverts `tan = sinV / cosV`,
phrased as `sin lo ≤ y · cos lo` so no division is needed; `argBracket`
certifies `Complex.arg` on the right half-plane, where
`arg z = arctan (im z / re z)`; and `logC_encloses` assembles the complex
logarithm from the first and third via `Complex.log_re` / `log_im`. This is
the same discipline as `unitaryUpTo`: an executable predicate whose `true`
answer is a theorem, and which returns `false` rather than lying when it
cannot certify.

### The refinement triangle

`Computable/CComplexRefine.lean` relates the two models directly:
`FastComplex.EnclosesC z w` says the executable `z` encloses the
*specification* value `w`, and every operation — arithmetic and the verified
transcendentals — respects it. So a theorem proved in `CComplex`, where you
have a field and can rewrite freely, transfers to a statement about what the
engine actually computes, without unfolding a ball.

## Provenance

Extracted from the `HopfieldNet`/`HNBM` development, where this material grew
up alongside Hopfield-network and Boltzmann-machine formalization. The
application layer that uses it stayed behind there; everything here is
generic and imports only Mathlib. Theorem names were preserved through the
split, so results stay citable across both repositories.

## Known gaps

**Precision monotonicity.** Nothing states that increasing precision shrinks
a ball's radius; that needs engine-level convergence facts which do not
exist yet. Structural congruence lemmas for `Encloses` are provided instead.

**`arg` outside the right half-plane.** `argBracket` is stated for
`re z > 0`, where the argument lies in `(-π/2, π/2)` and equals an
arctangent. The other quadrants need the usual `±π` case split, which is
mechanical but not yet written.

**Bracket search.** The soundness theorems take the bracket endpoints as
given, and the accompanying `#eval`s use hand-chosen dyadics. An automatic
bisection that proposes endpoints would be convenient; it needs no proof,
since correctness rests entirely on the certificate.

**`CRealAQDyadicEquiv.lean`** is present but not imported by the root module:
it arrived broken, its `Dyadic.ulp` and `pow_le_pow_of_le_left` bitrot is
repaired, and what remains is an ambiguous `≈` from two `Setoid` instances on
`CReal.Pre` in scope — a design decision about which instance should win,
left flagged rather than patched.
