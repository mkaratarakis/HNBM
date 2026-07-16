# Computable reals (`CReals`) and executable NN computations

Migrated from `mkaratarakis/HopfieldNet` (branch `creal-nn-run`) to this
repository's toolchain (Lean v4.30.0) and Quiver-based `NeuralNetwork` API.

## Layout

**The computation path** (what you `#eval`):

- `CRealsFast.lean` — the execution engine: ball arithmetic (dyadic midpoint
  ± radius) over GMP-backed `Int`, with `exp`, `sqrt`, `π`, and a total,
  fuel-based `FastReal.compare`. Two improvements over the original:
  rounding error is added to the radius *only when rounding actually changed
  the midpoint* (so exact dyadic computations stay radius-0 end-to-end), and
  `compare` decides **exact ties** (`some .eq`) when both balls are points.
- `CRealsFastExamples.lean` — engine demos (`exp 1`, `π` to 12 digits, …).
- `API/Basic.lean` — fueled comparisons (`eqF`, `leF`), executable threshold
  activations (`binaryStep`, `signStep`), integer rendering of states, and a
  generic certified stabilizer `stabilizeF` for any
  `NeuralNetwork FastReal (Fin n) FastReal`. Stability is *decided*, never
  assumed: results carry decidedness certificates.
- `API/NNtest.lean` — 3-neuron threshold network: both update sequences give
  `[1, 1, 1]`; the run hits the exact tie `net = 0` and decides it.
- `API/HNtest.lean` — 4-neuron Hebbian Hopfield network, matching the `ℚ`
  test exactly: stable state `[-1, 1, -1, 1]`, convergence in 2 steps, both
  stored patterns verified as fixed points.

**The specification stack** (what you prove against):

- `CRealPre2/` + `CRealPre2.lean` — spec model: quotient of regular Cauchy
  sequences of rationals, with ring/order theory.
- `CRealAQ.lean`, `CRealAQOrder.lean`, `CRealRep.lean` — implementation
  model over "approximate rationals" backends, with proved equivalences
  (`CRealAQBackendEquiv.lean`).
- `CRealRealEquiv.lean` — bridge `CReal →+* ℝ` for theorem transfer.
- `CRealExp*.lean`, `CRealLog.lean`, `CRealSigmoid.lean` — exp/log/sigmoid
  on the spec model (sigmoid is the Boltzmann-machine ingredient).
- `CRealCCLOF.lean` — `CReal` is a conditionally complete linear ordered
  field (ported to the v4.30 `isLUB_csSup`/`isGLB_csInf` API).
- `SOTA.lean` — the façade: prove against `RealSpec`, run against
  `RealImpl`/`FastReal`.

## Build status (Lean v4.30.0, Mathlib v4.30.0)

Everything builds and all `#eval`s produce the expected results, **except**
two files with known v4.27→v4.30 bitrot (nothing else depends on them):

- `CRealAQDyadicEquiv.lean` — uses `Dyadic.ulp`, removed from Mathlib's
  `Dyadic` API; plus `pow_le_pow_of_le_left` rename fallout.
- `Examples.lean` — spec-model demos; v4.30 routes `Mul CReal`/`toString`
  through the (intentionally) noncomputable `Field CReal` instance, so the
  `#eval`s no longer compile. The executable demos live in
  `CRealsFastExamples.lean` and `API/` instead.

```
lake build HopfieldNet.CReals.API.NNtest HopfieldNet.CReals.API.HNtest
lake build HopfieldNet.CReals.SOTA
```
