# CReals — the Hopfield/Boltzmann application layer

The generic computable-real and computable-complex machinery no longer lives
here. It was extracted into the standalone [`ComputableReals`](../../ComputableReals)
library at the repository root, which depends on Mathlib alone and is
intended to be lifted into its own repository.

What remains in this folder is exactly the part that mentions a neural
network: a weight matrix, an energy, a Gibbs chain, or the Quiver-based
`NeuralNetwork` structure. Each file here imports the generic layer from
`ComputableReals.*` and adds the network-specific content on top.

## Contents

- `API/Basic.lean` — the `NeuralNetwork`-typed helpers: the fueled stability
  test `isStableF` and the certified stabilizer `stabilizeF`. The generic
  fueled predicates they are built from (`eqF`, `leF`, `binaryStep`,
  `signStep`, `actsToInts`) live in `ComputableReals/Decision.lean`.
- `API/NNtest.lean` — 3-neuron threshold network; both update sequences give
  `[1, 1, 1]`, and the run hits the exact tie `net = θ` and decides it.
- `API/HNtest.lean` — 4-neuron Hebbian Hopfield network matching the `ℚ`
  test exactly: stable state `[-1, 1, -1, 1]`, convergence in 2 steps.
- `Computable/FastEnergy.lean` — executable network energy and descent
  certificates over `FastReal`.
- `Computable/EnergySound.lean` — enclosure for the energy (`netF_encloses`,
  `EF_encloses`) and `descentCertified?_sound`: a certified descent really is
  a non-increasing chain of the enclosed `ℝ`-valued energies.
- `Computable/NNGibbs.lean` — executable Gibbs sampling and its soundness:
  `gibbsSiteUpdate?`/`gibbsSweep?` and the verified `…V?` variants built on
  the unconditional `expV`, with `gibbsSweepV?_sound` showing the executable
  chain is the true Gibbs chain.
- `Computable/QuiverBridge.lean` — connects the fueled activation steps to
  the Quiver `HopfieldNetwork` instance.
- `Computable/FastMatrixSound.lean` — enclosure for complex matrices, used
  for the unitarity certificates.
- `Computable/Demos/` — runnable Gibbs and contrastive-divergence demos.
- `ComputableRealsBridge.lean` — `HasToReal`/`IsHamiltonianR` and the
  transfer of energy statements into Mathlib's analysis.

## Note on the split

`Computable/NNGibbs.lean` was assembled from the network-specific halves of
four previously mixed files (`Refinement`, `ExpSound`, `FastLogistic`,
`GibbsSound`), whose generic halves moved to `ComputableReals`. The
mathematics is unchanged; the theorems kept their names.

Splitting them removed an accidental dependency worth remembering: the
soundness foundation `Refinement.lean` used to import
`FastEnergy → API.Basic → NeuralNetwork`, so the entire verified layer
transitively depended on Hopfield code for no mathematical reason. Files
that genuinely need `FastEnergy` (such as `EnergySound.lean`) now say so
explicitly instead of inheriting it by accident.
