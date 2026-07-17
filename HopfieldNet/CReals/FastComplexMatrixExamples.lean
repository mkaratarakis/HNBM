import HopfieldNet.CReals.FastComplexMatrix

open Computable.Fast Computable.Fast.FastMatrix Computable.Fast.Photonics

namespace Computable.Fast.FastComplexMatrixExamples
set_option autoImplicit false
/-!
Executable smoke tests for `FastMatrix` and the photonic devices.
-/

-- The beam splitter matrix itself: (1/√2)·[[1, i], [i, 1]]
#eval IO.println (toDecimal beamSplitter 8)

-- BS · BS = [[0, i], [i, 0]]: a photon entering mode 1 exits mode 2 with phase i
#eval IO.println (toDecimal (beamSplitter * beamSplitter) 8)

-- Rigorous unitarity certificates: every entry of U·Uᴴ - 1 certified < 2⁻²⁰
#eval unitaryUpTo beamSplitter 20
#eval unitaryUpTo (phaseShifter FastReal.pi) 20
#eval unitaryUpTo (mzi (FastReal.mul FastReal.pi (FastReal.ofDyadic ⟨1, -1⟩))) 20

-- 4-mode circuit (BS ⊗ BS) stays unitary
#eval unitaryUpTo twoBeamSplitters 20

-- Balanced MZI at φ = π/2: |t₀₀|² = |t₀₁|² = 1/2 (50:50 output)
def mziHalfPi : FastMatrix 2 2 := mzi (FastReal.mul FastReal.pi (FastReal.ofDyadic ⟨1, -1⟩))
#eval FastReal.toDecimal (FastComplex.abs (mziHalfPi 0 0)) 8   -- ≈ 1/√2
#eval FastReal.toDecimal (FastComplex.abs (mziHalfPi 0 1)) 8   -- ≈ 1/√2

-- MZI at φ = 0: BS·BS, photon swaps modes deterministically
def mziZero : FastMatrix 2 2 := mzi 0
#eval FastReal.toDecimal (FastComplex.abs (mziZero 0 0)) 8     -- ≈ 0
#eval FastReal.toDecimal (FastComplex.abs (mziZero 0 1)) 8     -- ≈ 1

-- Single photon in mode 1 through a beam splitter: amplitudes (1/√2, i/√2),
-- probabilities sum to 1
def out : Fin 2 → FastComplex := mulVec beamSplitter ![1, 0]
#eval FastReal.toDecimal (FastComplex.normSq (out 0) + FastComplex.normSq (out 1)) 10

-- Certified failure of a NON-unitary matrix: 2·BS is not unitary
#eval unitaryUpTo (FastComplex.ofDyadic ⟨2, 0⟩ • beamSplitter) 20  -- false (not certified)

end Computable.Fast.FastComplexMatrixExamples
