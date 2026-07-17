import HopfieldNet.CReals.FastComplexMatrix

open Computable.Fast Computable.Fast.FastMatrix

namespace Computable.Fast.FastComplexMatrixExamples
set_option autoImplicit false
/-!
Executable smoke tests for `FastMatrix`. The test matrices are standard 2×2
unitaries (a 50:50 splitter, a phase rotation, and their composition), used
here purely as generic exercises of `mul`, `kron`, and `unitaryUpTo`.
-/

/-- Test unitary `(1/√2) · [[1, i], [i, 1]]` (irrational entries). -/
def U : FastMatrix 2 2 :=
  let s : FastReal := FastReal.sqrt (FastReal.ofDyadic ⟨1, -1⟩) -- 1/√2 = √(1/2)
  ![![⟨s, 0⟩, ⟨0, s⟩],
    ![⟨0, s⟩, ⟨s, 0⟩]]

/-- Test unitary `[[1, 0], [0, e^{iφ}]]` (transcendental entries). -/
def P (φ : FastReal) : FastMatrix 2 2 :=
  ![![1, 0],
    ![0, FastComplex.phase φ]]

/-- A composed product of the two. -/
def UPU (φ : FastReal) : FastMatrix 2 2 := U * P φ * U

def piHalf : FastReal := FastReal.mul FastReal.pi (FastReal.ofDyadic ⟨1, -1⟩)

-- The test matrix itself: (1/√2)·[[1, i], [i, 1]]
#eval IO.println (toDecimal U 8)

-- U · U = [[0, i], [i, 0]] (a swap with phase i)
#eval IO.println (toDecimal (U * U) 8)

-- Rigorous unitarity certificates: every entry of A·Aᴴ - 1 certified < 2⁻²⁰
#eval unitaryUpTo U 20
#eval unitaryUpTo (P FastReal.pi) 20
#eval unitaryUpTo (UPU piHalf) 20

-- Kronecker product of unitaries stays unitary (4×4)
#eval unitaryUpTo (kron U U) 20

-- Entry magnitudes of the composition at φ = π/2: both ≈ 1/√2
#eval FastReal.toDecimal (FastComplex.abs (UPU piHalf 0 0)) 8
#eval FastReal.toDecimal (FastComplex.abs (UPU piHalf 0 1)) 8

-- At φ = 0 the composition is a deterministic swap: |(0,0)| ≈ 0, |(0,1)| ≈ 1
#eval FastReal.toDecimal (FastComplex.abs (UPU 0 0 0)) 8
#eval FastReal.toDecimal (FastComplex.abs (UPU 0 0 1)) 8

-- mulVec preserves the norm: ‖U·e₁‖² = 1
def out : Fin 2 → FastComplex := mulVec U ![1, 0]
#eval FastReal.toDecimal (FastComplex.normSq (out 0) + FastComplex.normSq (out 1)) 10

-- Certified failure: 2·U is not unitary
#eval unitaryUpTo (FastComplex.ofDyadic ⟨2, 0⟩ • U) 20  -- false (not certified)

end Computable.Fast.FastComplexMatrixExamples
