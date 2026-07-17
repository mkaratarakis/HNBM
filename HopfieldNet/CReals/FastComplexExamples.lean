import HopfieldNet.CReals.FastComplex

open Computable.Fast

namespace Computable.Fast.FastComplexExamples
set_option autoImplicit false
/-!
Executable smoke tests for `FastComplex` (`#eval`-first, like `CRealsFastExamples`).
-/

-- I * I = -1 (exact: dyadic components stay exact, so `eq?` decides equality)
#eval FastComplex.I * FastComplex.I
#eval FastComplex.eq? (FastComplex.I * FastComplex.I) (FastComplex.neg 1)

-- (1 + 2i) * (3 - i) = 5 + 5i
def z₁ : FastComplex := ⟨1, 2⟩
def z₂ : FastComplex := ⟨3, FastReal.neg 1⟩
#eval z₁ * z₂
#eval FastComplex.eq? (z₁ * z₂) ⟨5, 5⟩

-- |3 + 4i| = 5
#eval FastReal.toDecimal (FastComplex.abs ⟨3, 4⟩) 10

-- Euler: exp (iπ) ≈ -1 + 0i
#eval FastComplex.toDecimal (FastComplex.exp ⟨0, FastReal.pi⟩) 12

-- exp (iπ/2) ≈ i
def iPiHalf : FastComplex := ⟨0, FastReal.mul FastReal.pi (FastReal.ofDyadic ⟨1, -1⟩)⟩
#eval FastComplex.toDecimal (FastComplex.exp iPiHalf) 12

-- Division: (1 + 2i) / (3 - i) = 1/10 + 7/10 i
#eval (FastComplex.div? z₁ z₂) 20

-- Reciprocal: 1 / i = -i
#eval (FastComplex.inv? FastComplex.I) 20

-- Principal square roots: √(2i) = 1 + i, √(-1) = i (exact-zero im ⇒ principal branch)
#eval FastComplex.toDecimal (FastComplex.sqrt ⟨0, 2⟩) 10
#eval FastComplex.toDecimal (FastComplex.sqrt (FastComplex.neg 1)) 10

-- sqrt ∘ square: √((1+2i)²) ≈ 1 + 2i
#eval FastComplex.toDecimal (FastComplex.sqrt (z₁ * z₁)) 10

-- Argument: arg (1 + i) = π/4, arg i = π/2, arg (-1 + i) = 3π/4
#eval (FastComplex.arg? ⟨1, 1⟩) 20 |>.map (FastReal.ballToDecimalMidRad · 10)
#eval (FastComplex.arg? FastComplex.I) 20 |>.map (FastReal.ballToDecimalMidRad · 10)
#eval (FastComplex.arg? ⟨FastReal.neg 1, 1⟩) 20 |>.map (FastReal.ballToDecimalMidRad · 10)

-- On the branch cut the argument is (rightly) undecided: arg (-1 + 0i) = none
#eval (FastComplex.arg? (FastComplex.neg 1)) 20

-- log (exp (1 + i)) ≈ (1, 1)
#eval (FastComplex.log? (FastComplex.exp ⟨1, 1⟩)) 20

-- sin² + cos² = 1 at z = 1 + i (componentwise ≈ (1, 0))
def w : FastComplex := ⟨1, 1⟩
#eval FastComplex.toDecimal (FastComplex.sin w * FastComplex.sin w
  + FastComplex.cos w * FastComplex.cos w) 10

end Computable.Fast.FastComplexExamples
