import HopfieldNet.CReals.CComplexMatrix
import HopfieldNet.CReals.CRealSqrtQ

/-!
# Verified photonics: the beam splitter over computable numbers

The 50:50 beam splitter with **verified amplitudes**: its entries are
`(1/√2)·1` and `(1/√2)·i` where `1/√2 = CReal.sqrtQ (1/2)` is a genuine
computable real (an executable rational Cauchy sequence), and unitarity is
*proved*, not numerically certified:

* `beamSplitterC_unitary : beamSplitterC ∈ Matrix.unitaryGroup (Fin 2) CComplex`
* probability conservation drops out via `sum_normSq_col_of_unitary`.

Compare `FastComplexMatrix.lean`, where the same device is evaluated with
interval arithmetic (`unitaryUpTo`): there the certificate is numerical and
approximate; here it is exact and symbolic. Both describe the same physics.
-/

namespace Computable
namespace Photonics

open CComplex

/-- `1/√2`, the beam-splitter amplitude, as a verified computable real. -/
def invSqrtTwo : CReal := CReal.sqrtQ (1 / 2)

theorem invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = (((1 : ℚ) / 2 : ℚ) : CReal) :=
  CReal.sqrtQ_mul_self (by norm_num)

theorem half_add_half : (((1 : ℚ) / 2 : ℚ) : CReal) + (((1 : ℚ) / 2 : ℚ) : CReal) = 1 := by
  apply CReal.toReal_injective
  rw [CReal.toReal_add, CReal.toReal_ratCast, CReal.toReal_one]
  norm_num

/-- Two copies of the squared amplitude sum to `1`. -/
theorem invSqrtTwo_sq_add :
    invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo = 1 := by
  rw [invSqrtTwo_sq, half_add_half]

/-- The 50:50 beam splitter `(1/√2)·[[1, i], [i, 1]]` over `CComplex`. -/
def beamSplitterC : CMatrix 2 :=
  Matrix.of fun i j =>
    if i = j then invSqrtTwo • (1 : CComplex) else invSqrtTwo • I

/-! ### The entry-level algebra (sub-free, via the smul/conj API) -/

private theorem bs_diag :
    (invSqrtTwo • (1 : CComplex)) * conj (invSqrtTwo • 1)
      + (invSqrtTwo • I) * conj (invSqrtTwo • I) = 1 := by
  rw [conj_smul, conj_smul, conj_one, conj_I, smul_neg, mul_neg,
    smul_mul_smul_comm, smul_mul_smul_comm, one_mul, I_mul_I, smul_neg, neg_neg,
    ← add_smul, invSqrtTwo_sq_add, one_smul]

private theorem bs_off :
    (invSqrtTwo • (1 : CComplex)) * conj (invSqrtTwo • I)
      + (invSqrtTwo • I) * conj (invSqrtTwo • 1) = 0 := by
  rw [conj_smul, conj_smul, conj_one, conj_I, smul_neg, mul_neg,
    smul_mul_smul_comm, smul_mul_smul_comm, one_mul, mul_one,
    neg_add_cancel]

/-- **The beam splitter is unitary** — proved, not numerically certified. -/
theorem beamSplitterC_unitary :
    beamSplitterC ∈ Matrix.unitaryGroup (Fin 2) CComplex := by
  rw [Matrix.mem_unitaryGroup_iff]
  refine Matrix.ext fun i j => ?_
  have hmul : (beamSplitterC * star beamSplitterC) i j
      = beamSplitterC i 0 * conj (beamSplitterC j 0)
        + beamSplitterC i 1 * conj (beamSplitterC j 1) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.star_apply]
  rw [hmul]
  fin_cases i <;> fin_cases j
  · exact bs_diag
  · exact bs_off
  · rw [add_comm]; exact bs_off
  · rw [add_comm]; exact bs_diag

/-- Probability conservation at the beam splitter: the output probabilities
from either input mode sum to exactly `1`, as computable reals. -/
theorem beamSplitter_prob_conservation (j : Fin 2) :
    ∑ i, normSq (beamSplitterC i j) = 1 :=
  sum_normSq_col_of_unitary beamSplitterC_unitary j

end Photonics
end Computable
