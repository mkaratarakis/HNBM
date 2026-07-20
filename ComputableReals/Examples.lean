import ComputableReals.CRealLog
import ComputableReals.CRealSigmoid
import ComputableReals.CRealPre2.InvTranscendental
import ComputableReals.CRealCCLOF

open Computable CReal

/-!
# Computable Real Number Examples

This file demonstrates the use of the `CReal` implementation by computing
approximations of various constants and function values.

Since `CReal` is a quotient type, we cannot directly `#eval` a `CReal`.
Instead, we define a helper function `show` that computes a rational
approximation to a given precision, and a `toString` function to display it.
-/

/--
Get a rational approximation of a `CReal` to precision `n`.
This means the result is within `1/2^n` of the true value.
This function uses `Quotient.out`, which is non-constructive, but it is fine
for demonstration purposes with `#eval`.
-/
noncomputable def show' (x : CReal) (n : ℕ) : ℚ :=
  (Quotient.out x).approx (n + 1)

/--
A simple function to convert a rational number to a decimal string representation
with a given precision.
-/
def ratToString (q : ℚ) (prec : ℕ) : String :=
  let sign := if q < 0 then "-" else ""
  let q' := |q|
  let intPart := q'.floor.toNat
  let fracPart := q' - intPart
  let rec go (k : ℕ) (r : ℚ) (s : String) : String :=
    if k = 0 then s
    else
      let r' := 10 * r
      let digit := Nat.floor r'
      go (k-1) (r' - digit) (s ++ toString digit)
  sign ++ toString intPart ++ "." ++ go prec fracPart ""

noncomputable def CReal.toString (x : CReal) (prec : ℕ) : String :=
  -- To get `prec` decimal digits, we need an error < 10⁻ᵖʳᵉᶜ / 2.
  -- We use an approximation with error < 1/2ⁿ.
  -- We need 2ⁿ > 2 * 10ᵖʳᵉᶜ, so n > log₂(2 * 10ᵖʳᵉᶜ) = 1 + prec * log₂(10).
  -- log₂(10) ≈ 3.32, so n > 1 + 3.32 * prec. `n = 4 * prec` is a safe choice.
  let n := 4 * prec
  let q := show' x n
  ratToString q prec

/-! ## Basic Arithmetic -/

-- These live in the (noncomputable) quotient `CReal`; we only `#check` /
-- prove with them below. Executable numerics belong to `Computable.Fast`.
noncomputable def one : CReal := 1
noncomputable def two : CReal := 2
noncomputable def three : CReal := 3
noncomputable def half : CReal := ((1 / 2 : ℚ) : CReal)

/-
Note: `CReal` is a *quotient*, and displaying a value requires extracting a
representative via `Quotient.out`, which is noncomputable. So `CReal.toString`
is noncomputable and these display lines use `#check` (they confirm the
expressions typecheck, not that they run). For actual `#eval` numerics use the
executable `Computable.Fast` layer (`FastReal`), which is designed for it.
-/
#check CReal.toString (one + two) 10 -- Expected: 3.0000000000
#check CReal.toString three 10
#check CReal.toString (two * three) 10 -- Expected: 6.0000000000
#check CReal.toString half 10 -- Expected: 0.5000000000

/-! ## Transcendental Functions -/

-- `log(1+x)` is defined for `|x| ≤ 1/2`
def log_one_and_a_half : CReal := log1pRatSmall (1/2) (by norm_num)

-- log(1.5) ≈ 0.405465
#check CReal.toString log_one_and_a_half 5 -- Expected: 0.40546

-- `sigmoid(x)` is defined for `|x| ≤ 1/2`
-- sigmoid(0) = 1 / (1 + exp(0)) = 1/2
def sigmoid_zero : CReal := sigmoidRatSmall 0 (by norm_num)
#check CReal.toString sigmoid_zero 10 -- Expected: 0.5000000000

-- sigmoid(0.5) = 1 / (1 + exp(-0.5)) ≈ 1 / (1 + 0.6065) ≈ 0.62245
def sigmoid_half : CReal := sigmoidRatSmall (1/2) (by norm_num)
#check CReal.toString sigmoid_half 5 -- Expected: 0.62245

/-! ## Sanity checks for the small-exp pre-real on rationals

These operate on the *pre-quotient* `CReal.Pre` directly, where `.approx n`
is an honest rational — so unlike the quotient-level display above, these
`#eval` and run. -/

#eval (CReal.Pre.small_exp (1/4 : ℚ) (by norm_num)).approx 5
#eval (CReal.Pre.small_exp (-1/3 : ℚ) (by norm_num)).approx 5

/-! ## Comparisons -/

-- We can't `#eval` the order (it isn't decidable-by-evaluation on the
-- quotient), but we can prove order facts. This transfers to `ℝ`.
theorem one_lt_two' : (1 : CReal) < 2 := by norm_num

#check one_lt_two'
