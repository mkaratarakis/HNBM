import ComputableReals.FastComplex
import Mathlib.Data.Fin.VecNotation

/-!
# FastMatrix: executable complex matrix arithmetic

Matrices of computable complex numbers (`FastComplex`), purely executable
(`#eval`-friendly):

- ring-style operations: `add`, `sub`, `smul`, `mul` (matrix product),
  `mulVec`, `trace`;
- `conjTranspose` (`Aᴴ`) and `transpose`;
- `kron`, the Kronecker/tensor product;
- `unitaryUpTo`, a **rigorous numerical certificate** of unitarity: interval
  arithmetic certifies every entry of `U * Uᴴ - 1` has absolute value below
  `2^{-tol}`. `true` is a sound bound; `false` only means "not certified at
  this precision".

See `FastComplexMatrixExamples.lean` for `#eval` smoke tests.
-/

namespace Computable.Fast

/-- An `m × n` matrix of computable complex numbers. -/
def FastMatrix (m n : Nat) : Type := Fin m → Fin n → FastComplex

namespace FastMatrix

variable {m n p q : Nat}

def zero : FastMatrix m n := fun _ _ => 0

/-- The identity matrix. -/
def one : FastMatrix n n := fun i j => if i = j then 1 else 0

def add (A B : FastMatrix m n) : FastMatrix m n := fun i j => A i j + B i j

def neg (A : FastMatrix m n) : FastMatrix m n := fun i j => FastComplex.neg (A i j)

def sub (A B : FastMatrix m n) : FastMatrix m n := fun i j => A i j - B i j

/-- Scale by a complex number. -/
def smul (c : FastComplex) (A : FastMatrix m n) : FastMatrix m n := fun i j => c * A i j

instance : Add (FastMatrix m n) := ⟨add⟩
instance : Sub (FastMatrix m n) := ⟨sub⟩
instance : Neg (FastMatrix m n) := ⟨neg⟩
instance : SMul FastComplex (FastMatrix m n) := ⟨smul⟩

/-- Sum of a finite family of computable complex numbers. -/
def sumFin (f : Fin n → FastComplex) : FastComplex :=
  (List.finRange n).foldl (fun acc k => acc + f k) 0

/-- Matrix product. -/
def mul (A : FastMatrix m n) (B : FastMatrix n p) : FastMatrix m p :=
  fun i j => sumFin (fun k => A i k * B k j)

instance : HMul (FastMatrix m n) (FastMatrix n p) (FastMatrix m p) := ⟨mul⟩

/-- Apply a matrix to a (mode-amplitude) vector. -/
def mulVec (A : FastMatrix m n) (v : Fin n → FastComplex) : Fin m → FastComplex :=
  fun i => sumFin (fun k => A i k * v k)

def transpose (A : FastMatrix m n) : FastMatrix n m := fun i j => A j i

/-- Conjugate transpose `Aᴴ`. -/
def conjTranspose (A : FastMatrix m n) : FastMatrix n m := fun i j => (A j i).conj

def trace (A : FastMatrix n n) : FastComplex := sumFin (fun i => A i i)

/-- Kronecker (tensor) product — composition of optical modes. -/
def kron (A : FastMatrix m n) (B : FastMatrix p q) : FastMatrix (m * p) (n * q) :=
  fun i j => A i.divNat j.divNat * B i.modNat j.modNat

/-!
### Certified numerical predicates

Equality of computable reals is only semi-decidable, so exact unitarity
`U * Uᴴ = 1` cannot be decided by evaluation (entries like `1/√2` never
become exact dyadic balls). What *is* decidable — and rigorous, thanks to
ball arithmetic — is an enclosure bound: every entry of `U * Uᴴ - 1` is
certified to have absolute value `< 2^{-tol}`.
-/

/-- Certified `|x| < 2^{-tol}`: sound when `true`, inconclusive when `false`. -/
def certSmall (x : FastReal) (tol : Nat) : Bool :=
  ((x (tol + 4)).absUpper < (⟨1, -(tol : Int)⟩ : Dyadic) : Bool)

/-- Certified `|z| < 2^{-tol}` componentwise. -/
def certSmallC (z : FastComplex) (tol : Nat) : Bool :=
  certSmall z.re tol && certSmall z.im tol

/-- Certified entrywise `|A i j - B i j| < 2^{-tol}`. -/
def approxEq (A B : FastMatrix m n) (tol : Nat) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j => certSmallC (A i j - B i j) tol

/-- Rigorous unitarity certificate: every entry of `U * Uᴴ - 1` is certified
`< 2^{-tol}` in absolute value (componentwise). -/
def unitaryUpTo (U : FastMatrix n n) (tol : Nat) : Bool :=
  approxEq (U * conjTranspose U) one tol

/-- Decimal rendering, one row per line (for `#eval IO.println`). -/
def toDecimal (A : FastMatrix m n) (digits : Nat := 6) : String :=
  String.intercalate "\n" <| (List.finRange m).map fun i =>
    String.intercalate "  |  " <| (List.finRange n).map fun j =>
      (A i j).toDecimal digits

end FastMatrix

end Computable.Fast
