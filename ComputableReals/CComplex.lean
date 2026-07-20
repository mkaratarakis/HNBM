import ComputableReals.CRealPre2

/-!
# CComplex: verified computable complex numbers

A computable complex number is a pair of computable reals (`Computable.CReal`,
the quotient of regular Cauchy sequences of rationals from `CRealPre2`).

This file gives the **computable, verified ring structure**: all operations
below are quotient-level `CReal` operations (hence executable in principle),
and `CComplex` is proved to be a `CommRing` componentwise from the verified
`CommRing CReal`.

The classical field structure and the ring hom to Mathlib's `ℂ` live in
`CComplexBridge.lean`, mirroring the `CReal` split between `CRealPre2`
(computable, verified) and `CRealCCLOF` (classical, theorem-transfer).
-/

namespace Computable

/-- A computable complex number: a pair of computable reals. -/
@[ext]
structure CComplex : Type where
  re : CReal
  im : CReal

namespace CComplex

instance : Zero CComplex := ⟨⟨0, 0⟩⟩
instance : One CComplex := ⟨⟨1, 0⟩⟩
instance : Add CComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg CComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub CComplex := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul CComplex :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem zero_re : (0 : CComplex).re = 0 := rfl
@[simp] theorem zero_im : (0 : CComplex).im = 0 := rfl
@[simp] theorem one_re : (1 : CComplex).re = 1 := rfl
@[simp] theorem one_im : (1 : CComplex).im = 0 := rfl
@[simp] theorem add_re (z w : CComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : CComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : CComplex) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : CComplex) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : CComplex) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : CComplex) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : CComplex) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : CComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- The imaginary unit. -/
def I : CComplex := ⟨0, 1⟩

@[simp] theorem I_re : I.re = 0 := rfl
@[simp] theorem I_im : I.im = 1 := rfl

/-- The (computable) embedding of `CReal` into `CComplex`. -/
def ofReal (x : CReal) : CComplex := ⟨x, 0⟩

instance : Coe CReal CComplex := ⟨ofReal⟩

@[simp] theorem ofReal_re (x : CReal) : (ofReal x).re = x := rfl
@[simp] theorem ofReal_im (x : CReal) : (ofReal x).im = 0 := rfl

/-- Complex conjugation (computable). -/
def conj (z : CComplex) : CComplex := ⟨z.re, -z.im⟩

@[simp] theorem conj_re (z : CComplex) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : CComplex) : (conj z).im = -z.im := rfl

/-- The squared absolute value `re² + im²`, as a computable real. -/
def normSq (z : CComplex) : CReal := z.re * z.re + z.im * z.im

instance : CommRing CComplex where
  zero := 0
  one := 1
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  mul := (· * ·)
  add_assoc := by intros; ext <;> simp [add_assoc]
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp [add_comm]
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring

instance : Nontrivial CComplex :=
  ⟨⟨0, 1, fun h => zero_ne_one (congrArg re h)⟩⟩

theorem I_mul_I : I * I = -1 := by
  ext <;> simp

theorem mul_conj (z : CComplex) : z * conj z = ofReal (normSq z) := by
  ext <;> simp [normSq, mul_comm]

theorem ofReal_injective : Function.Injective ofReal := by
  intro x y h
  simpa using congrArg re h

/-! ### `re`/`im` as additive homs, sums -/

/-- The real part as an additive monoid hom. -/
def reAddHom : CComplex →+ CReal where
  toFun := re
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- The imaginary part as an additive monoid hom. -/
def imAddHom : CComplex →+ CReal where
  toFun := im
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] theorem reAddHom_apply (z : CComplex) : reAddHom z = z.re := rfl
@[simp] theorem imAddHom_apply (z : CComplex) : imAddHom z = z.im := rfl

theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → CComplex) :
    (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re :=
  map_sum reAddHom f s

theorem im_sum {ι : Type*} (s : Finset ι) (f : ι → CComplex) :
    (∑ x ∈ s, f x).im = ∑ x ∈ s, (f x).im :=
  map_sum imAddHom f s

/-! ### `normSq` lemmas -/

@[simp] theorem normSq_zero : normSq (0 : CComplex) = 0 := by
  show (0 : CReal) * 0 + 0 * 0 = 0; simp

@[simp] theorem normSq_one : normSq (1 : CComplex) = 1 := by
  show (1 : CReal) * 1 + 0 * 0 = 1; simp

@[simp] theorem normSq_I : normSq I = 1 := by
  show (0 : CReal) * 0 + 1 * 1 = 1; simp

@[simp] theorem normSq_conj (z : CComplex) : normSq (conj z) = normSq z := by
  simp only [normSq, conj_re, conj_im]; ring

@[simp] theorem normSq_ofReal (x : CReal) : normSq (ofReal x) = x * x := by
  simp only [normSq, ofReal_re, ofReal_im]; ring

/-- `normSq` is multiplicative — for photonics: probabilities compose under
sequential (matrix) evolution. -/
theorem normSq_mul (z w : CComplex) : normSq (z * w) = normSq z * normSq w := by
  simp only [normSq, mul_re, mul_im]; ring

/-- `ofReal` as a ring homomorphism. -/
def ofRealRingHom : CReal →+* CComplex where
  toFun := ofReal
  map_one' := rfl
  map_mul' := by intros; ext <;> simp
  map_zero' := rfl
  map_add' := by intros; ext <;> simp

@[simp] theorem ofRealRingHom_apply (x : CReal) : ofRealRingHom x = ofReal x := rfl

/-- `CComplex` is a (computable) `CReal`-algebra via `ofReal`. -/
instance : Algebra CReal CComplex := ofRealRingHom.toAlgebra

@[simp] theorem algebraMap_eq (x : CReal) :
    algebraMap CReal CComplex x = ofReal x := rfl

/-! ### `re`/`im` of ring casts

`CComplex` inherits `NatCast`/`IntCast` from its `CommRing`; both factor
through `ofReal`, so their real/imaginary parts are the corresponding `CReal`
cast and `0`. (This relies on `CReal` having a single, canonical `NatCast`.) -/

@[simp] theorem ofReal_natCast (n : ℕ) : ofReal (n : CReal) = (n : CComplex) := by
  rw [← ofRealRingHom_apply]; exact map_natCast ofRealRingHom n

@[simp] theorem ofReal_intCast (k : ℤ) : ofReal (k : CReal) = (k : CComplex) := by
  rw [← ofRealRingHom_apply]; exact map_intCast ofRealRingHom k

@[simp] theorem natCast_re (n : ℕ) : (n : CComplex).re = (n : CReal) := by
  rw [← ofReal_natCast]; rfl

@[simp] theorem natCast_im (n : ℕ) : (n : CComplex).im = 0 := by
  rw [← ofReal_natCast]; rfl

@[simp] theorem intCast_re (k : ℤ) : (k : CComplex).re = (k : CReal) := by
  rw [← ofReal_intCast]; rfl

@[simp] theorem intCast_im (k : ℤ) : (k : CComplex).im = 0 := by
  rw [← ofReal_intCast]; rfl

@[simp] theorem smul_re (x : CReal) (z : CComplex) : (x • z).re = x * z.re := by
  rw [Algebra.smul_def]; simp

@[simp] theorem smul_im (x : CReal) (z : CComplex) : (x • z).im = x * z.im := by
  rw [Algebra.smul_def]; simp

@[simp] theorem conj_smul (x : CReal) (z : CComplex) : conj (x • z) = x • conj z := by
  ext <;> simp [mul_neg]

/-- Conjugation as a ring homomorphism. -/
def conjRingHom : CComplex →+* CComplex where
  toFun := conj
  map_one' := by ext <;> simp
  map_mul' := by
    intros; ext
    · simp
    · simp; ring
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp [add_comm]

@[simp] theorem conj_conj (z : CComplex) : conj (conj z) = z := by
  ext <;> simp

@[simp] theorem conj_one : conj (1 : CComplex) = 1 := by
  ext <;> simp

@[simp] theorem conj_I : conj I = -I := by
  ext <;> simp

/-! ### Star structure

Conjugation as a (computable) `StarRing` structure. This is what makes
Mathlib's `Matrix.conjTranspose` (`Aᴴ`) and `Matrix.unitaryGroup` available
over `CComplex`.
-/

instance : StarRing CComplex where
  star := conj
  star_involutive := conj_conj
  star_mul := by intro z w; ext <;> simp [mul_comm, add_comm]
  star_add := by intro z w; ext <;> simp [add_comm]

@[simp] theorem star_def (z : CComplex) : star z = conj z := rfl

end CComplex

end Computable
