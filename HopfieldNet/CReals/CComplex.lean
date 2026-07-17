import HopfieldNet.CReals.CRealPre2

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

theorem I_mul_I : I * I = -1 := by
  ext <;> simp

theorem mul_conj (z : CComplex) : z * conj z = ofReal (normSq z) := by
  ext <;> simp [normSq, mul_comm]

/-- `ofReal` as a ring homomorphism. -/
def ofRealRingHom : CReal →+* CComplex where
  toFun := ofReal
  map_one' := rfl
  map_mul' := by intros; ext <;> simp
  map_zero' := rfl
  map_add' := by intros; ext <;> simp

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

end CComplex

end Computable
