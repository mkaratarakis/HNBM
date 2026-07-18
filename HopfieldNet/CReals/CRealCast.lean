import HopfieldNet.CReals.CRealCCLOF

/-!
# Cast and transfer lemmas for `CReal`

The workhorse of the computable-real API: `toReal : CReal → ℝ` is injective
and order-reflecting, so **any `CReal` equation or inequality can be settled
by pushing `toReal` through it and finishing in `ℝ`** (`norm_num`, `ring`,
`push_cast`, …). This file makes that push automatic:

* `toReal_add/mul/neg/sub/pow` and the cast lemmas
  `toReal_ratCast/natCast/intCast/ofNat` are all `@[simp]`, so
  `apply toReal_injective; simp` reduces a `CReal` identity to an `ℝ` one;
* `ratCastRingHom : ℚ →+* CReal` bundles the rational embedding, with
  `ratCast_add/mul/neg/sub/inv` and the order iffs `ratCast_le/lt`.

`toReal_ratCast` is definitional: the rational embedding is literally the
constant Cauchy sequence on both sides.
-/

namespace Computable
namespace CReal

attribute [simp] toReal_add toReal_mul toReal_neg

/-! ### `toReal` and casts -/

@[simp] theorem toReal_ratCast (q : ℚ) : toReal ((q : ℚ) : CReal) = (q : ℝ) := rfl

@[simp] theorem toReal_natCast (n : ℕ) : toReal ((n : ℕ) : CReal) = (n : ℝ) :=
  map_natCast toRealRingHom n

@[simp] theorem toReal_intCast (k : ℤ) : toReal ((k : ℤ) : CReal) = (k : ℝ) :=
  map_intCast toRealRingHom k

@[simp] theorem toReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    toReal (OfNat.ofNat n : CReal) = OfNat.ofNat n :=
  map_ofNat toRealRingHom n

/-! ### `toReal` and the remaining ring operations

`CReal` subtraction is definitionally `x + -y` on every instance path, so the
`show` below is `rfl`-robust against the non-canonical `Sub` instances.
-/

@[simp] theorem toReal_sub (x y : CReal) : toReal (x - y) = toReal x - toReal y := by
  show toReal (x + -y) = _
  rw [toReal_add, toReal_neg, sub_eq_add_neg]

@[simp] theorem toReal_pow (x : CReal) (n : ℕ) : toReal (x ^ n) = toReal x ^ n :=
  map_pow toRealRingHom x n

attribute [simp] toReal_inv

@[simp] theorem toReal_div (x y : CReal) : toReal (x / y) = toReal x / toReal y := by
  rw [div_eq_mul_inv, toReal_mul, toReal_inv, div_eq_mul_inv]

@[simp] theorem toReal_zpow (x : CReal) (n : ℤ) : toReal (x ^ n) = toReal x ^ n := by
  cases n with
  | ofNat m => simp [toReal_pow x m]
  | negSucc m =>
    rw [zpow_negSucc, zpow_negSucc, toReal_inv, toReal_pow]

/-! ### The rational embedding as a ring hom -/

@[simp] theorem ratCast_zero : ((0 : ℚ) : CReal) = 0 := by
  apply toReal_injective; simp

@[simp] theorem ratCast_one : ((1 : ℚ) : CReal) = 1 := by
  apply toReal_injective; simp

@[simp] theorem ratCast_add (p q : ℚ) : ((p + q : ℚ) : CReal) = (p : CReal) + q := by
  apply toReal_injective; simp

@[simp] theorem ratCast_mul (p q : ℚ) : ((p * q : ℚ) : CReal) = (p : CReal) * q := by
  apply toReal_injective; simp

@[simp] theorem ratCast_neg (q : ℚ) : ((-q : ℚ) : CReal) = -(q : CReal) := by
  apply toReal_injective; simp

@[simp] theorem ratCast_sub (p q : ℚ) : ((p - q : ℚ) : CReal) = (p : CReal) - q := by
  apply toReal_injective; simp

@[simp] theorem ratCast_inv (q : ℚ) : ((q⁻¹ : ℚ) : CReal) = ((q : CReal))⁻¹ := by
  apply toReal_injective
  rw [toReal_inv]
  simp

/-- The rational embedding `ℚ →+* CReal` (computable: constant sequences). -/
def ratCastRingHom : ℚ →+* CReal where
  toFun q := (q : CReal)
  map_one' := ratCast_one
  map_mul' := ratCast_mul
  map_zero' := ratCast_zero
  map_add' := ratCast_add

@[simp] theorem ratCastRingHom_apply (q : ℚ) : ratCastRingHom q = (q : CReal) := rfl

theorem ratCast_injective : Function.Injective (fun q : ℚ => (q : CReal)) := by
  intro p q h
  have := congrArg toReal h
  simpa using this

/-! ### Order transfer -/

@[simp] theorem ratCast_le {p q : ℚ} : ((p : CReal) ≤ (q : CReal)) ↔ p ≤ q := by
  rw [← toReal_le_iff]
  simp

@[simp] theorem ratCast_lt {p q : ℚ} : ((p : CReal) < (q : CReal)) ↔ p < q := by
  rw [← toReal_lt_iff]
  simp

@[simp] theorem ratCast_nonneg {q : ℚ} : (0 : CReal) ≤ (q : CReal) ↔ 0 ≤ q := by
  rw [← ratCast_zero, ratCast_le]

/-! ### The `CReal` decision procedure, in one lemma

Any equation between `CReal` expressions built from casts and ring
operations reduces to an `ℝ` (hence effectively `ℚ`) statement. Examples: -/

example : ((1 / 2 : ℚ) : CReal) + ((1 / 2 : ℚ) : CReal) = 1 := by
  apply toReal_injective
  simp only [toReal_add, toReal_ratCast, toReal_one]; norm_num

example (x y : CReal) : (x + y) * (x - y) = x * x - y * y := by
  apply toReal_injective; simp; ring

end CReal
end Computable
