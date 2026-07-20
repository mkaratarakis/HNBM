/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.Computable.Refinement

/-!
# Enclosure preservation for `FastReal` arithmetic

`Refinement.lean` proves fueled comparisons sound *given* enclosures of the
inputs. This file supplies those enclosures for the arithmetic actually used
by the executable layer: if `x` encloses `r` and `y` encloses `s`, then

* `-x` encloses `-r`                     (`FastReal.neg_encloses`),
* `x + y` encloses `r + s`               (`FastReal.add_encloses`),
* `x - y` encloses `r - s`               (`FastReal.sub_encloses`),
* `x * y` encloses `r * s`               (`FastReal.mul_encloses`),

together with grounding for numeric literals (`encloses_ofNat`). The chain
bottoms out in certified error bounds for the dyadic rounding primitives:
`round` (to nearest, ties to even) moves a value by at most `2^(p-1)` — the
exact budget `Ball.add`/`Ball.mul` reserve in their radius — and `roundUp`
never decreases a value. (`round`/`roundUp` are stated via `rfl`-equal
copies `roundSpec`/`roundUpSpec`, because their bodies use a private
helper.)

With these, enclosure proofs for composite executable quantities (energies,
fields) reduce to structural induction, and the certificates of
`FastEnergy`/`Refinement` apply to inputs built from literals and ring
operations without further hypotheses. `exp`, `sqrt` and `inv?` remain
future work.
-/

namespace Computable.Fast

private lemma two_q_pos : (0 : ℚ) < 2 := by norm_num

/-! ## Dyadic rounding: certified error bounds -/

namespace Dyadic

/-- `rfl`-equal copy of `Dyadic.roundUp` (whose body uses a private
helper), for stating specifications. -/
private def roundUpSpec (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := (1 : Int) <<< shift
    let q := d.man >>> shift
    let r := d.man % denom
    { man := if r == 0 then q else q + 1, exp := min_exp }

private lemma roundUp_eq_spec : Dyadic.roundUp = roundUpSpec := rfl

/-- `rfl`-equal copy of `Dyadic.round`. -/
private def roundSpec (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := (1 : Int) <<< shift
    let q := d.man >>> shift
    let r := d.man % denom
    let half : Int := denom >>> 1
    let q' :=
      if r < half then q
      else if r > half then q + 1
      else if q % 2 == 0 then q else q + 1
    { man := q', exp := min_exp }

private lemma round_eq_spec : Dyadic.round = roundSpec := rfl

/-- `toRat` of the mantissa-`abs` is the rational `abs`. -/
theorem toRat_abs (d : Dyadic) : (Dyadic.abs d).toRat = |d.toRat| := by
  show ((d.man.natAbs : ℤ) : ℚ) * 2 ^ d.exp = |(d.man : ℚ) * 2 ^ d.exp|
  rw [abs_mul, abs_of_pos (zpow_pos two_q_pos d.exp)]
  congr 1
  rw [← Int.cast_abs, ← Int.natCast_natAbs]

section RoundBounds

variable (d : Dyadic) (p : ℤ)

/-- Common scaffolding: in the non-trivial branch (`d.exp < p`), writing
`sh`, `den`, `q`, `r` as in the rounding bodies, a mantissa `q'` with
`|q' * den - d.man| ≤ B` yields `|⟨q',p⟩.toRat - d.toRat| ≤ B * 2^(p-sh)`
where `2^(p-sh) = 2^d.exp`. We inline this per lemma below. -/

private lemma toRat_mk_sub (hlt : d.exp < p) (q' : ℤ) :
    Dyadic.toRat ⟨q', p⟩ - d.toRat =
      ((q' * ((1 : ℤ) <<< (p - d.exp).toNat) - d.man : ℤ) : ℚ) * 2 ^ d.exp := by
  have hsh : (((p - d.exp).toNat : ℤ)) = p - d.exp := Int.toNat_of_nonneg (by omega)
  have hden : ((1 : ℤ) <<< (p - d.exp).toNat) = 2 ^ (p - d.exp).toNat := by
    simpa using Int.shiftLeft_eq 1 (p - d.exp).toNat
  have hpow : (2 : ℚ) ^ p = (2 : ℚ) ^ ((p - d.exp).toNat : ℤ) * 2 ^ d.exp := by
    rw [← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
    congr 1
    omega
  show (q' : ℚ) * 2 ^ p - (d.man : ℚ) * 2 ^ d.exp = _
  rw [hpow, hden]
  push_cast
  rw [zpow_natCast]
  ring

/-- **Round-to-nearest moves a dyadic by at most half an ulp**:
`|round d p - d| ≤ 2^(p-1)` in `toRat`. This is exactly the error budget
`Ball.add`/`Ball.mul` reserve when rounding changed the midpoint. -/
theorem abs_toRat_round_sub_le :
    |((Dyadic.round d p).toRat - d.toRat)| ≤ (2 : ℚ) ^ (p - 1) := by
  rw [round_eq_spec]
  by_cases h : d.exp ≥ p
  · simp only [roundSpec, if_pos h]
    simpa using (zpow_pos two_q_pos (p - 1)).le
  · have hlt : d.exp < p := lt_of_not_ge h
    have hsh_pos : 1 ≤ (p - d.exp).toNat := by omega
    obtain ⟨k, hk⟩ : ∃ k, (p - d.exp).toNat = k + 1 :=
      ⟨(p - d.exp).toNat - 1, by omega⟩
    set sh : ℕ := (p - d.exp).toNat with hsh_def
    set den : ℤ := (1 : ℤ) <<< sh with hden_def
    have hden : den = 2 ^ sh := by simpa [hden_def] using Int.shiftLeft_eq 1 sh
    have hden_pos : 0 < den := by rw [hden]; positivity
    set q : ℤ := d.man >>> sh with hq_def
    set r : ℤ := d.man % den with hr_def
    set half : ℤ := den >>> 1 with hhalf_def
    have hq : q = d.man / den := by
      rw [hq_def, hden, Int.shiftRight_eq_div_pow]; norm_cast
    have hhalf : half = 2 ^ k := by
      rw [hhalf_def, hden, hk, Int.shiftRight_eq_div_pow, pow_succ, pow_one]
      norm_num
    have hden2 : den = 2 * half := by rw [hden, hhalf, hk, pow_succ]; ring
    have hdecomp : d.man = den * q + r := by
      rw [hq, hr_def]; exact (Int.mul_ediv_add_emod d.man den).symm
    have hr0 : 0 ≤ r := hr_def ▸ Int.emod_nonneg d.man hden_pos.ne'
    have hrden : r < den := hr_def ▸ Int.emod_lt_of_pos d.man hden_pos
    -- commutativity links for `omega` (products are opaque atoms to it)
    have hcomm : q * den = den * q := mul_comm q den
    have hcomm1 : (q + 1) * den = den * q + den := by ring
    -- identify the produced mantissa and bound its distance
    have hgoal : ∀ q' : ℤ, |q' * den - d.man| ≤ half →
        |Dyadic.toRat ⟨q', p⟩ - d.toRat| ≤ (2 : ℚ) ^ (p - 1) := by
      intro q' hb
      rw [toRat_mk_sub d p hlt q', ← hsh_def, ← hden_def]
      rw [abs_mul, abs_of_pos (zpow_pos two_q_pos d.exp)]
      have hcast : |((q' * den - d.man : ℤ) : ℚ)| ≤ (half : ℚ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hb
      calc |((q' * den - d.man : ℤ) : ℚ)| * 2 ^ d.exp
          ≤ (half : ℚ) * 2 ^ d.exp := by
            exact mul_le_mul_of_nonneg_right hcast (zpow_pos two_q_pos _).le
        _ = (2 : ℚ) ^ (p - 1) := by
            rw [hhalf]
            push_cast
            rw [← zpow_natCast (2 : ℚ) k, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
            congr 1
            omega
    -- unfold the spec, fold the abbreviations back, case on the branch
    show |Dyadic.toRat (roundSpec d p) - d.toRat| ≤ (2 : ℚ) ^ (p - 1)
    simp only [roundSpec, if_neg h]
    rw [← hsh_def, ← hden_def, ← hq_def, ← hr_def, ← hhalf_def]
    split_ifs with h1 h2 h3
    · exact hgoal q (by rw [abs_le]; omega)
    · exact hgoal (q + 1) (by rw [abs_le]; omega)
    · exact hgoal q (by rw [abs_le]; omega)
    · exact hgoal (q + 1) (by rw [abs_le]; omega)

/-- **Rounding up never decreases a dyadic** (in `toRat`). -/
theorem le_toRat_roundUp : d.toRat ≤ (Dyadic.roundUp d p).toRat := by
  rw [roundUp_eq_spec]
  by_cases h : d.exp ≥ p
  · simp [roundUpSpec, if_pos h]
  · have hlt : d.exp < p := lt_of_not_ge h
    set sh : ℕ := (p - d.exp).toNat with hsh_def
    set den : ℤ := (1 : ℤ) <<< sh with hden_def
    have hden : den = 2 ^ sh := by simpa [hden_def] using Int.shiftLeft_eq 1 sh
    have hden_pos : 0 < den := by rw [hden]; positivity
    set q : ℤ := d.man >>> sh with hq_def
    set r : ℤ := d.man % den with hr_def
    have hq : q = d.man / den := by
      rw [hq_def, hden, Int.shiftRight_eq_div_pow]; norm_cast
    have hdecomp : d.man = den * q + r := by
      rw [hq, hr_def]; exact (Int.mul_ediv_add_emod d.man den).symm
    have hr0 : 0 ≤ r := hr_def ▸ Int.emod_nonneg d.man hden_pos.ne'
    have hrden : r < den := hr_def ▸ Int.emod_lt_of_pos d.man hden_pos
    have hcomm : q * den = den * q := mul_comm q den
    have hcomm1 : (q + 1) * den = den * q + den := by ring
    have hgoal : ∀ q' : ℤ, 0 ≤ q' * den - d.man →
        d.toRat ≤ Dyadic.toRat ⟨q', p⟩ := by
      intro q' hb
      have hEq := toRat_mk_sub d p hlt q'
      rw [← hsh_def, ← hden_def] at hEq
      have hnn : (0 : ℚ) ≤ Dyadic.toRat ⟨q', p⟩ - d.toRat := by
        rw [hEq]
        apply mul_nonneg _ (zpow_pos two_q_pos _).le
        exact_mod_cast hb
      linarith
    show d.toRat ≤ Dyadic.toRat (roundUpSpec d p)
    simp only [roundUpSpec, if_neg h]
    rw [← hsh_def, ← hden_def, ← hq_def, ← hr_def]
    split_ifs with h1
    · have hr_eq : r = 0 := by simpa using h1
      exact hgoal q (by omega)
    · exact hgoal (q + 1) (by omega)

end RoundBounds

end Dyadic

/-! ## Ball arithmetic preserves enclosure -/

namespace Ball

/-- Enclosure in distance-to-midpoint form. -/
theorem encloses_iff_abs {b : Ball} {r : ℝ} :
    b.Encloses r ↔ |r - (b.mid.toRat : ℝ)| ≤ (b.rad.toRat : ℝ) := by
  unfold Ball.Encloses
  rw [abs_sub_le_iff]
  constructor <;> intro h <;> obtain ⟨h1, h2⟩ := h <;> constructor <;>
    push_cast at * <;> linarith

/-- Any enclosing ball has nonnegative radius. -/
theorem rad_nonneg_of_encloses {b : Ball} {r : ℝ} (h : b.Encloses r) :
    (0 : ℚ) ≤ b.rad.toRat := by
  obtain ⟨h1, h2⟩ := h
  have hle : ((b.mid.toRat - b.rad.toRat : ℚ) : ℝ) ≤
      ((b.mid.toRat + b.rad.toRat : ℚ) : ℝ) := le_trans h1 h2
  have := (Rat.cast_le (K := ℝ)).mp hle
  linarith

/-- Negation is exact. -/
theorem neg_encloses {b : Ball} {r : ℝ} (h : b.Encloses r) :
    (Ball.neg b).Encloses (-r) := by
  rw [encloses_iff_abs] at h ⊢
  have hmid : (Ball.neg b).mid = -b.mid := rfl
  have hrad : (Ball.neg b).rad = b.rad := rfl
  rw [hmid, hrad]
  have : |(-r) - ((-b.mid).toRat : ℝ)| = |r - (b.mid.toRat : ℝ)| := by
    rw [show ((-b.mid).toRat : ℚ) = -b.mid.toRat from Dyadic.toRat_neg b.mid]
    push_cast
    rw [← abs_neg]
    ring_nf
  rw [this]
  exact h

/-- The error term reserved by `Ball.add`/`Ball.mul` for midpoint rounding
really bounds it. -/
private lemma round_err_bound (m : Dyadic) (prec : ℤ) :
    |((m.round prec).toRat - m.toRat)| ≤
      (Dyadic.toRat (if m.round prec == m then (⟨0, 0⟩ : Dyadic) else ⟨1, prec - 1⟩)) := by
  by_cases hb : m.round prec = m
  · simp [hb, Dyadic.toRat]
  · rw [if_neg (by simpa [beq_iff_eq] using hb)]
    have : Dyadic.toRat ⟨1, prec - 1⟩ = (2 : ℚ) ^ (prec - 1) := by
      simp [Dyadic.toRat]
    rw [this]
    exact Dyadic.abs_toRat_round_sub_le m prec

/-- **`Ball.add` preserves enclosure.** -/
theorem add_encloses {bx bz : Ball} {r s : ℝ} (prec : ℤ)
    (hx : bx.Encloses r) (hz : bz.Encloses s) :
    (Ball.add bx bz prec).Encloses (r + s) := by
  have hrx : (0 : ℚ) ≤ bx.rad.toRat := rad_nonneg_of_encloses hx
  have hrz : (0 : ℚ) ≤ bz.rad.toRat := rad_nonneg_of_encloses hz
  rw [encloses_iff_abs] at hx hz ⊢
  -- name the components (definitional projections of `Ball.add`)
  set rawMid : Dyadic := bx.mid + bz.mid with hrawMid
  set newMid : Dyadic := rawMid.round prec with hnewMid
  set errD : Dyadic := if newMid == rawMid then (⟨0, 0⟩ : Dyadic) else ⟨1, prec - 1⟩
    with herrD
  set rawRad : Dyadic := bx.rad + bz.rad + errD with hrawRad
  have hmid : (Ball.add bx bz prec).mid = newMid := rfl
  have hrad : (Ball.add bx bz prec).rad = rawRad.abs.roundUp prec := rfl
  rw [hmid, hrad]
  -- error bound for the midpoint rounding
  have herr : |(newMid.toRat - rawMid.toRat : ℚ)| ≤ errD.toRat := by
    simpa [hnewMid, herrD] using round_err_bound rawMid prec
  have herr0 : (0 : ℚ) ≤ errD.toRat := le_trans (abs_nonneg _) herr
  -- radius chain: rawRad ≥ 0, so |rawRad| = rawRad, and roundUp only grows
  have hrawRad_val : rawRad.toRat = bx.rad.toRat + bz.rad.toRat + errD.toRat := by
    simp [hrawRad]
  have hrawRad0 : (0 : ℚ) ≤ rawRad.toRat := by rw [hrawRad_val]; positivity
  have hradge : rawRad.toRat ≤ (rawRad.abs.roundUp prec).toRat := by
    calc rawRad.toRat = rawRad.abs.toRat := by
          rw [Dyadic.toRat_abs, abs_of_nonneg hrawRad0]
      _ ≤ (rawRad.abs.roundUp prec).toRat := Dyadic.le_toRat_roundUp _ prec
  -- the triangle chain over ℝ
  have hrawMid_val : (rawMid.toRat : ℚ) = bx.mid.toRat + bz.mid.toRat := by
    simp [hrawMid]
  have hA : |(r + s) - ((rawMid.toRat : ℚ) : ℝ)| ≤
      (bx.rad.toRat : ℝ) + (bz.rad.toRat : ℝ) := by
    rw [hrawMid_val]
    push_cast
    calc |(r + s) - ((bx.mid.toRat : ℝ) + (bz.mid.toRat : ℝ))|
        = |(r - (bx.mid.toRat : ℝ)) + (s - (bz.mid.toRat : ℝ))| := by ring_nf
      _ ≤ |r - (bx.mid.toRat : ℝ)| + |s - (bz.mid.toRat : ℝ)| := abs_add_le _ _
      _ ≤ _ := add_le_add hx hz
  have hB : |((rawMid.toRat : ℚ) : ℝ) - (newMid.toRat : ℝ)| ≤ ((errD.toRat : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    exact_mod_cast herr
  calc |(r + s) - (newMid.toRat : ℝ)|
      ≤ |(r + s) - ((rawMid.toRat : ℚ) : ℝ)| +
          |((rawMid.toRat : ℚ) : ℝ) - (newMid.toRat : ℝ)| := abs_sub_le _ _ _
    _ ≤ ((bx.rad.toRat : ℝ) + (bz.rad.toRat : ℝ)) + ((errD.toRat : ℚ) : ℝ) :=
        add_le_add hA hB
    _ = ((rawRad.toRat : ℚ) : ℝ) := by rw [hrawRad_val]; push_cast; ring
    _ ≤ (((rawRad.abs.roundUp prec).toRat : ℚ) : ℝ) := by exact_mod_cast hradge

/-- **`Ball.mul` preserves enclosure.** -/
theorem mul_encloses {bx bz : Ball} {r s : ℝ} (prec : ℤ)
    (hx : bx.Encloses r) (hz : bz.Encloses s) :
    (Ball.mul bx bz prec).Encloses (r * s) := by
  have hrx : (0 : ℚ) ≤ bx.rad.toRat := rad_nonneg_of_encloses hx
  have hrz : (0 : ℚ) ≤ bz.rad.toRat := rad_nonneg_of_encloses hz
  rw [encloses_iff_abs] at hx hz ⊢
  set rawMid : Dyadic := bx.mid * bz.mid with hrawMid
  set newMid : Dyadic := rawMid.round prec with hnewMid
  set errD : Dyadic := if newMid == rawMid then (⟨0, 0⟩ : Dyadic) else ⟨1, prec - 1⟩
    with herrD
  set rawRad : Dyadic :=
    bx.mid.abs * bz.rad + bz.mid.abs * bx.rad + bx.rad * bz.rad + errD with hrawRad
  have hmid : (Ball.mul bx bz prec).mid = newMid := rfl
  have hrad : (Ball.mul bx bz prec).rad = rawRad.abs.roundUp prec := rfl
  rw [hmid, hrad]
  have herr : |(newMid.toRat - rawMid.toRat : ℚ)| ≤ errD.toRat := by
    simpa [hnewMid, herrD] using round_err_bound rawMid prec
  have herr0 : (0 : ℚ) ≤ errD.toRat := le_trans (abs_nonneg _) herr
  have hrawRad_val : rawRad.toRat =
      |bx.mid.toRat| * bz.rad.toRat + |bz.mid.toRat| * bx.rad.toRat +
        bx.rad.toRat * bz.rad.toRat + errD.toRat := by
    simp [hrawRad, Dyadic.toRat_abs]
  have hrawRad0 : (0 : ℚ) ≤ rawRad.toRat := by
    rw [hrawRad_val]; positivity
  have hradge : rawRad.toRat ≤ (rawRad.abs.roundUp prec).toRat := by
    calc rawRad.toRat = rawRad.abs.toRat := by
          rw [Dyadic.toRat_abs, abs_of_nonneg hrawRad0]
      _ ≤ (rawRad.abs.roundUp prec).toRat := Dyadic.le_toRat_roundUp _ prec
  have hrawMid_val : (rawMid.toRat : ℚ) = bx.mid.toRat * bz.mid.toRat := by
    simp [hrawMid]
  -- the interval product bound
  have hprod : |(r * s) - ((rawMid.toRat : ℚ) : ℝ)| ≤
      |(bx.mid.toRat : ℝ)| * (bz.rad.toRat : ℝ) +
        |(bz.mid.toRat : ℝ)| * (bx.rad.toRat : ℝ) +
        (bx.rad.toRat : ℝ) * (bz.rad.toRat : ℝ) := by
    rw [hrawMid_val]
    push_cast
    have hkey : (r * s) - (bx.mid.toRat : ℝ) * (bz.mid.toRat : ℝ) =
        (bx.mid.toRat : ℝ) * (s - (bz.mid.toRat : ℝ)) +
          (r - (bx.mid.toRat : ℝ)) * (bz.mid.toRat : ℝ) +
          (r - (bx.mid.toRat : ℝ)) * (s - (bz.mid.toRat : ℝ)) := by ring
    rw [hkey]
    have hrxR : (0 : ℝ) ≤ (bx.rad.toRat : ℝ) := by exact_mod_cast hrx
    have h1 : |(bx.mid.toRat : ℝ)| * |s - (bz.mid.toRat : ℝ)| ≤
        |(bx.mid.toRat : ℝ)| * (bz.rad.toRat : ℝ) :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    have h2 : |r - (bx.mid.toRat : ℝ)| * |(bz.mid.toRat : ℝ)| ≤
        |(bz.mid.toRat : ℝ)| * (bx.rad.toRat : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
        (le_of_eq (mul_comm _ _))
    have h3 : |r - (bx.mid.toRat : ℝ)| * |s - (bz.mid.toRat : ℝ)| ≤
        (bx.rad.toRat : ℝ) * (bz.rad.toRat : ℝ) :=
      mul_le_mul hx hz (abs_nonneg _) hrxR
    calc |_ + _ + _|
        ≤ |(bx.mid.toRat : ℝ) * (s - (bz.mid.toRat : ℝ))| +
            |(r - (bx.mid.toRat : ℝ)) * (bz.mid.toRat : ℝ)| +
            |(r - (bx.mid.toRat : ℝ)) * (s - (bz.mid.toRat : ℝ))| :=
          (abs_add_three _ _ _)
      _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_mul]
          exact add_le_add (add_le_add h1 h2) h3
  have hB : |((rawMid.toRat : ℚ) : ℝ) - (newMid.toRat : ℝ)| ≤ ((errD.toRat : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    exact_mod_cast herr
  calc |(r * s) - (newMid.toRat : ℝ)|
      ≤ |(r * s) - ((rawMid.toRat : ℚ) : ℝ)| +
          |((rawMid.toRat : ℚ) : ℝ) - (newMid.toRat : ℝ)| := abs_sub_le _ _ _
    _ ≤ (|(bx.mid.toRat : ℝ)| * (bz.rad.toRat : ℝ) +
          |(bz.mid.toRat : ℝ)| * (bx.rad.toRat : ℝ) +
          (bx.rad.toRat : ℝ) * (bz.rad.toRat : ℝ)) + ((errD.toRat : ℚ) : ℝ) :=
        add_le_add hprod hB
    _ = (((rawRad.toRat : ℚ)) : ℝ) := by
        rw [hrawRad_val]; push_cast [Rat.cast_abs]; ring
    _ ≤ (((rawRad.abs.roundUp prec).toRat : ℚ) : ℝ) := by exact_mod_cast hradge

end Ball

/-! ## `FastReal` arithmetic preserves enclosure -/

namespace FastReal

theorem neg_encloses {x : FastReal} {r : ℝ} (hx : x.Encloses r) :
    (-x).Encloses (-r) := fun n => Ball.neg_encloses (hx n)

theorem add_encloses {x y : FastReal} {r s : ℝ}
    (hx : x.Encloses r) (hy : y.Encloses s) :
    (x + y).Encloses (r + s) := fun n =>
  Ball.add_encloses _ (hx (n + 4)) (hy (n + 4))

theorem sub_encloses {x y : FastReal} {r s : ℝ}
    (hx : x.Encloses r) (hy : y.Encloses s) :
    (x - y).Encloses (r - s) := by
  intro n
  have h := add_encloses hx (neg_encloses hy) n
  rwa [show r + -s = r - s from by ring] at h

theorem mul_encloses {x y : FastReal} {r s : ℝ}
    (hx : x.Encloses r) (hy : y.Encloses s) :
    (x * y).Encloses (r * s) := fun _ =>
  Ball.mul_encloses _ (hx _) (hy _)

/-- Numeric literals enclose themselves. -/
theorem encloses_ofNat (n : ℕ) :
    (OfNat.ofNat n : FastReal).Encloses ((n : ℝ)) := by
  have h := FastReal.encloses_ofDyadic ⟨(n : ℤ), 0⟩
  have hval : ((Dyadic.toRat ⟨(n : ℤ), 0⟩ : ℚ) : ℝ) = (n : ℝ) := by
    simp [Dyadic.toRat]
  rwa [hval] at h

end FastReal

end Computable.Fast
