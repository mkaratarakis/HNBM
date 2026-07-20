/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange

/-!
# Folds over `finRange` are sums

The executable layer accumulates with `List.foldl` over `List.finRange n`,
because `FastReal`/`FastComplex` are not `AddCommMonoid`s and cannot use
`∑`. The specification layer states the same quantities with `∑`. These two
lemmas are the bridge, and they are pure `AddCommMonoid` facts with nothing
computable about them.
-/

open Finset

namespace Computable.Fast.Sums

variable {M : Type} [AddCommMonoid M] {n : ℕ}

private lemma foldl_add_eq_sum {α : Type} (f : α → M) :
    ∀ (l : List α) (init : M),
      l.foldl (fun acc v => acc + f v) init = init + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a t ih => intro init; simp [ih, add_assoc]

/-- A `finRange` fold of additions is a `∑`. -/
theorem finRange_foldl_add_eq_sum (f : Fin n → M) :
    (List.finRange n).foldl (fun acc v => acc + f v) 0 = ∑ v, f v := by
  rw [foldl_add_eq_sum, zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

/-- A guarded `finRange` fold of additions is a filtered `∑`. -/
theorem finRange_foldl_ite_add_eq_sum (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → M) :
    (List.finRange n).foldl (fun acc v => if p v then acc + f v else acc) 0
      = ∑ v ∈ Finset.univ.filter p, f v := by
  have hfun : (fun (acc : M) v => if p v then acc + f v else acc)
      = fun acc v => acc + (if p v then f v else 0) := by
    funext acc v
    split <;> simp
  rw [hfun, finRange_foldl_add_eq_sum]
  exact (Finset.sum_filter _ _).symm

end Computable.Fast.Sums
