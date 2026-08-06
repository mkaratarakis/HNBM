/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Data.Rat.Defs

/-!
# Deterministic pseudo-randomness for neurodynamic experiments

Several algorithms in the neurodynamic-optimization literature are *stochastic*, and so
cannot be run at all without a source of randomness:

* the Boltzmann machine update itself — `P(xᵢ = 1) = 1/(1 + exp(-uᵢ/T))` is a coin flip;
* the particle-swarm re-initialisation rule, which needs two draws `r₁, r₂ ∈ [0,1]`
  and two further `U(0,1)` draws per particle;
* bit-flip mutation, which flips `xⱼ` when a draw `κ` falls below the mutation
  probability `Pₘ`;
* the initial population `x⁽ⁱ⁾(0) ∈ {0,1}ⁿ` and velocities `v⁽ⁱ⁾ ∈ [-1,1]ⁿ`.

Lean functions are pure, so there is no ambient `random ()`. Instead we thread a `Seed`
explicitly. This is not a workaround — it is strictly better here: every run is
*reproducible*, so a reported experimental result can be replayed exactly, and a
disagreement between two runs is a real disagreement rather than a different draw.

## Design

`Rand α` is the type of seed-threading computations. It is a monad, so experiments read
in direct style while the seed is passed along behind the scenes.

The generator is **splitmix64** (Steele, Lea & Flood): a fixed-increment Weyl sequence
followed by an avalanche of xor-shift/multiply rounds. It is chosen over a plain linear
congruential generator because the low bits of an LCG are notoriously poor, and the
Bernoulli draws here consume exactly those bits.

## Scope

This file is deliberately dependency-light: it needs only `ℚ`, not the computable reals.
Uniform draws are exact rationals with denominator `2^53`. For the Boltzmann acceptance
of eq. (5) the acceptance threshold must be compared against a *real* number, which is
what `bernoulliWith` is for: the caller supplies the decision, and can implement it with
`FastReal`'s fuelled comparison — including deciding what to do when the comparison
exhausts its fuel and returns `none`.
-/

namespace HopfieldNet.Computations

/-- The state of the pseudo-random generator. -/
abbrev Seed := UInt64

/-- A seed-threading computation producing an `α`.

Purity is the point: `Rand α` is an ordinary function, so an experiment is reproducible
from its seed and can be replayed exactly. -/
def Rand (α : Type) : Type := Seed → α × Seed

namespace Rand

instance : Monad Rand where
  pure a := fun s => (a, s)
  bind x f := fun s => match x s with | (a, s') => f a s'

/-- Run a computation from `s`, returning the value and the final seed. -/
def run {α} (x : Rand α) (s : Seed) : α × Seed := x s

/-- Run a computation from `s`, discarding the final seed. -/
def eval {α} (x : Rand α) (s : Seed) : α := (x s).1

end Rand

/-! ### The generator -/

/-- The golden-ratio increment `⌊2⁶⁴/φ⌋`, odd so the Weyl sequence has full period. -/
def splitmixGamma : UInt64 := 0x9E3779B97F4A7C15

/-- One splitmix64 step: advance the Weyl sequence, then avalanche.

The two multiply/xor-shift rounds mix high bits down into low bits, which is what makes
the low-order bits usable — the reason this is preferred to a bare LCG here. -/
def nextUInt64 : Rand UInt64 := fun s =>
  let s := s + splitmixGamma
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-! ### Uniform draws -/

/-- The number of significand bits used for a uniform rational draw. -/
def uniformBits : ℕ := 53

/-- A uniform draw from `[0,1)`, as an exact rational with denominator `2^53`.

Taking the *top* 53 bits (`>>> 11`) rather than the bottom is deliberate: it is the
high bits of a 64-bit generator that are of best quality. -/
def uniformQ : Rand ℚ := fun s =>
  match nextUInt64 s with
  | (z, s') => (((z >>> 11).toNat : ℚ) / ((2 : ℚ) ^ uniformBits), s')

/-- A uniform draw from `[-1,1)`, for the initial particle velocities `v⁽ⁱ⁾`. -/
def uniformSignedQ : Rand ℚ := fun s =>
  match uniformQ s with
  | (q, s') => (2 * q - 1, s')

/-- A uniform draw from `Fin n`, for picking a neuron to update. -/
def uniformFin (n : ℕ) [NeZero n] : Rand (Fin n) := fun s =>
  match nextUInt64 s with
  | (z, s') => (⟨z.toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩, s')

/-- A uniform bit. -/
def uniformBool : Rand Bool := fun s =>
  match nextUInt64 s with
  | (z, s') => (z % 2 == 1, s')

/-! ### Bernoulli draws -/

/-- Fire with probability `p`, comparing against an exact rational draw.

`p ≤ 0` never fires and `p ≥ 1` always fires, since the draw lies in `[0,1)`. -/
def bernoulli (p : ℚ) : Rand Bool := fun s =>
  match uniformQ s with
  | (r, s') => (decide (r < p), s')

/-- Fire when the caller's predicate accepts the uniform draw `r ∈ [0,1)`.

This is the hook for the Boltzmann acceptance `P(xᵢ = 1) = 1/(1 + exp(-uᵢ/T))`, whose
threshold is a genuine real number: pass a predicate that compares `r` against the
computed acceptance using `FastReal`'s fuelled comparison. Because that comparison
returns an `Option`, the caller — not this file — must decide the policy when it
exhausts its fuel. -/
def bernoulliWith (accept : ℚ → Bool) : Rand Bool := fun s =>
  match uniformQ s with
  | (r, s') => (accept r, s')

/-- Bit-flip mutation: negate `x` with probability `pm`. -/
def bitFlip (pm : ℚ) (x : Bool) : Rand Bool := fun s =>
  match bernoulli pm s with
  | (flip, s') => (if flip then !x else x, s')

/-! ### Vectors -/

/-- Draw `n` values, threading the seed left to right. -/
def vector {α} (n : ℕ) (x : Rand α) : Rand (Array α) := fun s =>
  Nat.rec (motive := fun _ => Array α × Seed) (#[], s)
    (fun _ ih => match x ih.2 with | (a, s') => (ih.1.push a, s')) n

/-- A uniform initial state `x⁽ⁱ⁾(0) ∈ {0,1}ⁿ`. -/
def uniformState (n : ℕ) : Rand (Array Bool) := vector n uniformBool

/-- A uniform initial velocity `v⁽ⁱ⁾ ∈ [-1,1)ⁿ`. -/
def uniformVelocity (n : ℕ) : Rand (Array ℚ) := vector n uniformSignedQ

/-! ### Smoke tests

These are `#eval`s rather than theorems: this file provides *executable* randomness, and
its statistical properties are not proved here. Connecting a sampled trajectory to the
stationary Gibbs measure is the job of the ergodicity layer, and is future work. -/

section Tests

/-- Count how many entries of a `Bool` array are `true`. -/
def countTrue (a : Array Bool) : ℕ := a.foldl (fun n b => if b then n + 1 else n) 0

-- Ten uniform draws from `[0,1)`.
#eval (vector 10 uniformQ).eval 2026

-- Frequency of `bernoulli (1/4)` over 10000 draws; expect ≈ 2500.
#eval countTrue ((vector 10000 (bernoulli (1/4))).eval 1)

-- Frequency of `bernoulli (1/4)` from a different seed; expect ≈ 2500 again.
#eval countTrue ((vector 10000 (bernoulli (1/4))).eval 99)

-- Fraction of 1000 draws from `Fin 64` landing in the lower half; expect ≈ 500.
#eval countTrue (((vector 1000 (uniformFin 64)).eval 7).map (fun i => i.val < 32))

-- Sign balance: negative signed draws out of 10000; expect ≈ 5000.
-- (Counting beats summing here: adding rationals with denominators up to `2^53`
-- builds an enormous common denominator and is very slow.)
#eval countTrue (((vector 10000 uniformSignedQ).eval 5).map (fun q => q < 0))

end Tests

end HopfieldNet.Computations
