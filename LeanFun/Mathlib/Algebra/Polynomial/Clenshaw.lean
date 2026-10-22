/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Ring

/-!
# Exact Clenshaw evaluation

An executable backward recurrence for a family satisfying
`p (k + 2) = a k * p (k + 1) + b k * p k`.
The state represents a suffix as a linear combination of two consecutive members.
No division, orthogonality, or nondegeneracy is needed by the generic algorithm.
Reference: Clenshaw (1955); DLMF §3.11(ii), §18.40(i).
-/

@[expose] public section

namespace Polynomial

section Algorithm
variable {R : Type*} [Ring R]

/-- Backward Clenshaw state for `n` coefficients, starting at index `k`.
There is one recursive call per coefficient. If the tail state is `(u, v)`,
substituting the three-term recurrence gives the new state `(c k + b k * v, u + a k * v)`.
-/
def clenshawState (a b c : ℕ → R) : ℕ → ℕ → R × R
  | 0, _ => (0, 0)
  | n + 1, k =>
    let s := clenshawState a b c n (k + 1)
    (c k + b k * s.2, s.1 + a k * s.2)

/-- Evaluate the first `n` coefficients, including the full constant coefficient.
The initial values `p₀` and `p₁` are supplied separately to avoid artificial
singularities in formulas for the three-term recurrence at the initial index. -/
def clenshaw (a b c : ℕ → R) (p₀ p₁ : R) (n : ℕ) : R :=
  let s := clenshawState a b c n 0
  s.1 * p₀ + s.2 * p₁

/-- An empty expansion evaluates to zero. -/
@[simp] theorem clenshaw_zero (a b c : ℕ → R) (p₀ p₁ : R) :
    clenshaw a b c p₀ p₁ 0 = 0 := by
  simp [clenshaw, clenshawState]

/-- A constant expansion uses the full initial coefficient. -/
@[simp] theorem clenshaw_one (a b c : ℕ → R) (p₀ p₁ : R) :
    clenshaw a b c p₀ p₁ 1 = c 0 * p₀ := by
  simp [clenshaw, clenshawState]

/-- Clenshaw state commutes with ring homomorphisms. This transports polynomial
recurrences to operators without assuming that all operators commute. -/
theorem clenshawState_map {S : Type*} [Ring S] (f : R →+* S)
    (a b c : ℕ → R) (n k : ℕ) :
    clenshawState (f ∘ a) (f ∘ b) (f ∘ c) n k =
      (f (clenshawState a b c n k).1, f (clenshawState a b c n k).2) := by
  induction n generalizing k with
  | zero => simp [clenshawState]
  | succ n ih => simp [clenshawState, ih]

/-- Clenshaw evaluation commutes with a ring homomorphism, in the full-constant
convention (Clenshaw 1955). -/
theorem clenshaw_map {S : Type*} [Ring S] (f : R →+* S)
    (a b c : ℕ → R) (p₀ p₁ : R) (n : ℕ) :
    clenshaw (f ∘ a) (f ∘ b) (f ∘ c) (f p₀) (f p₁) n =
      f (clenshaw a b c p₀ p₁ n) := by
  simp [clenshaw, clenshawState_map]

end Algorithm

variable {R : Type*} [CommRing R]

/-- The backward state reconstructs the corresponding suffix of a finite expansion. -/
theorem clenshawState_spec (a b c p : ℕ → R)
    (hp : ∀ k, p (k + 2) = a k * p (k + 1) + b k * p k) (n k : ℕ) :
    (clenshawState a b c n k).1 * p k +
        (clenshawState a b c n k).2 * p (k + 1) =
      ∑ i ∈ Finset.range n, c (k + i) * p (k + i) := by
  induction n generalizing k with
  | zero => simp [clenshawState]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have ht := ih (k + 1)
    simp only [Nat.add_assoc, Nat.add_comm 1] at ht
    rw [← ht]
    simp only [clenshawState, hp]
    ring

/-- Exactness of Clenshaw evaluation for the first `n` coefficients. -/
theorem clenshaw_eq_sum (a b c p : ℕ → R)
    (hp : ∀ k, p (k + 2) = a k * p (k + 1) + b k * p k) (n : ℕ) :
    clenshaw a b c (p 0) (p 1) n = ∑ i ∈ Finset.range n, c i * p i := by
  simpa [clenshaw] using clenshawState_spec a b c p hp n 0

end Polynomial
