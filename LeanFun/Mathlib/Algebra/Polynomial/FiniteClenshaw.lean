/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Clenshaw

/-!
# Clenshaw evaluation with finite recurrence data

Only the recurrence indices needed by the finite expansion are supplied.
This prevents evaluating unused partial recurrence coefficients.
References: Clenshaw (1955); DLMF §18.40(i).
-/

@[expose] public section

namespace Polynomial
variable {R : Type*} [Ring R]
/-- Finite backward state using only the recurrence indices below `n - 2`.
The last two coefficients need no recurrence evaluation (Clenshaw 1955). -/
def finiteClenshawState : (n : ℕ) → (Fin (n - 2) → R) → (Fin (n - 2) → R) →
    (Fin n → R) → R × R
  | 0, _, _, _ => (0, 0)
  | 1, _, _, c => (c 0, 0)
  | 2, _, _, c => (c 0, c 1)
  | n + 3, a, b, c =>
    let s := finiteClenshawState (n + 2)
      (fun i ↦ a ⟨i.val + 1, by omega⟩)
      (fun i ↦ b ⟨i.val + 1, by omega⟩)
      (fun i ↦ c ⟨i.val + 1, by omega⟩)
    (c 0 + b ⟨0, by omega⟩ * s.2, s.1 + a ⟨0, by omega⟩ * s.2)

/-- Finite data give the same suffix state as the stream-based recurrence. -/
theorem finiteClenshawState_eq (a b c : ℕ → R) (n k : ℕ) :
    finiteClenshawState n (fun i ↦ a (k + i.val)) (fun i ↦ b (k + i.val))
      (fun i ↦ c (k + i.val)) = clenshawState a b c n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => simp [finiteClenshawState, clenshawState]
    | 2 => simp [finiteClenshawState, clenshawState]
    | n + 3 =>
      have ht := ih (n + 2) (by omega) (k + 1)
      simp only [finiteClenshawState]
      simp only [Nat.add_assoc, Nat.add_comm 1] at ht
      rw [ht]
      simp [clenshawState]
end Polynomial
namespace Polynomial
variable {R : Type*} [Ring R]
/-- Clenshaw evaluation from finite recurrence data (DLMF §18.40(i)). -/
def finiteClenshaw (n : ℕ) (a b : Fin (n - 2) → R) (c : Fin n → R)
    (p₀ p₁ : R) : R :=
  let s := finiteClenshawState n a b c
  s.1 * p₀ + s.2 * p₁

/-- Finite and stream-based Clenshaw evaluation agree. -/
theorem finiteClenshaw_eq (a b c : ℕ → R) (p₀ p₁ : R) (n : ℕ) :
    finiteClenshaw n (fun i ↦ a i.val) (fun i ↦ b i.val) (fun i ↦ c i.val) p₀ p₁ =
      clenshaw a b c p₀ p₁ n := by
  have h := finiteClenshawState_eq a b c n 0
  simpa [finiteClenshaw, clenshaw, h] using
    congrArg (fun s : R × R ↦ s.1 * p₀ + s.2 * p₁) h
end Polynomial
