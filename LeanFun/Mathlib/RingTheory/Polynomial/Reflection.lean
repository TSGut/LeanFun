/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Polynomial reflection and coefficient parity
Coefficient identities used in symmetric orthogonality measures and disk lifts.
-/

public section
namespace Polynomial

/-- Reflection multiplies each coefficient by the parity of its index. -/
theorem coeff_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) (j : ℕ) :
    (p.comp (-X)).coeff j = (-1 : R) ^ j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial k a =>
    have hpow : (-X : R[X]) ^ k = C ((-1 : R) ^ k) * X ^ k := by
      rw [show (-X : R[X]) = C (-1 : R) * X by simp, mul_pow, ← map_pow]
    rw [monomial_comp, hpow]
    simp only [coeff_C_mul, coeff_X_pow, coeff_monomial]
    by_cases h : j = k
    · subst j
      simp [mul_comm]
    · simp [h, Ne.symm h]

/-- A reflected real polynomial has no coefficients of the opposite parity. -/
theorem coeff_eq_zero_of_reflection {p : ℝ[X]} (n j : ℕ)
    (hp : p.comp (-X) = C ((-1 : ℝ) ^ n) * p) (hj : j % 2 ≠ n % 2) :
    p.coeff j = 0 := by
  have he := congrArg (fun p : ℝ[X] => p.coeff j) hp
  rw [coeff_comp_neg_X, coeff_C_mul] at he
  rw [neg_one_pow_eq_pow_mod_two j, neg_one_pow_eq_pow_mod_two n] at he
  have h₁ : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h₂ : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : (j % 2 = 0 ∧ n % 2 = 1) ∨ (j % 2 = 1 ∧ n % 2 = 0) := by omega
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂] at he <;> simp only [pow_zero, pow_one, one_mul, neg_one_mul] at he <;>
    linarith

/-- Coefficient parity also implies the corresponding reflection identity. -/
theorem comp_neg_X_eq_of_coeff_parity {p : ℝ[X]} (n : ℕ)
    (hp : ∀ j, j % 2 ≠ n % 2 → p.coeff j = 0) :
    p.comp (-X) = C ((-1 : ℝ)^n)*p := by
  ext j
  rw [coeff_comp_neg_X, coeff_C_mul]
  by_cases hj : j % 2 = n % 2
  · rw [neg_one_pow_eq_pow_mod_two j, neg_one_pow_eq_pow_mod_two n, hj]
  · simp [hp j hj]

end Polynomial
