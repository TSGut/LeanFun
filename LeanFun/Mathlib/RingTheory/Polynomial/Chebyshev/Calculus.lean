/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp

/-! # Polynomial antiderivatives in the Chebyshev basis
An unanchored antiderivative has bandwidth (1,1). Anchoring it at an endpoint
adds a constant row. Reference: ATAP, Chapter 19; Chebfun coefficient calculus.
-/

@[expose] public section
namespace Polynomial.Chebyshev
variable {K : Type*} [Field K] [CharZero K]

/-- The precise nonzero denominators needed by the adjacent-degree primitive. -/
def PrimitiveInput (K : Type*) [Field K] : ℕ → Prop
  | 0 => True
  | 1 => (4 : K) ≠ 0
  | n + 2 => (2 * (n + 3 : K)) ≠ 0 ∧ (2 * (n + 1 : K)) ≠ 0

/-- Characteristic zero supplies every primitive denominator. -/
theorem PrimitiveInput.ofCharZero (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    PrimitiveInput K n := by
  rcases n with _ | _ | n
  · trivial
  · norm_num [PrimitiveInput]
  · constructor <;> apply mul_ne_zero (by norm_num)
    · exact_mod_cast (show n + 3 ≠ 0 by omega)
    · exact_mod_cast (show n + 1 ≠ 0 by omega)

/-- An antiderivative with only adjacent Chebyshev degrees; the constant of
integration is free (ATAP, Chapter 19). -/
noncomputable def primitiveT (K : Type*) [Field K] (n : ℕ)
    (_d : PrimitiveInput K n := by exact Polynomial.Chebyshev.PrimitiveInput.ofCharZero _ _) : K[X] :=
  match n with
  | 0 => T K 1
  | 1 => Polynomial.C (1 / 4) * T K 2
  | n + 2 => Polynomial.C (1 / (2 * (n + 3 : K))) * T K (n + 3 : ℕ) -
      Polynomial.C (1 / (2 * (n + 1 : K))) * T K (n + 1 : ℕ)

/-- The two adjacent terms differentiate exactly to the original Chebyshev
polynomial, including degrees zero and one. -/
theorem derivative_primitiveT (n : ℕ) : derivative (primitiveT K n) = T K n := by
  rcases n with _ | _ | n
  · simp [primitiveT, T_one]
  · simp only [primitiveT, derivative_C_mul, T_derivative_eq_U,
      Int.reduceSub, U_one, Int.cast_ofNat]
    norm_num [← mul_assoc, ← C_ofNat, ← map_mul]
    rw [← C_ofNat 4, ← map_mul]
    norm_num
  · simp only [primitiveT, derivative_sub, derivative_C_mul, T_derivative_eq_U]
    have h₁ : (1 / (2 * (n + 3 : K))) * (n + 3 : K) = 1 / 2 := by
      have hn : (n + 3 : K) ≠ 0 := by exact_mod_cast (show n + 3 ≠ 0 by omega)
      field_simp
    have h₂ : (1 / (2 * (n + 1 : K))) * (n + 1 : K) = 1 / 2 := by
      have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
      field_simp
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Int.cast_add,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_one, ← C_eq_natCast, ← C_ofNat, ← C_1,
      ← map_add, ← mul_assoc, ← map_mul]
    rw [h₁, h₂]
    have hu := two_mul_T_eq_U_sub_U K (n : ℤ)
    have hi₁ : (n : ℤ) + 3 - 1 = n + 2 := by omega
    have hi₂ : (n : ℤ) + 1 - 1 = n := by omega
    rw [hi₁, hi₂, ← mul_sub, ← hu]
    rw [show (n : ℤ) + 1 + 1 = n + 2 by omega, ← mul_assoc, ← C_ofNat 2, ← map_mul]
    norm_num

/-- Finite coefficient integration is exact (Chebfun cumsum's polynomial core). -/
theorem derivative_sum_primitiveT (s : Finset ℕ) (a : ℕ → K) :
    derivative (∑ n ∈ s, Polynomial.C (a n) * primitiveT K n) = ∑ n ∈ s, Polynomial.C (a n) * T K n := by
  simp only [derivative_sum, derivative_C_mul, derivative_primitiveT]

/-- Endpoint-anchored integration adds the constant needed to make cumsum
vanish at its starting point. This constant row need not be banded. -/
noncomputable def primitiveTAt (a : K) (n : ℕ)
    (d : PrimitiveInput K n := by exact Polynomial.Chebyshev.PrimitiveInput.ofCharZero _ _) : K[X] :=
  primitiveT K n d - Polynomial.C ((primitiveT K n d).eval a)

/-- Anchoring does not alter the derivative. -/
@[simp] theorem derivative_primitiveTAt (a : K) (n : ℕ) :
    derivative (primitiveTAt a n) = T K n := by
  simp [primitiveTAt, derivative_primitiveT]

omit [CharZero K] in
/-- The anchored primitive vanishes at the chosen starting point. -/
@[simp] theorem eval_primitiveTAt_self (a : K) (n : ℕ) (d : PrimitiveInput K n) :
    (primitiveTAt a n d).eval a = 0 := by simp [primitiveTAt]

omit [CharZero K] in
/-- The negative-endpoint Neumann row in the full Chebyshev basis
(Olver–Townsend, boundary bordering). -/
theorem derivative_T_succ_eval_neg_one (n : ℕ) :
    (derivative (T K (n + 1 : ℕ))).eval (-1) = (-1 : K) ^ n * (n + 1 : K) ^ 2 := by
  rw [T_derivative_eq_U]
  simp only [eval_mul, eval_intCast, Nat.cast_add, Nat.cast_one,
    Int.add_sub_cancel, U_eval_neg_one, Int.cast_natCast]
  simp only [Int.cast_negOnePow_natCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
  ring

end Polynomial.Chebyshev
