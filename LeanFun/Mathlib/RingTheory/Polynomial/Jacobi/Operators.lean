/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Connection

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Jacobi differentiation and parameter-conversion matrices
The target basis is explicit; this permits every coefficient algebra in which
the chosen family is a basis. Rows index output coefficients and columns index
input coefficients. References: DLMF 18.9.5, 18.9.15; Olver--Townsend (2013).
-/

public section
open Module
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R] (α β : R) (b : Basis ℕ R R[X])

/-- Differentiation has one nonzero diagonal in the doubly shifted Jacobi basis
(DLMF 18.9.15; Olver--Townsend 2013). -/
theorem jacobi_derivative_matrix_succ
    (hb : ∀ k, b k = jacobi (α + 1) (β + 1) k) (n i : ℕ) :
    b.toMatrix (fun j ↦ derivative (jacobi α β j)) i (n + 1) =
      if i = n then algebraMap ℚ R (1 / 2) * (n + α + β + 2) else 0 := by
  rw [Basis.toMatrix_apply, derivative_jacobi_succ, ← smul_eq_C_mul, ← hb]
  simp [Finsupp.single_apply, eq_comm]

/-- The derivative matrix has zero constant column (DLMF 18.9.15). -/
theorem jacobi_derivative_matrix_zero (i : ℕ) :
    b.toMatrix (fun j ↦ derivative (jacobi α β j)) i 0 = 0 := by
  simp [Basis.toMatrix_apply]

/-- Jacobi differentiation has lower bandwidth zero and upper bandwidth one
(DLMF 18.9.15; Olver--Townsend 2013). -/
theorem jacobi_derivative_matrix_isBanded
    (hb : ∀ k, b k = jacobi (α + 1) (β + 1) k) :
    (b.toMatrix (fun j ↦ derivative (jacobi α β j))).IsBanded 0 1 := by
  intro i j hij
  cases j with
  | zero => exact jacobi_derivative_matrix_zero α β b i
  | succ n =>
    rw [jacobi_derivative_matrix_succ α β b hb]
    exact ite_eq_right (by omega)

/-- Cleared entries for raising the second parameter (DLMF 18.9.5). -/
theorem jacobi_raise_beta_matrix_succ
    (hb : ∀ k, b k = jacobi α (β + 1) k) (n i : ℕ) :
    (2 * n + α + β + 3) * b.toMatrix (jacobi α β) i (n + 1) =
      (if i = n + 1 then n + α + β + 2 else 0) +
        (if i = n then n + α + 1 else 0) := by
  have h := congrArg (fun p : R[X] ↦ b.repr p i) (jacobi_raise_beta α β n)
  simp only [← smul_eq_C_mul] at h
  simp only [map_add, map_smul, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ← hb] at h
  simpa [Basis.toMatrix_apply, Finsupp.single_apply, eq_comm, mul_ite] using h

/-- Cleared entries for raising the first parameter (DLMF 18.9.5 by reflection). -/
theorem jacobi_raise_alpha_matrix_succ
    (hb : ∀ k, b k = jacobi (α + 1) β k) (n i : ℕ) :
    (2 * n + α + β + 3) * b.toMatrix (jacobi α β) i (n + 1) =
      (if i = n + 1 then n + α + β + 2 else 0) -
        (if i = n then n + β + 1 else 0) := by
  have h := congrArg (fun p : R[X] ↦ b.repr p i) (jacobi_raise_alpha α β n)
  simp only [← smul_eq_C_mul] at h
  simp only [map_sub, map_smul, Finsupp.coe_sub, Pi.sub_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ← hb] at h
  simpa [Basis.toMatrix_apply, Finsupp.single_apply, eq_comm, mul_ite] using h

/-- Parameter conversion preserves the constant column (DLMF 18.9.5). -/
theorem jacobi_conversion_matrix_zero {α' β' : R}
    (hb : ∀ k, b k = jacobi α' β' k) (i : ℕ) :
    b.toMatrix (jacobi α β) i 0 = if i = 0 then 1 else 0 := by
  have hb0 : b 0 = 1 := by rw [hb, jacobi_zero]
  simp [Basis.toMatrix_apply, ← hb0, Finsupp.single_apply, eq_comm]

/-- Cleared multiplication entries for positive-index columns (DLMF 18.9.1--2). -/
theorem jacobi_mul_matrix_succ
    (hb : ∀ k, b k = jacobi α β k) (n i : ℕ) :
    ((2 * n + α + β + 3) * (2 * n + α + β + 2) * (2 * n + α + β + 4)) *
        b.toMatrix (fun j ↦ X * jacobi α β j) i (n + 1) =
      (if i = n + 2 then 2 * (n + 2) * (n + α + β + 2) *
        (2 * n + α + β + 2) else 0) -
      (if i = n + 1 then (2 * n + α + β + 3) * (α ^ 2 - β ^ 2) else 0) +
      (if i = n then 2 * (n + α + 1) * (n + β + 1) *
        (2 * n + α + β + 4) else 0) := by
  have he : C ((2 * n + α + β + 3) * (2 * n + α + β + 2) *
        (2 * n + α + β + 4)) * (X * jacobi α β (n + 1)) =
      C (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) *
        jacobi α β (n + 2) -
      C ((2 * n + α + β + 3) * (α ^ 2 - β ^ 2)) * jacobi α β (n + 1) +
      C (2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4)) * jacobi α β n := by
    have h := jacobi_recurrence α β n
    simp only [map_mul, map_add, map_sub, map_pow, map_natCast, map_ofNat] at h ⊢
    linear_combination -h
  have h := congrArg (fun p : R[X] ↦ b.repr p i) he
  simp only [← smul_eq_C_mul] at h
  simp only [map_add, map_sub, map_smul, Finsupp.coe_add, Finsupp.coe_sub,
    Pi.add_apply, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h
  simpa [Basis.toMatrix_apply, ← hb, Finsupp.single_apply, eq_comm, mul_ite] using h

/-- The initial multiplication column, without a spurious parameter singularity
(DLMF 18.9.1--2). -/
theorem jacobi_mul_matrix_zero
    (hb : ∀ k, b k = jacobi α β k) (i : ℕ) :
    (α + β + 2) * b.toMatrix (fun j ↦ X * jacobi α β j) i 0 =
      (if i = 1 then 2 else 0) + (if i = 0 then β - α else 0) := by
  have he : C (α + β + 2) * (X * jacobi α β 0) =
      C 2 * jacobi α β 1 + C (β - α) * jacobi α β 0 := by
    rw [jacobi_zero, jacobi_one]
    have hhalf : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
      have hm := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
      simpa only [map_mul, map_ofNat, map_one] using hm
    simp only [map_add, map_sub, map_mul, map_ofNat, map_one]
    have hh := congrArg (C : R →+* R[X]) hhalf
    simp only [map_mul, map_ofNat, map_one] at hh
    linear_combination -(C α + C β + 2) * (X - 1) * hh
  have h := congrArg (fun p : R[X] ↦ b.repr p i) he
  simp only [← smul_eq_C_mul] at h
  simp [Basis.toMatrix_apply, ← hb, Finsupp.single_apply, eq_comm] at h ⊢
  split_ifs at h ⊢ <;> first | omega | linear_combination h

section Field
variable {K : Type*} [Field K] [Algebra ℚ K]
  (a b : K) (B : Basis ℕ K K[X])

/-- Divided entries of the upper-bidiagonal second-parameter conversion
(DLMF 18.9.5). The denominator hypothesis is explicit. -/
theorem jacobi_raise_beta_matrix_succ_div
    (hB : ∀ k, B k = jacobi a (b + 1) k) (n i : ℕ)
    (hd : 2 * (n : K) + a + b + 3 ≠ 0) :
    B.toMatrix (jacobi a b) i (n + 1) =
      ((if i = n + 1 then n + a + b + 2 else 0) +
        (if i = n then n + a + 1 else 0)) / (2 * n + a + b + 3) := by
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using jacobi_raise_beta_matrix_succ a b B hB n i

/-- Divided entries of the upper-bidiagonal first-parameter conversion
(DLMF 18.9.5 by reflection). -/
theorem jacobi_raise_alpha_matrix_succ_div
    (hB : ∀ k, B k = jacobi (a + 1) b k) (n i : ℕ)
    (hd : 2 * (n : K) + a + b + 3 ≠ 0) :
    B.toMatrix (jacobi a b) i (n + 1) =
      ((if i = n + 1 then n + a + b + 2 else 0) -
        (if i = n then n + b + 1 else 0)) / (2 * n + a + b + 3) := by
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using jacobi_raise_alpha_matrix_succ a b B hB n i

/-- Raising the second parameter is upper bidiagonal (DLMF 18.9.5). -/
theorem jacobi_raise_beta_matrix_isBanded
    (hB : ∀ k, B k = jacobi a (b + 1) k)
    (hd : ∀ n : ℕ, 2 * (n : K) + a + b + 3 ≠ 0) :
    (B.toMatrix (jacobi a b)).IsBanded 0 1 := by
  intro i j hij
  cases j with
  | zero =>
    rw [jacobi_conversion_matrix_zero a b B hB]
    exact ite_eq_right (by omega)
  | succ n =>
    rw [jacobi_raise_beta_matrix_succ_div a b B hB n i (hd n)]
    simp [show i ≠ n + 1 by omega, show i ≠ n by omega]

/-- Raising the first parameter is upper bidiagonal (DLMF 18.9.5 by reflection). -/
theorem jacobi_raise_alpha_matrix_isBanded
    (hB : ∀ k, B k = jacobi (a + 1) b k)
    (hd : ∀ n : ℕ, 2 * (n : K) + a + b + 3 ≠ 0) :
    (B.toMatrix (jacobi a b)).IsBanded 0 1 := by
  intro i j hij
  cases j with
  | zero =>
    rw [jacobi_conversion_matrix_zero a b B hB]
    exact ite_eq_right (by omega)
  | succ n =>
    rw [jacobi_raise_alpha_matrix_succ_div a b B hB n i (hd n)]
    simp [show i ≠ n + 1 by omega, show i ≠ n by omega]

/-- The standard three rational multiplication entries (DLMF 18.9.2_2,
with positive input degree). -/
theorem jacobi_mul_matrix_succ_div (hB : ∀ k, B k = jacobi a b k) (n i : ℕ)
    (h2 : 2 * (n : K) + a + b + 2 ≠ 0)
    (h3 : 2 * (n : K) + a + b + 3 ≠ 0)
    (h4 : 2 * (n : K) + a + b + 4 ≠ 0) :
    B.toMatrix (fun j ↦ X * jacobi a b j) i (n + 1) =
      (if i = n + 2 then 2 * (n + 2) * (n + a + b + 2) /
        ((2 * n + a + b + 3) * (2 * n + a + b + 4)) else 0) +
      (if i = n + 1 then (b ^ 2 - a ^ 2) /
        ((2 * n + a + b + 2) * (2 * n + a + b + 4)) else 0) +
      (if i = n then 2 * (n + a + 1) * (n + b + 1) /
        ((2 * n + a + b + 2) * (2 * n + a + b + 3)) else 0) := by
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h3 h2) h4)
  rw [jacobi_mul_matrix_succ a b B hB n i]
  split_ifs <;> field_simp <;> ring

/-- The divided initial multiplication column (DLMF 18.9.2_2). -/
theorem jacobi_mul_matrix_zero_div (hB : ∀ k, B k = jacobi a b k) (i : ℕ)
    (hd : a + b + 2 ≠ 0) :
    B.toMatrix (fun j ↦ X * jacobi a b j) i 0 =
      ((if i = 1 then 2 else 0) + (if i = 0 then b - a else 0)) / (a + b + 2) := by
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using jacobi_mul_matrix_zero a b B hB i

/-- Jacobi multiplication is tridiagonal when the recurrence factors can be
cancelled (DLMF 18.9.1--2; Olver--Townsend 2013). -/
theorem jacobi_mul_matrix_isBanded (hB : ∀ k, B k = jacobi a b k)
    (hzero : a + b + 2 ≠ 0)
    (hd : ∀ n : ℕ, (2 * (n : K) + a + b + 3) *
      (2 * n + a + b + 2) * (2 * n + a + b + 4) ≠ 0) :
    (B.toMatrix (fun j ↦ X * jacobi a b j)).IsBanded 1 1 := by
  intro i j hij
  cases j with
  | zero =>
    have h := jacobi_mul_matrix_zero a b B hB i
    simp only [ite_eq_right (show i ≠ 1 by omega),
      ite_eq_right (show i ≠ 0 by omega), zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hzero
  | succ n =>
    have h := jacobi_mul_matrix_succ a b B hB n i
    simp only [ite_eq_right (show i ≠ n + 2 by omega),
      ite_eq_right (show i ≠ n + 1 by omega), ite_eq_right (show i ≠ n by omega),
      sub_self, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hd n)

end Field
end Polynomial
