/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Recurrence

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Tactic.LinearCombination

/-! # Gegenbauer operator matrices
Multiplication, differentiation and parameter conversion have explicit sparse
columns. The target basis is explicit and all parameter denominators in the
ring identities are cleared. References: DLMF 18.9.1, 18.9.7, 18.9.19;
Olver--Townsend (2013), §2.
-/

public section
open Module
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R] (lam : R) (b : Basis ℕ R R[X])

/-- The derivative matrix in the next Gegenbauer basis has one diagonal
(DLMF 18.9.19). -/
theorem gegenbauer_derivative_matrix_succ
    (hb : ∀ k, b k = gegenbauer (lam + 1) k) (n i : ℕ) :
    b.toMatrix (fun j ↦ derivative (gegenbauer lam j)) i (n + 1) =
      if i = n then 2 * lam else 0 := by
  rw [Basis.toMatrix_apply, derivative_gegenbauer_succ, ← smul_eq_C_mul, ← hb]
  simp [Finsupp.single_apply, eq_comm]

/-- The derivative annihilates the constant column (DLMF 18.9.19). -/
theorem gegenbauer_derivative_matrix_zero (i : ℕ) :
    b.toMatrix (fun j ↦ derivative (gegenbauer lam j)) i 0 = 0 := by
  simp [Basis.toMatrix_apply]

/-- Differentiation has lower bandwidth zero and upper bandwidth one
(DLMF 18.9.19; Olver--Townsend 2013). -/
theorem gegenbauer_derivative_matrix_isBanded
    (hb : ∀ k, b k = gegenbauer (lam + 1) k) :
    (b.toMatrix (fun j ↦ derivative (gegenbauer lam j))).IsBanded 0 1 := by
  intro i j hij
  cases j with
  | zero => exact gegenbauer_derivative_matrix_zero lam b i
  | succ n =>
    rw [gegenbauer_derivative_matrix_succ lam b hb]
    exact ite_eq_right (by omega)

/-- Conversion preserves the constant column (DLMF 18.9.7). -/
theorem gegenbauer_conversion_matrix_zero
    (hb : ∀ k, b k = gegenbauer (lam + 1) k) (i : ℕ) :
    b.toMatrix (gegenbauer lam) i 0 = if i = 0 then 1 else 0 := by
  have hb0 : b 0 = 1 := by rw [hb, gegenbauer_zero]
  simp [Basis.toMatrix_apply, ← hb0, Finsupp.single_apply, eq_comm]

/-- Cleared linear column of parameter conversion (DLMF 18.9.7). -/
theorem gegenbauer_conversion_matrix_one
    (hb : ∀ k, b k = gegenbauer (lam + 1) k) (i : ℕ) :
    (lam + 1) * b.toMatrix (gegenbauer lam) i 1 = if i = 1 then lam else 0 := by
  have h := congrArg (fun p : R[X] ↦ b.repr p i) (gegenbauer_conversion_one lam)
  simp only [← smul_eq_C_mul] at h
  simpa [Basis.toMatrix_apply, ← hb, Finsupp.single_apply, eq_comm, mul_ite] using h

/-- Cleared conversion entries lie on the diagonal and second superdiagonal
(DLMF 18.9.7). -/
theorem gegenbauer_conversion_matrix_add_two
    (hb : ∀ k, b k = gegenbauer (lam + 1) k) (n i : ℕ) :
    (n + lam + 2) * b.toMatrix (gegenbauer lam) i (n + 2) =
      (if i = n + 2 then lam else 0) - (if i = n then lam else 0) := by
  have h := congrArg (fun p : R[X] ↦ b.repr p i) (gegenbauer_conversion lam n)
  simp only [← smul_eq_C_mul] at h
  simpa [Basis.toMatrix_apply, ← hb, Finsupp.single_apply, eq_comm, mul_sub, mul_ite] using h

/-- Cleared multiplication entries in the positive-index columns (DLMF 18.9.1). -/
theorem gegenbauer_mul_matrix_succ
    (hb : ∀ k, b k = gegenbauer lam k) (n i : ℕ) :
    (2 * (n + lam + 1)) * b.toMatrix (fun j ↦ X * gegenbauer lam j) i (n + 1) =
      (if i = n + 2 then (n : R) + 2 else 0) + (if i = n then n + 2 * lam else 0) := by
  have h := congrArg (fun p : R[X] ↦ b.repr p i) (gegenbauer_recurrence lam n)
  rw [mul_assoc] at h
  simp only [← smul_eq_C_mul] at h
  simp [← hb, Finsupp.single_apply, eq_comm] at h
  change _ * (b.repr (X * gegenbauer lam (n + 1))) i = _
  rw [← hb]
  split_ifs at h ⊢ <;> first | omega | linear_combination h

/-- The initial multiplication column (DLMF 18.9.1). -/
theorem gegenbauer_mul_matrix_zero
    (hb : ∀ k, b k = gegenbauer lam k) (i : ℕ) :
    (2 * lam) * b.toMatrix (fun j ↦ X * gegenbauer lam j) i 0 =
      if i = 1 then 1 else 0 := by
  have he : C (2 * lam) * (X * gegenbauer lam 0) = gegenbauer lam 1 := by
    simp [gegenbauer_one]
  have h := congrArg (fun p : R[X] ↦ b.repr p i) he
  simp only [← smul_eq_C_mul] at h
  simpa [Basis.toMatrix_apply, ← hb, Finsupp.single_apply, eq_comm] using h

section Field
variable {K : Type*} [Field K] [Algebra ℚ K] (lam : K) (B : Basis ℕ K K[X])

/-- The linear conversion column in divided form (DLMF 18.9.7). -/
theorem gegenbauer_conversion_matrix_one_div
    (hB : ∀ k, B k = gegenbauer (lam + 1) k) (i : ℕ) (hd : lam + 1 ≠ 0) :
    B.toMatrix (gegenbauer lam) i 1 = (if i = 1 then lam else 0) / (lam + 1) := by
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using gegenbauer_conversion_matrix_one lam B hB i

/-- Divided entries of Gegenbauer parameter conversion (DLMF 18.9.7). -/
theorem gegenbauer_conversion_matrix_add_two_div
    (hB : ∀ k, B k = gegenbauer (lam + 1) k) (n i : ℕ)
    (hd : (n : K) + lam + 2 ≠ 0) :
    B.toMatrix (gegenbauer lam) i (n + 2) =
      ((if i = n + 2 then lam else 0) - (if i = n then lam else 0)) / (n + lam + 2) := by
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using gegenbauer_conversion_matrix_add_two lam B hB n i

/-- Conversion has lower bandwidth zero and upper bandwidth two
(DLMF 18.9.7; Olver--Townsend 2013). -/
theorem gegenbauer_conversion_matrix_isBanded
    (hB : ∀ k, B k = gegenbauer (lam + 1) k)
    (hd : ∀ n : ℕ, (n : K) + lam + 1 ≠ 0) :
    (B.toMatrix (gegenbauer lam)).IsBanded 0 2 := by
  intro i j hij
  rcases j with _ | (_ | n)
  · rw [gegenbauer_conversion_matrix_zero lam B hB]
    exact ite_eq_right (by omega)
  · rw [gegenbauer_conversion_matrix_one_div lam B hB i (by simpa using hd 0)]
    simp [show i ≠ 1 by omega]
  · rw [gegenbauer_conversion_matrix_add_two_div lam B hB n i (by
      convert hd (n + 1) using 1
      push_cast
      ring)]
    simp [show i ≠ n + 2 by omega, show i ≠ n by omega]

/-- Divided positive-index multiplication columns (DLMF 18.9.1). -/
theorem gegenbauer_mul_matrix_succ_div
    (hB : ∀ k, B k = gegenbauer lam k) (n i : ℕ) (hd : (n : K) + lam + 1 ≠ 0) :
    B.toMatrix (fun j ↦ X * gegenbauer lam j) i (n + 1) =
      ((if i = n + 2 then (n : K) + 2 else 0) +
        (if i = n then n + 2 * lam else 0)) / (2 * (n + lam + 1)) := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).2
  simpa only [mul_comm] using gegenbauer_mul_matrix_succ lam B hB n i

/-- The divided initial multiplication column (DLMF 18.9.1). -/
theorem gegenbauer_mul_matrix_zero_div
    (hB : ∀ k, B k = gegenbauer lam k) (i : ℕ) (hd : lam ≠ 0) :
    B.toMatrix (fun j ↦ X * gegenbauer lam j) i 0 =
      (if i = 1 then 1 else 0) / (2 * lam) := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).2
  simpa only [mul_comm] using gegenbauer_mul_matrix_zero lam B hB i

/-- Multiplication is tridiagonal (DLMF 18.9.1; Olver--Townsend 2013). -/
theorem gegenbauer_mul_matrix_isBanded
    (hB : ∀ k, B k = gegenbauer lam k) (hzero : lam ≠ 0)
    (hd : ∀ n : ℕ, (n : K) + lam + 1 ≠ 0) :
    (B.toMatrix (fun j ↦ X * gegenbauer lam j)).IsBanded 1 1 := by
  intro i j hij
  cases j with
  | zero =>
    rw [gegenbauer_mul_matrix_zero_div lam B hB i hzero]
    simp [show i ≠ 1 by omega]
  | succ n =>
    rw [gegenbauer_mul_matrix_succ_div lam B hB n i (hd n)]
    simp [show i ≠ n + 2 by omega, show i ≠ n by omega]

end Field

end Polynomial
