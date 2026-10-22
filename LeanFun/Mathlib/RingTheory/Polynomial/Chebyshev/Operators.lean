/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Gegenbauer
public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded
import Mathlib.Algebra.Algebra.IsSimpleRing

/-! # Chebyshev entry matrices for the ultraspherical method
Rows are output coefficients and columns are input coefficients. The exceptional
constant column is retained in the full-constant convention.
Reference: Olver--Townsend (2013), equations 2.5, 2.8 and Section 3.
-/

public section
namespace Polynomial
open Module
variable {K : Type*} [Field K] [Algebra ℚ K] (b : Basis ℕ K K[X])

/-- Conversion leaves the constant column unchanged (Olver--Townsend, 2.8). -/
theorem chebyshev_gegenbauer_conversion_zero
    (hb : ∀ j, b j = gegenbauer (1 : K) j) (i : ℕ) :
    b.toMatrix (fun j : ℕ ↦ Chebyshev.T K j) i 0 = if i = 0 then 1 else 0 := by
  have hb0 : b 0 = 1 := by rw [hb, gegenbauer_zero]
  simp [Basis.toMatrix_apply, Chebyshev.T_zero, ← hb0, Finsupp.single_apply, eq_comm]

/-- The linear conversion column carries the factor one half (2.8). -/
theorem chebyshev_gegenbauer_conversion_one
    (hb : ∀ j, b j = gegenbauer (1 : K) j) (i : ℕ) :
    b.toMatrix (fun j : ℕ ↦ Chebyshev.T K j) i 1 = (if i = 1 then 1 else 0) / 2 := by
  have : CharZero K := Algebra.charZero_of_charZero ℚ K
  have he : 2 * Chebyshev.T K 1 = gegenbauer (1 : K) 1 := by
    simp [Chebyshev.T_one, gegenbauer_one, map_ofNat]
  have h := congrArg (fun p : K[X] ↦ b.repr p i) he
  rw [← C_ofNat 2, ← smul_eq_C_mul] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, ← hb, b.repr_self,
    Finsupp.single_apply] at h
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).2
  simpa [Basis.toMatrix_apply, eq_comm, mul_comm] using h

/-- The remaining conversion columns have entries one half and minus one half (2.8). -/
theorem chebyshev_gegenbauer_conversion_add_two
    (hb : ∀ j, b j = gegenbauer (1 : K) j) (n i : ℕ) :
    b.toMatrix (fun j : ℕ ↦ Chebyshev.T K j) i (n + 2) =
      ((if i = n + 2 then 1 else 0) - (if i = n then 1 else 0)) / 2 := by
  have : CharZero K := Algebra.charZero_of_charZero ℚ K
  have h := congrArg (fun p : K[X] ↦ b.repr p i) (two_mul_chebyshev_T_eq_gegenbauer_sub K n)
  rw [← C_ofNat 2, ← smul_eq_C_mul] at h
  simp only [map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul,
    ← hb, b.repr_self, Finsupp.single_apply] at h
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).2
  simpa [Basis.toMatrix_apply, eq_comm, mul_comm] using h

/-- Chebyshev-to-ultraspherical conversion has bandwidths `(0,2)` (2.8). -/
theorem chebyshev_gegenbauer_conversion_isBanded
    (hb : ∀ j, b j = gegenbauer (1 : K) j) :
    (b.toMatrix (fun j : ℕ ↦ Chebyshev.T K j)).IsBanded 0 2 := by
  intro i j hij
  rcases j with _ | (_ | n)
  · rw [chebyshev_gegenbauer_conversion_zero b hb]
    exact ite_eq_right (by omega)
  · rw [chebyshev_gegenbauer_conversion_one b hb]
    simp [show i ≠ 1 by omega]
  · rw [chebyshev_gegenbauer_conversion_add_two b hb]
    simp [show i ≠ n + 2 by omega, show i ≠ n by omega]

/-- A nonzero column of the `(k+1)`st derivative has one ultraspherical entry
(Olver--Townsend, Section 3). -/
theorem chebyshev_iterate_derivative_matrix (k : ℕ)
    (hb : ∀ j, b j = gegenbauer (k + 1 : K) j) (n i : ℕ) :
    b.toMatrix (fun j : ℕ ↦ derivative^[k + 1] (Chebyshev.T K j)) i (n + k + 1) =
      if i = n then (2 : K) ^ k * k.factorial * (n + k + 1) else 0 := by
  rw [Basis.toMatrix_apply, iterate_derivative_chebyshev_T,
    ← smul_eq_C_mul, ← hb]
  simp [Finsupp.single_apply, eq_comm]

/-- Columns below the derivative order vanish (Olver--Townsend, Section 3). -/
theorem chebyshev_iterate_derivative_matrix_zero (k i j : ℕ) (hj : j < k) :
    b.toMatrix (fun n : ℕ ↦ derivative^[k] (Chebyshev.T K n)) i j = 0 := by
  have : CharZero K := Algebra.charZero_of_charZero ℚ K
  rw [Basis.toMatrix_apply, iterate_derivative_chebyshev_T_eq_zero K hj]
  simp

/-- The `(k+1)`st derivative has bandwidths `(0,k+1)` into `C^(k+1)` (Section 3). -/
theorem chebyshev_iterate_derivative_isBanded (k : ℕ)
    (hb : ∀ j, b j = gegenbauer (k + 1 : K) j) :
    (b.toMatrix (fun j : ℕ ↦ derivative^[k + 1] (Chebyshev.T K j))).IsBanded 0 (k + 1) := by
  intro i j hij
  by_cases hj : j < k + 1
  · exact chebyshev_iterate_derivative_matrix_zero b _ _ _ hj
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + k + 1 := ⟨j - (k + 1), by omega⟩
    rw [chebyshev_iterate_derivative_matrix b k hb]
    exact ite_eq_right (by omega)

end Polynomial
