/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Operators
public import Mathlib.Data.Int.NatAbs

/-! # Explicit Chebyshev multiplication entries
The full-constant convention changes both the constant row and the diagonal.
Reference: Olver--Townsend (2013), Section 2.2, equation (2.7).
-/

public section
namespace Polynomial
open Module

/-- Coordinates of a product of two Chebyshev modes, with the factor two cleared. -/
theorem two_mul_chebyshevBasis_repr_mul (m j i : ℕ) :
    2 * chebyshevBasis.repr (chebyshevBasis m * chebyshevBasis j) i =
      (if i = m + j then 1 else 0) +
        (if i = ((m : ℤ) - j).natAbs then 1 else 0) := by
  have h := congrArg (fun p : ℝ[X] ↦ chebyshevBasis.repr p i) (Chebyshev.T_mul_T ℝ m j)
  rw [mul_assoc, ← C_ofNat 2, ← smul_eq_C_mul] at h
  have ha : Chebyshev.T ℝ ((m : ℤ) + j) = chebyshevBasis (m + j) := by
    simp [chebyshevBasis_apply]
  have hs : Chebyshev.T ℝ ((m : ℤ) - j) = chebyshevBasis ((m : ℤ) - j).natAbs := by
    rw [chebyshevBasis_apply, Chebyshev.T_natAbs]
  rw [ha, hs, ← chebyshevBasis_apply m, ← chebyshevBasis_apply j] at h
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_add, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply, eq_comm] using h

/-- Column zero is the multiplier's own Chebyshev coefficient vector. -/
theorem chebyshev_mul_matrix_zero_column (p : ℝ[X]) (i : ℕ) :
    chebyshevBasis.toMatrix (fun j ↦ p * chebyshevBasis j) i 0 = chebyshevBasis.repr p i := by
  simp [Basis.toMatrix_apply, chebyshevBasis_apply, Chebyshev.T_zero]

/-- The positive columns of row zero are halved in the full-constant convention. -/
theorem chebyshev_mul_matrix_zero_row (p : ℝ[X]) {j : ℕ} (hj : 0 < j) :
    chebyshevBasis.toMatrix (fun j ↦ p * chebyshevBasis j) 0 j = chebyshevBasis.repr p j / 2 := by
  have h : (2 : ℝ) • ((chebyshevBasis.coord 0).comp (LinearMap.mulRight ℝ (chebyshevBasis j))) =
      chebyshevBasis.coord j := by
    apply chebyshevBasis.ext
    intro m
    change 2 * chebyshevBasis.repr (chebyshevBasis m * chebyshevBasis j) 0 =
      chebyshevBasis.repr (chebyshevBasis m) j
    rw [two_mul_chebyshevBasis_repr_mul]
    simp only [Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm, ne_of_gt hj, Int.natAbs_eq_zero, sub_eq_zero]
  have he := congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ ↦ L p) h
  change 2 * chebyshevBasis.repr (p * chebyshevBasis j) 0 = chebyshevBasis.repr p j at he
  change chebyshevBasis.repr (p * chebyshevBasis j) 0 = _
  linarith

/-- Positive-row, positive-column multiplication entries, displaying the extra
constant-coefficient contribution on the diagonal (Olver--Townsend, 2.7). -/
theorem chebyshev_mul_matrix_positive (p : ℝ[X]) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    chebyshevBasis.toMatrix (fun j ↦ p * chebyshevBasis j) i j =
      ((if i = j then 2 else 1) * chebyshevBasis.repr p ((i : ℤ) - j).natAbs +
        chebyshevBasis.repr p (i + j)) / 2 := by
  have h : (2 : ℝ) • ((chebyshevBasis.coord i).comp (LinearMap.mulRight ℝ (chebyshevBasis j))) =
      (if i = j then (2 : ℝ) else 1) • chebyshevBasis.coord ((i : ℤ) - j).natAbs +
        chebyshevBasis.coord (i + j) := by
    apply chebyshevBasis.ext
    intro m
    change 2 * chebyshevBasis.repr (chebyshevBasis m * chebyshevBasis j) i =
      (if i = j then 2 else 1) * chebyshevBasis.repr (chebyshevBasis m) ((i : ℤ) - j).natAbs +
        chebyshevBasis.repr (chebyshevBasis m) (i + j)
    rw [two_mul_chebyshevBasis_repr_mul]
    simp only [Basis.repr_self, Finsupp.single_apply]
    have hdiff (a b : ℕ) : ((a : ℤ) - b).natAbs = if b ≤ a then a - b else b - a := by
      split_ifs with hab
      · exact Int.natAbs_natCast_sub_natCast_of_ge hab
      · exact Int.natAbs_natCast_sub_natCast_of_le (by omega)
    simp only [hdiff]
    split_ifs <;> first | omega | norm_num
  have he := congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ ↦ L p) h
  change 2 * chebyshevBasis.repr (p * chebyshevBasis j) i =
      (if i = j then 2 else 1) * chebyshevBasis.repr p ((i : ℤ) - j).natAbs +
        chebyshevBasis.repr p (i + j) at he
  change chebyshevBasis.repr (p * chebyshevBasis j) i = _
  linarith

end Polynomial
