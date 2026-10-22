/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Multiplication
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCoordinates
public import LeanFun.Mathlib.Analysis.Normed.Lp.Finsupp

/-! # Agreement of raw ℓ² multiplication with finite Jacobi coordinates

Reference: the shifted form of DLMF 18.9.2 and Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace Polynomial

/-- The initial raw coefficient column is exactly the initial polynomial recurrence. -/
theorem shiftedJacobiOneZeroL2_single_zero :
    shiftedJacobiOneZeroL2 (lp.single 2 0 1) =
      lp.single 2 1 (shiftedJacobiOneZeroUpper 0) +
      lp.single 2 0 (shiftedJacobiOneZeroDiag 0) := by
  apply lp.ext
  funext i
  cases i with
  | zero => simp [shiftedJacobiOneZeroL2_apply_zero]
  | succ i =>
    rw [shiftedJacobiOneZeroL2_apply_succ]
    by_cases hi : i = 0
    · subst i; simp
    · simp [lp.single_apply, hi]

/-- Every positive-degree raw column agrees with the three-term polynomial recurrence. -/
theorem shiftedJacobiOneZeroL2_single_succ (n : ℕ) :
    shiftedJacobiOneZeroL2 (lp.single 2 (n+1) 1) =
      lp.single 2 (n+2) (shiftedJacobiOneZeroUpper (n+1)) +
      lp.single 2 (n+1) (shiftedJacobiOneZeroDiag (n+1)) +
      lp.single 2 n (shiftedJacobiOneZeroLower (n+1)) := by
  apply lp.ext
  funext i
  cases i with
  | zero =>
    rw [shiftedJacobiOneZeroL2_apply_zero]
    cases n <;> simp
  | succ i =>
    rw [shiftedJacobiOneZeroL2_apply_succ]
    by_cases h1 : i = n+1
    · subst i; simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]
      split_ifs <;> simp_all
      omega
    by_cases h2 : i = n
    · subst i; simp [lp.single_apply]
    by_cases h3 : i+1 = n
    · subst n; simp [lp.single_apply, show i ≠ i+1+1 by omega]
    · simp [lp.single_apply, h1, h2, h3, show i+2 ≠ n+1 by omega]

/-- Polynomial coefficients in the raw shifted (1,0) basis, embedded into real ℓ². -/
def shiftedJacobiOneZeroCoefficients : ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  lp.finsuppL2.comp (shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)).repr.toLinearMap

/-- A basis polynomial has exactly its standard coordinate vector. -/
@[simp] theorem shiftedJacobiOneZeroCoefficients_basis (n : ℕ) :
    shiftedJacobiOneZeroCoefficients (shiftedJacobi 1 0 n) = lp.single 2 n 1 := by
  unfold shiftedJacobiOneZeroCoefficients
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← shiftedJacobiBasis_apply (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0) n, Module.Basis.repr_self, lp.finsuppL2_single]

/-- The bounded raw operator agrees with multiplication by x on every basis vector. -/
theorem shiftedJacobiOneZeroL2_coefficients_basis (n : ℕ) :
    shiftedJacobiOneZeroL2 (shiftedJacobiOneZeroCoefficients (shiftedJacobi 1 0 n)) =
      shiftedJacobiOneZeroCoefficients (X*shiftedJacobi 1 0 n) := by
  rw [shiftedJacobiOneZeroCoefficients_basis]
  cases n with
  | zero =>
    rw [X_mul_shiftedJacobi_one_zero_zero, shiftedJacobiOneZeroL2_single_zero]
    simp only [← smul_eq_C_mul, map_add, map_smul, shiftedJacobiOneZeroCoefficients_basis,
      ← lp.single_smul, smul_eq_mul, mul_one]
  | succ n =>
    rw [X_mul_shiftedJacobi_one_zero_succ, shiftedJacobiOneZeroL2_single_succ]
    simp only [← smul_eq_C_mul, map_add, map_smul, shiftedJacobiOneZeroCoefficients_basis,
      ← lp.single_smul, smul_eq_mul, mul_one]

/-- Exact polynomial multiplication is preserved by the raw ℓ² realization. -/
theorem shiftedJacobiOneZeroL2_coefficients (p : ℝ[X]) :
    shiftedJacobiOneZeroL2 (shiftedJacobiOneZeroCoefficients p) =
      shiftedJacobiOneZeroCoefficients (X*p) := by
  have he : shiftedJacobiOneZeroL2.toLinearMap.comp shiftedJacobiOneZeroCoefficients =
      shiftedJacobiOneZeroCoefficients.comp (LinearMap.mulLeft ℝ X) := by
    apply (shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
      (by norm_num : (-1 : ℝ) < 0)).ext
    intro n
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      shiftedJacobiBasis_apply, LinearMap.mulLeft_apply] using
      shiftedJacobiOneZeroL2_coefficients_basis n
  exact LinearMap.congr_fun he p

end Polynomial
