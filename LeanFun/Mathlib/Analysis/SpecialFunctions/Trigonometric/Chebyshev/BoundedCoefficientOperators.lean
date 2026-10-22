/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientShift
public import LeanFun.Mathlib.Analysis.Polynomial.CoefficientLp
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.UltrasphericalLadder
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Bounded Chebyshev multiplication and conversion
Finite-band formulas extend to continuous operators on square-summable
coefficients with the full constant convention. Polynomial multipliers are
polynomials of the coordinate multiplication operator.
Reference: Olver--Townsend (2013), Section 2.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open ContinuousLinearMap

/-- Multiplication by x in the full-constant Chebyshev convention. -/
noncomputable def boundedMulX :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  (1 / 2 : ℂ) • (lp.coefficientShiftRight + lp.coefficientShiftLeft) +
    (1 / 2 : ℂ) • (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 0).smulRight
      (lp.single (E := fun _ : ℕ ↦ ℂ) 2 1 (1 : ℂ))

/-- Coordinate formula, retaining the exceptional constant input column. -/
theorem boundedMulX_apply (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    boundedMulX x i = (lp.coefficientShiftRight x i + x (i + 1)) / 2 +
      if i = 1 then x 0 / 2 else 0 := by
  change (1 / 2 : ℂ) * (lp.coefficientShiftRight x i + lp.coefficientShiftLeft x i) +
    (1 / 2 : ℂ) * (x 0 * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 1 1 i)) = _
  simp only [lp.coefficientShiftLeft_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> ring

/-- Multiplication by x sends the constant Chebyshev mode to the linear mode. -/
theorem boundedMulX_single_zero :
    boundedMulX (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
  ext i
  rw [boundedMulX_apply]
  rcases i with _ | (_ | i) <;>
    norm_num [lp.single_apply, Pi.single_apply]


/-- Positive multiplication columns are the usual two neighboring modes. -/
theorem boundedMulX_single_succ (j : ℕ) :
    boundedMulX (lp.single 2 (j + 1) (1 : ℂ)) =
      (1 / 2 : ℂ) • (lp.single 2 j (1 : ℂ) + lp.single 2 (j + 2) (1 : ℂ)) := by
  ext i
  rw [boundedMulX_apply]
  change (lp.coefficientShiftRight (lp.single 2 (j + 1) (1 : ℂ)) i +
    (lp.single (E := fun _ : ℕ ↦ ℂ) 2 (j + 1) 1 (i + 1))) / 2 +
    (if i = 1 then (lp.single (E := fun _ : ℕ ↦ ℂ) 2 (j + 1) 1 0) / 2 else 0) =
    (1 / 2 : ℂ) * ((lp.single (E := fun _ : ℕ ↦ ℂ) 2 j 1 i) +
      (lp.single (E := fun _ : ℕ ↦ ℂ) 2 (j + 2) 1 i))
  cases i with
  | zero =>
    simp only [lp.coefficientShiftRight_zero, lp.single_apply, Pi.single_apply]
    split_ifs <;> norm_num at * <;> omega
  | succ i =>
    simp only [lp.coefficientShiftRight_succ, lp.single_apply, Pi.single_apply]
    split_ifs <;> norm_num at * <;> omega


/-- The bounded coordinate operator agrees with the original polynomial coordinates. -/
theorem boundedMulX_coefficientLp (p : ℝ[X]) :
    boundedMulX (chebyshevBasis.coefficientLp p) = chebyshevBasis.coefficientLp (X * p) := by
  have h : (boundedMulX.restrictScalars ℝ).toLinearMap.comp chebyshevBasis.coefficientLp =
      chebyshevBasis.coefficientLp.comp (LinearMap.mulLeft ℝ X) := by
    apply chebyshevBasis.ext
    intro j
    change boundedMulX (chebyshevBasis.coefficientLp (chebyshevBasis j)) =
      chebyshevBasis.coefficientLp (X * chebyshevBasis j)
    rw [Module.Basis.coefficientLp_basis]
    cases j with
    | zero =>
      rw [boundedMulX_single_zero]
      have he : X * chebyshevBasis 0 = chebyshevBasis 1 := by
        simp [chebyshevBasis_apply, T_zero, T_one]
      rw [he, Module.Basis.coefficientLp_basis]
    | succ j =>
      rw [boundedMulX_single_succ]
      have he : X * chebyshevBasis (j + 1) =
          (1 / 2 : ℝ) • (chebyshevBasis j + chebyshevBasis (j + 2)) := by
        simp only [chebyshevBasis_apply, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        rw [T_add_two]
        have h : (2 : ℝ) • (X * T ℝ (↑j + 1)) =
            T ℝ ↑j + (2 * X * T ℝ (↑j + 1) - T ℝ ↑j) := by
          simp only [smul_eq_C_mul, map_ofNat]
          ring
        linear_combination (norm := module) (1 / 2 : ℝ) • h
      rw [he, map_smul, map_add, Module.Basis.coefficientLp_basis,
        Module.Basis.coefficientLp_basis]
      ext i
      change (1 / 2 : ℂ) * _ = ((1 / 2 : ℝ) : ℂ) * _
      push_cast
      rfl
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 ↦ L p) h

/-- Bounded entry conversion from T to U=C^(1). -/
noncomputable def boundedConversion :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  (1 / 2 : ℂ) • (1 - lp.coefficientShiftLeft.comp lp.coefficientShiftLeft) +
    (1 / 2 : ℂ) • lp.coefficientProjection 1

/-- The constant output coordinate has its exceptional normalization. -/
theorem boundedConversion_zero (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    boundedConversion x 0 = x 0 - x 2 / 2 := by
  change (1 / 2 : ℂ) * (x 0 - x 2) +
    (1 / 2 : ℂ) * (lp.coefficientProjection 1 x 0) = _
  rw [lp.coefficientProjection_apply]
  norm_num
  ring

/-- Positive output coordinates have the standard two-diagonal formula. -/
theorem boundedConversion_succ (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    boundedConversion x (i + 1) = (x (i + 1) - x (i + 3)) / 2 := by
  change (1 / 2 : ℂ) * (x (i + 1) - x (i + 1 + 1 + 1)) +
    (1 / 2 : ℂ) * (lp.coefficientProjection 1 x (i + 1)) = _
  rw [lp.coefficientProjection_apply, ite_eq_right (by omega : ¬i + 1 < 1)]
  simp only [mul_zero, add_zero, Nat.add_assoc]
  ring

/-- Polynomial multiplication as a bounded polynomial of the coordinate operator. -/
noncomputable def boundedPolynomialMultiplier (p : ℝ[X]) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  aeval boundedMulX p

/-- Polynomial functional calculus agrees with multiplication of polynomials. -/
theorem boundedPolynomialMultiplier_coefficientLp (p q : ℝ[X]) :
    boundedPolynomialMultiplier p (chebyshevBasis.coefficientLp q) =
      chebyshevBasis.coefficientLp (p * q) := by
  unfold boundedPolynomialMultiplier
  induction p using Polynomial.induction_on generalizing q with
  | C a =>
    rw [Polynomial.aeval_C]
    change a • chebyshevBasis.coefficientLp q = _
    rw [← map_smul, smul_eq_C_mul]
  | add p r hp hr =>
    rw [map_add, add_apply, hp, hr, add_mul, map_add]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, mul_apply_eq_comp, aeval_X,
      boundedMulX_coefficientLp, ih]
    simp only [mul_assoc]

/-- Bounded conversion agrees with the existing ultraspherical polynomial basis. -/
theorem boundedConversion_coefficientLp (p : ℝ[X]) :
    boundedConversion (chebyshevBasis.coefficientLp p) =
      (ultrasphericalBasis 1).coefficientLp p := by
  have hb (j : ℕ) : ultrasphericalBasis 1 j = gegenbauer (1 : ℝ) j := by
    simp
  have h : (boundedConversion.restrictScalars ℝ).toLinearMap.comp
      chebyshevBasis.coefficientLp = (ultrasphericalBasis 1).coefficientLp := by
    apply chebyshevBasis.ext
    intro j
    change boundedConversion (chebyshevBasis.coefficientLp (chebyshevBasis j)) = _
    rw [Module.Basis.coefficientLp_basis]
    ext i
    rw [Module.Basis.coefficientLp_apply, chebyshevBasis_apply]
    change boundedConversion (lp.single 2 j (1 : ℂ)) i =
      (((ultrasphericalBasis 1).toMatrix (fun j : ℕ ↦ T ℝ j) i j : ℝ) : ℂ)
    rcases j with _ | (_ | j)
    · rw [chebyshev_gegenbauer_conversion_zero _ hb]
      cases i with
      | zero => norm_num [boundedConversion_zero, lp.single_apply, Pi.single_apply]
      | succ i => simp [boundedConversion_succ, lp.single_apply]
    · rw [chebyshev_gegenbauer_conversion_one _ hb]
      cases i with
      | zero => norm_num [boundedConversion_zero, lp.single_apply, Pi.single_apply]
      | succ i =>
        simp only [boundedConversion_succ, lp.single_apply, Pi.single_apply]
        split_ifs <;> norm_num at *
    · rw [chebyshev_gegenbauer_conversion_add_two _ hb]
      cases i with
      | zero =>
        simp only [boundedConversion_zero, lp.single_apply, Pi.single_apply]
        split_ifs <;> norm_num at * <;> omega
      | succ i =>
        simp only [boundedConversion_succ, lp.single_apply, Pi.single_apply]
        split_ifs <;> norm_num at * <;> omega
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 ↦ L p) h

end Polynomial.Chebyshev
