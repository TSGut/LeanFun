/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedCoefficientOperators

/-! Bounded multiplication in positive ultraspherical levels, OT §§3–4. -/
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open ContinuousLinearMap

/-- Coefficient of degree n+1 in x C_n^(k+1). -/
def positiveMulXUp (k n : ℕ) : ℂ :=
  (((n : ℝ) + 1) / (2 * ((n : ℝ) + k + 1)) : ℝ)

/-- Coefficient of degree n-1 in x C_n^(k+1); the backward shift omits n=0. -/
def positiveMulXDown (k n : ℕ) : ℂ :=
  (((n : ℝ) + 2 * k + 1) / (2 * ((n : ℝ) + k + 1)) : ℝ)

/-- The raising coefficient is bounded by one. -/
theorem norm_positiveMulXUp_le (k n : ℕ) : ‖positiveMulXUp k n‖ ≤ 1 := by
  rw [positiveMulXUp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]

/-- The lowering coefficient is bounded by one. -/
theorem norm_positiveMulXDown_le (k n : ℕ) : ‖positiveMulXDown k n‖ ≤ 1 := by
  rw [positiveMulXDown, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]

/-- Multiplication by x on square-summable C^(k+1) coefficients. -/
def boundedPositiveMulX (k : ℕ) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  lp.coefficientShiftRight.comp (lp.coefficientDiagonal (positiveMulXUp k)
    zero_le_one (norm_positiveMulXUp_le k)) +
  lp.coefficientShiftLeft.comp (lp.coefficientDiagonal (positiveMulXDown k)
    zero_le_one (norm_positiveMulXDown_le k))

/-- The constant coefficient of multiplication by x. -/
theorem boundedPositiveMulX_zero (k : ℕ) (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    boundedPositiveMulX k x 0 = positiveMulXDown k 1 * x 1 := by
  simp [boundedPositiveMulX]

/-- The positive-degree coefficients of multiplication by x. -/
theorem boundedPositiveMulX_succ (k i : ℕ) (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    boundedPositiveMulX k x (i + 1) =
      positiveMulXUp k i * x i + positiveMulXDown k (i + 2) * x (i + 2) := by
  simp [boundedPositiveMulX, Nat.add_assoc]

/-- Each multiplication column has at most two nonzero entries. -/
theorem boundedPositiveMulX_single (k j i : ℕ) :
    boundedPositiveMulX k (lp.single 2 j (1 : ℂ)) i =
      (if i = j + 1 then positiveMulXUp k j else 0) +
      (if i + 1 = j then positiveMulXDown k j else 0) := by
  cases i with
  | zero =>
    rw [boundedPositiveMulX_zero]
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> simp_all
  | succ i =>
    rw [boundedPositiveMulX_succ]
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> simp_all

/-- The bounded operator agrees with multiplication by x on polynomials. -/
theorem boundedPositiveMulX_coefficientLp (k : ℕ) (p : ℝ[X]) :
    boundedPositiveMulX k ((ultrasphericalBasis (k + 1)).coefficientLp p) =
      (ultrasphericalBasis (k + 1)).coefficientLp (X * p) := by
  let b := ultrasphericalBasis (k + 1)
  have hb (j : ℕ) : b j = gegenbauer ((k : ℝ) + 1) j := by simp [b]
  have h : ((boundedPositiveMulX k).restrictScalars ℝ).toLinearMap.comp b.coefficientLp =
      b.coefficientLp.comp (LinearMap.mulLeft ℝ X) := by
    apply b.ext
    intro j
    change boundedPositiveMulX k (b.coefficientLp (b j)) = b.coefficientLp (X * b j)
    rw [Module.Basis.coefficientLp_basis]
    ext i
    rw [boundedPositiveMulX_single, Module.Basis.coefficientLp_apply, hb]
    change _ = ((b.toMatrix (fun j ↦ X * gegenbauer ((k : ℝ) + 1) j) i j : ℝ) : ℂ)
    cases j with
    | zero =>
      have hd : 2 * ((k : ℝ) + 1) ≠ 0 := by positivity
      have he : b.toMatrix (fun j ↦ X * gegenbauer ((k : ℝ) + 1) j) i 0 =
          (if i = 1 then 1 else 0) / (2 * ((k : ℝ) + 1)) := by
        apply (eq_div_iff hd).2
        simpa only [mul_comm] using gegenbauer_mul_matrix_zero ((k : ℝ) + 1) b hb i
      rw [he]
      by_cases hi : i = 1 <;> simp [positiveMulXUp, hi, div_eq_mul_inv, mul_comm]
    | succ j =>
      have hc := congrArg (fun x : ℝ ↦ (x : ℂ))
        (gegenbauer_mul_matrix_succ ((k : ℝ) + 1) b hb j i)
      have hd : 2 * ((j : ℂ) + ((k : ℂ) + 1) + 1) ≠ 0 := by
        exact_mod_cast (show 2 * ((j : ℝ) + ((k : ℝ) + 1) + 1) ≠ 0 by positivity)
      apply mul_left_cancel₀ hd
      split_ifs at hc ⊢ <;> try omega
      all_goals push_cast at hc
      all_goals try simp only [positiveMulXUp, positiveMulXDown]
      all_goals push_cast
      all_goals ring_nf at hc hd ⊢
      all_goals field_simp [hd]
      all_goals first | linear_combination -hc | linear_combination -(2 * ((j : ℂ) + k + 2)) * hc
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 ↦ L p) h

/-- Polynomial functional calculus of the positive-level multiplication operator. -/
def boundedPositivePolynomialMultiplier (k : ℕ) (p : ℝ[X]) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  aeval (boundedPositiveMulX k) p

/-- Polynomial functional calculus agrees with polynomial multiplication. -/
theorem boundedPositivePolynomialMultiplier_coefficientLp (k : ℕ) (p q : ℝ[X]) :
    boundedPositivePolynomialMultiplier k p ((ultrasphericalBasis (k + 1)).coefficientLp q) =
      (ultrasphericalBasis (k + 1)).coefficientLp (p * q) := by
  unfold boundedPositivePolynomialMultiplier
  induction p using Polynomial.induction_on generalizing q with
  | C a =>
    rw [Polynomial.aeval_C]
    change a • (ultrasphericalBasis (k + 1)).coefficientLp q = _
    rw [← map_smul, smul_eq_C_mul]
  | add p r hp hr =>
    rw [map_add, add_apply, hp, hr, add_mul, map_add]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, mul_apply_eq_comp, aeval_X,
      boundedPositiveMulX_coefficientLp, ih]
    simp only [mul_assoc]

end Polynomial.Chebyshev
