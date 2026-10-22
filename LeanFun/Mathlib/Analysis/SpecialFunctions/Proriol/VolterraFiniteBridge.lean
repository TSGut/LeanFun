/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Preconditioner
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Columns
public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterra
public import Mathlib.Algebra.Polynomial.Roots
/-! # Exact coordinate identities for finite Volterra assembly

Kernel multiplication by either coordinate is transported through the exact
Proriol assembly. The output reflection changes outer multiplication into
I-J, while inner multiplication acts by J on the input. The integration
diagonal agrees with the existing finite diagonal.
Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

@[expose] public noncomputable section
namespace Polynomial
/-- The raw polynomial coefficient map recovers every finite coefficient vector. -/
theorem shiftedJacobiOneZeroCoefficients_linearCombination (c : ℕ →₀ ℝ) :
    shiftedJacobiOneZeroCoefficients (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c) =
      lp.finsuppL2 c := by
  let B := shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  have hB : shiftedJacobi 1 0 = B := by
    funext n
    exact (shiftedJacobiBasis_apply _ _ n).symm
  change lp.finsuppL2 (B.repr (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c)) = _
  rw [hB, Module.Basis.repr_linearCombination]
private theorem eq_of_reflected_endpoint_eval_eq (p q : ℝ[X])
    (h : ∀ x : ℝ, x*p.eval (1-x) = x*q.eval (1-x)) : p = q := by
  have he : X*p.comp (1-X) = X*q.comp (1-X) := by
    apply Polynomial.funext
    intro x
    simpa only [eval_mul, eval_X, eval_comp, eval_sub, eval_one] using h x
  have hc := mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0) he
  have hh := congrArg (fun p : ℝ[X] ↦ p.comp (1-X)) hc
  simpa only [comp_assoc, sub_comp, one_comp, X_comp, sub_sub_cancel, comp_X] using hh
/-- The bounded raw diagonal agrees with the exact finite Jacobi diagonal. -/
theorem volterraRawDiagonal_finsupp (c : ℕ →₀ ℝ) :
    volterraRawDiagonal (lp.finsuppL2 c) = lp.finsuppL2 (MvPolynomial.volterraJacobiDiagonal c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single n a =>
    apply lp.ext
    funext i
    rw [lp.finsuppL2_single, MvPolynomial.volterraJacobiDiagonal_single,
      lp.finsuppL2_single, volterraRawDiagonal_apply]
    by_cases hi : i = n
    · subst i; simp only [lp.single_apply, Pi.single_eq_same]; ring
    · simp [lp.single_apply, hi]
end Polynomial
namespace MvPolynomial
open Polynomial
local notation "S" => Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
/-- Outer kernel multiplication becomes multiplication by 1-x in the reflected core. -/
theorem volterraProriolCore_mul_X_zero (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ) :
    S (volterraProriolCoefficients (K*X 0) c) =
      (1-Polynomial.X)*S (volterraProriolCoefficients K c) := by
  apply Polynomial.eq_of_reflected_endpoint_eval_eq
  intro x
  have h := polynomialVolterraIntegral_mul_X_zero K (fun y ↦ (S c).eval y) x
    (intervalIntegrable_polynomialKernel_mul K (S c).continuous.locallyIntegrable x 0 x)
  simp only [Real.volterraIntegral_ofKernel] at h
  change (∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) (K*X 0)*(S c).eval y) =
    (∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) K*(S c).eval y)*x at h
  rw [← volterraProriolCoefficients_exact, ← volterraProriolCoefficients_exact] at h
  rw [h]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  ring
/-- The outer-coordinate identity agrees exactly with the bounded raw operator I-J. -/
theorem volterraProriolCoefficients_raw_mul_X_zero (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) :
    lp.finsuppL2 (volterraProriolCoefficients (K*X 0) c) =
      (1-shiftedJacobiOneZeroL2) (lp.finsuppL2 (volterraProriolCoefficients K c)) := by
  rw [← shiftedJacobiOneZeroCoefficients_linearCombination,
    volterraProriolCore_mul_X_zero, sub_mul, one_mul, map_sub,
    ← shiftedJacobiOneZeroL2_coefficients, shiftedJacobiOneZeroCoefficients_linearCombination]
  rfl
/-- Inner kernel multiplication becomes multiplication of the input polynomial by x. -/
theorem volterraProriolCore_mul_X_one (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ) :
    S (volterraProriolCoefficients (K*X 1) c) =
      S (volterraProriolCoefficients K
        ((shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
          (by norm_num : (-1 : ℝ) < 0)).repr (Polynomial.X*S c))) := by
  apply Polynomial.eq_of_reflected_endpoint_eval_eq
  intro x
  rw [volterraProriolCoefficients_exact, volterraProriolCoefficients_exact,
    linearCombination_shiftedJacobi_repr]
  have h := polynomialVolterraIntegral_mul_X_one K (fun y ↦ (S c).eval y) x
    (intervalIntegrable_polynomialKernel_mul K
      (continuous_id.mul (S c).continuous).locallyIntegrable x 0 x)
  simpa only [Real.volterraIntegral_ofKernel, Polynomial.eval_mul, Polynomial.eval_X] using h
/-- Finite Proriol assembly respects addition of kernels. -/
theorem volterraProriolCoefficients_add_kernel (K L : MvPolynomial (Fin 2) ℝ) :
    volterraProriolCoefficients (K+L) = volterraProriolCoefficients K +
      volterraProriolCoefficients L := by
  simp only [volterraProriolCoefficients, map_add, LinearMap.add_comp, LinearMap.comp_add]
/-- Finite Proriol assembly respects scalar multiplication of the kernel. -/
theorem volterraProriolCoefficients_smul_kernel (a : ℝ) (K : MvPolynomial (Fin 2) ℝ) :
    volterraProriolCoefficients (a • K) = a • volterraProriolCoefficients K := by
  ext c n
  simp [volterraProriolCoefficients]
/-- Constant kernels reproduce the established finite integration diagonal. -/
theorem volterraProriolCoefficients_C (a : ℝ) :
    volterraProriolCoefficients (C a) = a • volterraJacobiDiagonal := by
  rw [C_eq_smul_one,
    volterraProriolCoefficients_smul_kernel, volterraProriolCoefficients_one]
end MvPolynomial
