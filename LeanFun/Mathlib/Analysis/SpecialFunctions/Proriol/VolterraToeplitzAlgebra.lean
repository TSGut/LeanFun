/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitz
public import Mathlib.Algebra.MonoidAlgebra.Module
/-! # Algebra of the ordered Jacobi Volterra expression

The kernel polynomial is quantized linearly, with outer-coordinate powers
placed to the left. Multiplication by the outer coordinate acts by H on the
left; multiplication by the inner coordinate acts by J on the right.
Reference: Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2
/-- Ordered kernel quantization as a linear map in the polynomial kernel. -/
def volterraPreconditionedLinear : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] (H →L[ℝ] H) :=
  (Finsupp.linearCombination ℝ (fun d : Fin 2 →₀ ℕ ↦
    reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap
/-- The linear quantization is the existing bounded ordered operator. -/
theorem volterraPreconditionedLinear_apply (K : MvPolynomial (Fin 2) ℝ) :
    volterraPreconditionedLinear K = volterraPreconditionedL2 K := rfl
/-- Ordered quantization respects kernel addition. -/
theorem volterraPreconditionedL2_add (K L : MvPolynomial (Fin 2) ℝ) :
    volterraPreconditionedL2 (K+L) = volterraPreconditionedL2 K+volterraPreconditionedL2 L :=
  volterraPreconditionedLinear.map_add K L
/-- Each kernel monomial has its prescribed ordered H/J action. -/
theorem volterraPreconditionedL2_monomial (d : Fin 2 →₀ ℕ) (a : ℝ) :
    volterraPreconditionedL2 (monomial d a) =
      a • (reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1)) := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single d a) = _
  exact Finsupp.linearCombination_single _ _ _
/-- Constant kernels act by scalar multiplication before applying the integration diagonal. -/
theorem volterraPreconditionedL2_C (a : ℝ) :
    volterraPreconditionedL2 (C a) = a • 1 := by
  change volterraPreconditionedL2 (monomial 0 a) = _
  rw [volterraPreconditionedL2_monomial]
  simp
/-- The outer kernel coordinate acts on the left by the reflected preconditioner. -/
theorem volterraPreconditionedL2_mul_X_zero (K : MvPolynomial (Fin 2) ℝ) :
    volterraPreconditionedL2 (K*X 0) = reflectedJacobiOneZeroL2*volterraPreconditionedL2 K := by
  induction K using MvPolynomial.induction_on' with
  | add K L hK hL => simp only [add_mul, volterraPreconditionedL2_add, hK, hL, mul_add]
  | monomial d a =>
    change volterraPreconditionedL2 (monomial d a * monomial (Finsupp.single 0 1) 1) = _
    rw [monomial_mul_monomial, mul_one, volterraPreconditionedL2_monomial,
      volterraPreconditionedL2_monomial]
    simp [Finsupp.add_apply, pow_succ']
    apply ContinuousLinearMap.ext
    intro u
    simp only [smul_apply, mul_apply_eq_comp, map_smul]
/-- The inner kernel coordinate acts on the right by Jacobi multiplication. -/
theorem volterraPreconditionedL2_mul_X_one (K : MvPolynomial (Fin 2) ℝ) :
    volterraPreconditionedL2 (K*X 1) = volterraPreconditionedL2 K*shiftedJacobiOneZeroL2 := by
  induction K using MvPolynomial.induction_on' with
  | add K L hK hL => simp only [add_mul, volterraPreconditionedL2_add, hK, hL]
  | monomial d a =>
    change volterraPreconditionedL2 (monomial d a * monomial (Finsupp.single 1 1) 1) = _
    rw [monomial_mul_monomial, mul_one, volterraPreconditionedL2_monomial,
      volterraPreconditionedL2_monomial]
    simp [Finsupp.add_apply, pow_succ]
    apply ContinuousLinearMap.ext
    intro u
    simp only [smul_apply, mul_apply_eq_comp]
end MvPolynomial
