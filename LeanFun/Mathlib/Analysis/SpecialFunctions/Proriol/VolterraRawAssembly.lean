/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzAlgebra
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraFiniteBridge
/-! # Ordered raw Volterra operators agree with finite Proriol assembly

The reflected output and integration diagonal are retained explicitly.
Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial
/-- Applying the raw integration diagonal to ordered polynomial quantization
recovers the exact finite Proriol assembly, including its output reflection. -/
theorem volterraRawDiagonal_preconditioned_finsupp (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) :
    volterraRawDiagonal (volterraPreconditionedL2 K (lp.finsuppL2 c)) =
      lp.finsuppL2 (volterraProriolCoefficients K c) := by
  induction K using MvPolynomial.induction_on generalizing c with
  | C a =>
    rw [volterraPreconditionedL2_C, volterraProriolCoefficients_C]
    simp only [smul_apply, LinearMap.smul_apply, one_apply_eq_self, map_smul, volterraRawDiagonal_finsupp]
  | add K L hK hL =>
    simp only [volterraPreconditionedL2_add, volterraProriolCoefficients_add_kernel,
      add_apply, LinearMap.add_apply, map_add, hK, hL]
  | mul_X K i hK =>
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at *
    · rw [volterraPreconditionedL2_mul_X_zero, mul_apply_eq_comp]
      have he := congrArg (fun A ↦ A (volterraPreconditionedL2 K (lp.finsuppL2 c)))
        volterraRawDiagonal_mul_reflectedJacobiOneZeroL2
      simp only [mul_apply_eq_comp] at he
      rw [he, hK]
      exact (volterraProriolCoefficients_raw_mul_X_zero K c).symm
    · let B := shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
        (by norm_num : (-1 : ℝ) < 0)
      let p := Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c
      let d := B.repr (Polynomial.X*p)
      have hJ : shiftedJacobiOneZeroL2 (lp.finsuppL2 c) = lp.finsuppL2 d := by
        rw [← shiftedJacobiOneZeroCoefficients_linearCombination,
          shiftedJacobiOneZeroL2_coefficients]
        rfl
      rw [volterraPreconditionedL2_mul_X_one, mul_apply_eq_comp, hJ, hK]
      have he := congrArg shiftedJacobiOneZeroCoefficients (volterraProriolCore_mul_X_one K c)
      simpa only [shiftedJacobiOneZeroCoefficients_linearCombination] using he.symm
end MvPolynomial
