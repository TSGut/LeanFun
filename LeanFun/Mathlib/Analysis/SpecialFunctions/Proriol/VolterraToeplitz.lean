/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Symbol
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Ordered polynomial Volterra factors and their diagonal symbol

The preconditioned expression is the ordered sum of H^r J^s with
H = D⁻¹(I-J)D. Its Laurent symbol is K(t,t), where t=(2+z+z⁻¹)/4.
Agreement with the integral operator and injectivity are separate obligations.
Reference: Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

/-- The bounded ordered polynomial expression in the reflected and raw Jacobi factors. -/
def volterraPreconditionedL2 (K : MvPolynomial (Fin 2) ℝ) : H →L[ℝ] H :=
  ∑ d ∈ K.support, K.coeff d • (reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1))

/-- The Laurent symbol obtained by restricting the polynomial kernel to its diagonal. -/
def volterraDiagonalLaurentSymbol (K : MvPolynomial (Fin 2) ℝ) : LaurentPolynomial ℝ :=
  ∑ d ∈ K.support, K.coeff d • shiftedJacobiLaurentSymbol^(d 0+d 1)

/-- Every polynomial expression differs compactly from its diagonal-symbol Toeplitz operator. -/
theorem isCompactOperator_volterraPreconditionedL2_sub_symbol
    (K : MvPolynomial (Fin 2) ℝ) :
    IsCompactOperator (volterraPreconditionedL2 K-
      lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)) := by
  classical
  simp only [volterraPreconditionedL2, volterraDiagonalLaurentSymbol, map_sum, map_smul,
    ← Finset.sum_sub_distrib]
  change (∑ d ∈ K.support, (K.coeff d •
    (reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1))-
      K.coeff d • lp.laurentToeplitz (shiftedJacobiLaurentSymbol^(d 0+d 1)))) ∈
    compactOperator (RingHom.id ℝ) H H
  apply Submodule.sum_mem
  intro d hd
  have he : K.coeff d • (reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1))-
      K.coeff d • lp.laurentToeplitz (shiftedJacobiLaurentSymbol^(d 0+d 1)) =
      K.coeff d • (reflectedJacobiOneZeroL2^(d 0)*shiftedJacobiOneZeroL2^(d 1)-
        lp.laurentToeplitz (shiftedJacobiLaurentSymbol^(d 0+d 1))) := by module
  rw [he]
  exact Submodule.smul_mem _ _ (isCompactOperator_reflectedJacobi_pow_mul_sub_symbol _ _)

/-- The finite Laurent sum is exactly evaluation of the kernel on the diagonal. -/
theorem volterraDiagonalLaurentSymbol_eq_eval₂ (K : MvPolynomial (Fin 2) ℝ) :
    volterraDiagonalLaurentSymbol K =
      K.eval₂ (algebraMap ℝ (LaurentPolynomial ℝ)) (fun _ ↦ shiftedJacobiLaurentSymbol) := by
  classical
  rw [eval₂_eq']
  simp only [volterraDiagonalLaurentSymbol, Fin.prod_univ_two, ← pow_add, Algebra.smul_def]

/-- Circle evaluation of the kernel symbol is its real diagonal restriction. -/
theorem volterraDiagonalLaurentSymbol_circle (K : MvPolynomial (Fin 2) ℝ)
    {T : {T : ℝ // T ≠ 0}} (x : AddCircle (T : ℝ)) :
    AddCircle.laurentSymbol (T := T)
      (AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom (volterraDiagonalLaurentSymbol K)) x =
      (eval (fun _ ↦ (1+(fourier 1 x).re)/2) K : ℂ) := by
  rw [volterraDiagonalLaurentSymbol_eq_eval₂]
  induction K using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, eval_C]
    rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.mapRingHom_single]
    rw [AddCircle.laurentSymbol_single]
    simp only [ContinuousMap.smul_apply, fourier_zero, smul_eq_mul, mul_one]
    rfl
  | add p q hp hq =>
    simp only [eval₂_add, map_add, ContinuousMap.add_apply, Complex.ofReal_add, hp, hq]
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X, map_mul, AddCircle.laurentSymbol_mul,
      ContinuousMap.mul_apply, hp, shiftedJacobiLaurentSymbol_circle,
      eval_mul, eval_X, Complex.ofReal_mul]

end MvPolynomial
