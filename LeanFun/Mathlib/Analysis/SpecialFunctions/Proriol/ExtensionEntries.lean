/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraJacobiCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalSequence
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Explicit marginal entries of Proriol extension

Extract the inner-degree-zero entries of the actual extension coordinates.
Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
namespace MvPolynomial
open Polynomial

/-- Marginal selection is exactly restriction to inner degree zero. -/
theorem proriolMarginalCoefficients_apply (c : (Σ n : ℕ, Fin (n+1)) →₀ ℝ) (n : ℕ) :
    proriolMarginalCoefficients c n = c ⟨n, 0⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single i a =>
    rw [proriolMarginalCoefficients_single]
    by_cases hi : i.2 = 0
    · by_cases hn : i.1 = n
      · have he : i = ⟨n, 0⟩ := Sigma.ext hn
          ((Fin.heq_ext_iff (congrArg (fun t : ℕ ↦ t+1) hn)).mpr (by simp only [hi, Fin.val_zero]))
        rw [he]
        simp
      · have he : (⟨n, 0⟩ : Σ n : ℕ, Fin (n+1)) ≠ i :=
          fun h ↦ hn (congrArg Sigma.fst h).symm
        simp [hi, Finsupp.single_eq_of_ne (Ne.symm hn), Finsupp.single_eq_of_ne he]
    · have hn : (⟨n, 0⟩ : Σ n : ℕ, Fin (n+1)) ≠ i := by
        intro he
        subst i
        exact hi rfl
      simp [hi, Finsupp.single_eq_of_ne hn]

/-- The marginal coefficient vector of one extended Jacobi mode is a single
explicit diagonal entry. This is an equality of actual extension coordinates. -/
theorem proriolMarginalCoefficients_extension_shiftedJacobi (n : ℕ) :
    proriolMarginalCoefficients
      (proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
        (natDegree_shiftedJacobi_le 1 0 n)) =
      Finsupp.single n ((-1 : ℝ)^n / ((n : ℝ)+1)) := by
  let c := proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
    (natDegree_shiftedJacobi_le 1 0 n)
  have h : (1-Polynomial.X) * Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
      (proriolMarginalCoefficients c) =
      (1-Polynomial.X) * Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
        (Finsupp.single n ((-1 : ℝ)^n / ((n : ℝ)+1))) := by
    apply Polynomial.funext
    intro x
    have he := eval_proriolMarginalPolynomial c x
    rw [show proriolVolterraSynthesis c = triangleExtendY (shiftedJacobi 1 0 n) from
      proriolVolterraSynthesis_extension _ _ _, triangleMarginal_extendY_shiftedJacobi] at he
    change ((1-Polynomial.X) * Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
      (proriolMarginalCoefficients c)).eval x = _ at he
    rw [he, Finsupp.linearCombination_single]
    simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hn : (1-Polynomial.X : ℝ[X]) ≠ 0 := by
    intro hz
    have := congrArg (fun p : ℝ[X] ↦ p.coeff 1) hz
    norm_num [Polynomial.coeff_one] at this
  have he := mul_left_cancel₀ hn h
  exact (shiftedJacobiSequence (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)).linearIndependent he

/-- All inner-degree-zero entries, including the off-degree zeros. -/
theorem proriolExtensionCoefficients_shiftedJacobi_inner_zero (n m : ℕ) :
    proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
      (natDegree_shiftedJacobi_le 1 0 n) ⟨m, 0⟩ =
      if n = m then (-1 : ℝ)^n / ((n : ℝ)+1) else 0 := by
  classical
  rw [← proriolMarginalCoefficients_apply, proriolMarginalCoefficients_extension_shiftedJacobi,
    Finsupp.single_apply]

private theorem proriol_zero_zero : proriol 0 0 0 0 0 = 1 := by
  norm_num [proriol, shiftedJacobi, scaledLift]
private theorem proriol_one_zero : proriol 0 0 0 1 0 = C 3 * X 0 - C 2 := by
  norm_num [proriol, shiftedJacobi, jacobi_one, scaledLift, Finset.sum_range_succ]
  simp only [map_ofNat]
  have h : C (3 / 2 : ℝ) * 2 = (3 : MvPolynomial (Fin 2) ℝ) := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num [map_ofNat]
  linear_combination (X 0 - 1) * h
private theorem proriol_one_one : proriol 0 0 0 1 1 = C 2 * X 1 - X 0 := by
  norm_num [proriol, shiftedJacobi, jacobi_one, scaledLift, Finset.sum_range_succ,
    Polynomial.coeff_one, map_ofNat]
  ring

/-- The complete constant-input extension column. -/
theorem proriolExtensionCoefficients_shiftedJacobi_zero :
    proriolExtensionCoefficients 0 (shiftedJacobi 1 0 0)
      (natDegree_shiftedJacobi_le 1 0 0) = Finsupp.single ⟨0, 0⟩ 1 := by
  apply proriolVolterraSynthesis_injective
  rw [proriolVolterraSynthesis_extension, proriolVolterraSynthesis,
    Finsupp.linearCombination_single]
  simp [proriol_zero_zero, shiftedJacobi]

/-- The complete linear-input column in the signed Volterra normalization. -/
theorem proriolExtensionCoefficients_shiftedJacobi_one :
    proriolExtensionCoefficients 1 (shiftedJacobi 1 0 1)
      (natDegree_shiftedJacobi_le 1 0 1) =
      Finsupp.single ⟨1, 0⟩ (-(1/2)) + Finsupp.single ⟨1, 1⟩ (3/2) := by
  apply proriolVolterraSynthesis_injective
  rw [proriolVolterraSynthesis_extension, map_add]
  simp only [proriolVolterraSynthesis, Finsupp.linearCombination_single]
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, eval_triangleExtendY]
  simp only [map_add, smul_eval, eval_triangleReflect]
  norm_num only [Fin.val_zero, Fin.val_one]
  rw [proriol_one_zero, proriol_one_one]
  norm_num [shiftedJacobi, jacobi_one, map_ofNat]
  ring

end MvPolynomial
