/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionEdge

/-! # Closed-form Jacobi-to-Proriol extension entries

Every degree-`n` input has a single nonzero degree block. In the signed reflected
Volterra convention its entries are `(-1)^(n-k) (2*k+1)/(n+1)`.
Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
open Polynomial MeasureTheory
namespace MvPolynomial

/-- Every entry in the nonzero degree block has an explicit rational formula,
including its sign in the reflected Volterra normalization. -/
theorem proriolExtensionCoefficients_shiftedJacobi_same_degree (n : ℕ) (k : Fin (n+1)) :
    proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
      (natDegree_shiftedJacobi_le 1 0 n) ⟨n, k⟩ =
      (-1 : ℝ)^(n-k.1)*(2*(k.1 : ℝ)+1)/((n : ℝ)+1) := by
  classical
  let c := proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
    (natDegree_shiftedJacobi_le 1 0 n)
  have he (y : ℝ) :
      (∑ i ∈ c.support, c i*((-1 : ℝ)^(i.1-i.2.1)*(shiftedJacobi 0 0 i.2.1).eval y)) =
        (shiftedJacobi 1 0 n).eval y := by
    have h := eval_proriolVolterraSynthesis_extension n (shiftedJacobi 1 0 n)
      (natDegree_shiftedJacobi_le 1 0 n) 0 y
    change eval (![0,y] : Fin 2 → ℝ) (proriolVolterraSynthesis c) = _ at h
    simpa only [proriolVolterraSynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, smul_eval, smul_eq_mul, eval_triangleReflect, sub_zero,
      eval_proriol_outer_one] using h
  have hi := congrArg (fun f : ℝ → ℝ ↦ ∫ y in (0 : ℝ)..1, f y*(shiftedJacobi 0 0 k.1).eval y)
    (funext he)
  simp_rw [Finset.sum_mul] at hi
  rw [intervalIntegral.integral_finsetSum] at hi
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul,
      integral_mul_shiftedJacobi_zero_zero] at hi
    rw [integral_shiftedJacobi_one_zero_mul_zero_zero n k.1 (by omega)] at hi
    have hs : (∑ i ∈ c.support, c i*((-1 : ℝ)^(i.1-i.2.1)*
        (if i.2.1 = k.1 then 1/(2*(k.1 : ℝ)+1) else 0))) =
        c ⟨n,k⟩*((-1 : ℝ)^(n-k.1)*(1/(2*(k.1 : ℝ)+1))) := by
      refine (Finset.sum_eq_single (s := c.support)
        (f := fun i : Σ m : ℕ, Fin (m+1) ↦ c i*((-1 : ℝ)^(i.1-i.2.1)*
          (if i.2.1 = k.1 then 1/(2*(k.1 : ℝ)+1) else 0))) ⟨n,k⟩ ?_ ?_).trans ?_
      · intro i him hne
        have hn : i.1 = n := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp him)
            (proriolExtensionCoefficients_shiftedJacobi_eq_zero_of_degree_ne n i h)
        have hk : i.2.1 ≠ k.1 := by
          intro h
          apply hne
          exact Sigma.ext hn ((Fin.heq_ext_iff (congrArg (fun t : ℕ ↦ t+1) hn)).mpr h)
        simp [hk]
      · intro hn
        rw [Finsupp.notMem_support_iff.mp hn]
        simp
      · simp
    rw [hs] at hi
    have hs2 : (-1 : ℝ)^(n-k.1)*(-1 : ℝ)^(n-k.1) = 1 := by
      rw [← mul_pow]; norm_num
    change c ⟨n,k⟩ = _
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    have hk : 2*(k.1 : ℝ)+1 ≠ 0 := by positivity
    field_simp at hi ⊢
    linear_combination (-1 : ℝ)^(n-k.1)*hi-c ⟨n,k⟩*((n : ℝ)+1)*hs2
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

/-- The entire extension column: all off-degree blocks vanish. -/
theorem proriolExtensionCoefficients_shiftedJacobi_apply (n : ℕ)
    (i : Σ m : ℕ, Fin (m+1)) :
    proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
      (natDegree_shiftedJacobi_le 1 0 n) i =
      if i.1 = n then (-1 : ℝ)^(n-i.2.1)*(2*(i.2.1 : ℝ)+1)/((n : ℝ)+1) else 0 := by
  classical
  by_cases hi : i.1 = n
  · obtain ⟨m,k⟩ := i
    dsimp only at hi
    subst m
    simpa only [ite_true] using proriolExtensionCoefficients_shiftedJacobi_same_degree n k
  · simp [hi, proriolExtensionCoefficients_shiftedJacobi_eq_zero_of_degree_ne n i hi]

end MvPolynomial
