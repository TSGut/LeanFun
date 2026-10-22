/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticWitness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.UniformInnerBandwidth

/-! # Necessity of quadratic separation for uniform inner bandwidth
The all-degree witnesses contradict a bound chosen before the factor measures.
Reference: varying-measure quadratic obstruction and Cartesian disk separation.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Nonnegative nonseparated diagonal quadratics have no uniform inner bandwidth. -/
theorem not_hasUniformCartesianInnerBandwidth_coordinateQuadratic (A B C : ℝ)
    (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) (hC : C ≠ 0) :
    ¬ HasUniformCartesianInnerBandwidth (coordinateQuadratic A B C) := by
  rintro ⟨w, hw⟩
  obtain ⟨δ, hδ, hδ1, hM, hP, hn⟩ := exists_integralGramFactor_quadratic_distant_entry
    (β := 0) (by norm_num) A B C hA hAB hAC hC (w + 2) (by omega)
  have hβ : (-1 : ℝ) < 0 := by norm_num
  have hβ' : (-1 : ℝ) < 0 + 1 / 2 := by norm_num
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isNegInvariant_jacobiMeasure (0 : ℝ)
  have hx := ae_mem_Icc_diskDeformedMeasure hδ.le hδ1
    (ae_mem_Icc_jacobiMeasure (0 + 1 / 2) (0 + 1 / 2))
  have hz := ae_mem_Icc_jacobiMeasure 0 0
  apply hn
  apply hw _ _ (hasFiniteMoments_diskDeformedMeasure hδ.le hδ1
      (ae_mem_Icc_jacobiMeasure (0 + 1 / 2) (0 + 1 / 2)))
    (hasPositiveDefiniteIntegral_diskDeformed_jacobiMeasure hβ' hβ' hδ hδ1)
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    hx hz (dunklXuDeformedCartesianSystem hβ hδ hδ1) _
    (ae_coordinateQuadratic_nonneg_cartesianDiskMeasure hx hz A B C hA hAB.le hAC) hM hP
  left
  simp [diskDegreeOrder_evenSectorEmbedding, dunklXuEvenBlockCoordinates]
  omega

/-- Uniform bandwidth forces precisely one of the two separated quadratic cases. -/
theorem coordinateQuadratic_separated_of_uniform_inner_bandwidth (A B C : ℝ)
    (hA : 0 ≤ A) (hAB : 0 ≤ A + B) (hAC : 0 ≤ A + C)
    (h : HasUniformCartesianInnerBandwidth (coordinateQuadratic A B C)) : C * (A + B) = 0 := by
  by_contra hn
  have hc := (mul_ne_zero_iff.mp hn).1
  have hab := lt_of_le_of_ne hAB (Ne.symm (mul_ne_zero_iff.mp hn).2)
  exact not_hasUniformCartesianInnerBandwidth_coordinateQuadratic A B C hA hab hAC hc h

end MvPolynomial
