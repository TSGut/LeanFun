/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ClassicalMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality

/-!
# Symmetric Jacobi measures in the Cartesian disk construction

The abstract inner-degree shift coincides with shifting both Jacobi parameters.
Reference: DLMF Table 18.3.1; Dunkl–Xu, disk construction.
-/

public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace Polynomial

/-- Symmetric Jacobi measures satisfy the closed support condition used on the disk. -/
theorem ae_mem_Icc_jacobiMeasure (α β : ℝ) :
    ∀ᵐ x ∂jacobiMeasure α β, x ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [ae_mem_Ioo_jacobiMeasure α β] with x hx
  exact ⟨hx.1.le,hx.2.le⟩

/-- The outer Cartesian shift equals the integer symmetric Jacobi measure shift,
including parameters with infinite mass. Reference: Dunkl–Xu, disk families. -/
theorem diskOuterMeasure_jacobi (α : ℝ) (k : ℕ) :
    diskOuterMeasure k ((jacobiMeasure α α).comap Subtype.val) =
      jacobiMeasure (α+k) (α+k) := by
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension ((1-X^2 : ℝ[X])^k)
  rw [diskOuterMeasure, he]
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal hφ]
  simp only [jacobiMeasure, openIntervalWeightMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).lintegral_map]
  erw [lintegral_withDensity_eq_lintegral_mul _
      (jacobiWeight α α).continuous.measurable.coe_nnreal_ennreal
      ((hw.coe_nnreal_ennreal.mul hφ).comp measurable_subtype_coe),
    lintegral_withDensity_eq_lintegral_mul _
      (jacobiWeight (α+k) (α+k)).continuous.measurable.coe_nnreal_ennreal
      (hφ.comp measurable_subtype_coe)]
  apply lintegral_congr
  intro x
  have hx : 0 ≤ ((1-X^2 : ℝ[X])^k).eval (x : ℝ) := by
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [x.property.1, x.property.2]) _
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hwval x hx]
  have hew : jacobiWeight (α+k) (α+k) x =
      jacobiWeight α α x * NNReal.mk (((1-X^2 : ℝ[X])^k).eval (x : ℝ)) hx := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, eval_pow, eval_sub, eval_one, eval_X]
    rw [jacobiWeight_add_nat]
    ring
  rw [hew, ENNReal.coe_mul, mul_assoc]

/-- The shifted Jacobi sequence is orthogonal for the abstract outer disk measure. -/
theorem isOrthogonal_jacobiSequence_diskOuterMeasure {α : ℝ} (hα : -1 < α) (k : ℕ) :
    (jacobiSequence (show -1 < α+k by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      (show -1 < α+k by have := Nat.cast_nonneg (α := ℝ) k; linarith)).IsOrthogonal
        (diskOuterMeasure k ((jacobiMeasure α α).comap Subtype.val)) := by
  constructor
  · intro m n
    exact ((hasFiniteMoments_jacobiMeasure hα hα).diskOuterMeasure
      (ae_mem_Icc_jacobiMeasure α α) k).integrable_mul _ _
  · intro m n hmn
    rw [diskOuterMeasure_jacobi]
    exact integral_mul_jacobi_eq_zero (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hmn

end Polynomial
