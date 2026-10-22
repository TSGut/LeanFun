/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.CoefficientInput
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Legendre.Structure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Completeness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Legendre Hilbert basis

Normalised Legendre polynomials are a Hilbert basis for unit-weight L² on
`[-1,1]`. References: DLMF 18.2(viii) and Table 18.3.1.
-/
public section
namespace Polynomial
open Real MeasureTheory Filter
open scoped ENNReal InnerProductSpace

/-- The unit Legendre weight is concentrated on `[-1,1]` (DLMF Table 18.3.1). -/
theorem ae_mem_Icc_legendreMeasure : ∀ᵐ x ∂legendreMeasure, x ∈ Set.Icc (-1) 1 := by
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ h ↦ Set.Ioc_subset_Icc_self h)

/-- Polynomial evaluations are dense in Legendre L² (DLMF 18.2(viii)). -/
theorem polynomialToL2_legendre_denseRange :
    DenseRange (polynomialToL2 hasFiniteMoments_legendreMeasure) :=
  polynomialToL2_denseRange hasFiniteMoments_legendreMeasure (-1) 1 ae_mem_Icc_legendreMeasure

/-- The Legendre pairing in L² (DLMF Table 18.3.1). -/
theorem inner_polynomialToL2_legendre (n m : ℕ) :
    ⟪polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n),
      polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ m)⟫_ℝ =
      if n = m then 2 / (2 * (n : ℝ) + 1) else 0 := by
  rw [inner_polynomialToL2, integral_mul_legendre_measure]
  split_ifs with h
  · subst m; rfl
  · rfl

/-- Normalised Legendre classes (DLMF Table 18.3.1). -/
noncomputable def normalizedLegendre (n : ℕ) : Lp ℝ 2 legendreMeasure :=
  (√(2 / (2 * (n : ℝ) + 1)))⁻¹ • polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n)

/-- The normalised Legendre family is orthonormal (DLMF Table 18.3.1). -/
theorem orthonormal_normalizedLegendre : Orthonormal ℝ normalizedLegendre := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedLegendre, inner_smul_left, inner_smul_right, conj_trivial,
    inner_polynomialToL2_legendre]
  by_cases h : n = m
  · subst m
    simp only [↓reduceIte]
    have hp : 0 < (2 / (2 * (n : ℝ) + 1) : ℝ) := by positivity
    calc
      _ = ((√(2 / (2 * (n : ℝ) + 1)))⁻¹ * (√(2 / (2 * (n : ℝ) + 1)))⁻¹) *
          (2 / (2 * (n : ℝ) + 1)) := by ring
      _ = 1 := by rw [← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  · simp [h]

/-- Legendre polynomial classes span the polynomial image in L² (DLMF 18.2(viii)). -/
theorem span_polynomialToL2_legendre :
    Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n))) =
      LinearMap.range (polynomialToL2 hasFiniteMoments_legendreMeasure) := by
  have hs : Submodule.span ℝ (Set.range (fun n : ℕ ↦ legendre ℝ n)) = ⊤ := by
    apply (legendreSequence ℝ).span
    intro n
    apply isUnit_iff_ne_zero.mpr
    exact leadingCoeff_ne_zero.mpr ((legendreSequence ℝ).ne_zero n)
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.map_top]
    using congrArg (Submodule.map (polynomialToL2 hasFiniteMoments_legendreMeasure)) hs

/-- The normalised Legendre family has dense span (DLMF 18.2(viii)). -/
theorem normalizedLegendre_dense_span :
    (Submodule.span ℝ (Set.range normalizedLegendre)).topologicalClosure = ⊤ := by
  have hd : (Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n)))).topologicalClosure = ⊤ := by
    rw [span_polynomialToL2_legendre]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp polynomialToL2_legendre_denseRange
  have hs : Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n))) ≤
      Submodule.span ℝ (Set.range normalizedLegendre) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    have hp : 0 < (2 / (2 * (n : ℝ) + 1) : ℝ) := by positivity
    have hz : √(2 / (2 * (n : ℝ) + 1)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hm := (Submodule.span ℝ (Set.range normalizedLegendre)).smul_mem
      (√(2 / (2 * (n : ℝ) + 1))) (Submodule.subset_span (Set.mem_range_self n))
    simpa only [SetLike.mem_coe, normalizedLegendre, smul_smul, mul_inv_cancel₀ hz, one_smul] using hm
  apply top_unique
  rw [← hd]
  exact Submodule.topologicalClosure_mono hs

/-- The Legendre Hilbert basis of weighted L² (DLMF Table 18.3.1; DLMF 18.2(viii)). -/
noncomputable def hilbertBasisLegendre : HilbertBasis ℕ ℝ (Lp ℝ 2 legendreMeasure) :=
  HilbertBasis.mk orthonormal_normalizedLegendre (by rw [normalizedLegendre_dense_span])

/-- The Hilbert basis vectors are the normalised Legendre classes (DLMF Table 18.3.1). -/
@[simp] theorem hilbertBasisLegendre_apply (n : ℕ) : hilbertBasisLegendre n = normalizedLegendre n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

/-- Normalisation as the usual positive square-root factor (DLMF Table 18.3.1). -/
theorem normalizedLegendre_eq (n : ℕ) :
    normalizedLegendre n = √((2 * (n : ℝ) + 1) / 2) •
      polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n) := by
  simp only [normalizedLegendre, ← Real.sqrt_inv, inv_div]

/-- L2 data supply every classical Legendre coefficient (DLMF 18.2(viii)). -/
@[expose] noncomputable def IntegralCoefficientInput.ofLegendreL2
    (f : Lp ℝ 2 legendreMeasure) (n : ℕ) :
    IntegralCoefficientInput ℝ legendreMeasure (legendre ℝ n) :=
  IntegralCoefficientInput.ofL2 hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure (legendre ℝ n)
    (by simpa using ((legendreSequence ℝ).ne_zero n)) f

/-- Legendre expansion coefficients on the full classical product-integrability domain
(DLMF 18.2(viii) and Table 18.3.1). -/
@[expose] noncomputable def legendreCoefficient {n : ℕ}
    (f : IntegralCoefficientInput ℝ legendreMeasure (legendre ℝ n)) : ℝ :=
  ((2 * (n : ℝ) + 1) / 2) * ∫ x, f.val x * (legendre ℝ n).eval x ∂legendreMeasure

/-- The standard coefficient formula on its classical domain (DLMF 18.2(viii)). -/
theorem legendreCoefficient_apply {n : ℕ}
    (f : IntegralCoefficientInput ℝ legendreMeasure (legendre ℝ n)) :
    legendreCoefficient f = ((2 * (n : ℝ) + 1) / 2) *
      ∫ x, f.val x * (legendre ℝ n).eval x ∂legendreMeasure := rfl

/-- Hilbert-coordinate summands are the standard Legendre expansion terms
(DLMF 18.2(viii)). -/
theorem hilbertBasisLegendre_repr_smul (f : Lp ℝ 2 legendreMeasure) (n : ℕ) :
    hilbertBasisLegendre.repr f n • hilbertBasisLegendre n =
      legendreCoefficient (IntegralCoefficientInput.ofLegendreL2 f n) • polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n) := by
  rw [HilbertBasis.repr_apply_apply, hilbertBasisLegendre_apply, normalizedLegendre,
    inner_smul_left, inner_polynomialToL2_left]
  simp only [conj_trivial, smul_smul]
  congr 1
  have hp : 0 ≤ 2 / (2 * (n : ℝ) + 1) := by positivity
  calc
    _ = ((√(2 / (2 * (n : ℝ) + 1)))⁻¹ * (√(2 / (2 * (n : ℝ) + 1)))⁻¹) *
        (∫ x, f x * (legendre ℝ n).eval x ∂legendreMeasure) := by ring
    _ = _ := by rw [← mul_inv, Real.mul_self_sqrt hp, inv_div]; rfl

/-- Every unit-weight L² function is the L² sum of its Legendre expansion
(DLMF 18.2(viii)). -/
theorem hasSum_legendreCoefficient_polynomialToL2 (f : Lp ℝ 2 legendreMeasure) :
    HasSum (fun n : ℕ ↦ legendreCoefficient (IntegralCoefficientInput.ofLegendreL2 f n) •
      polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n)) f := by
  simpa only [hilbertBasisLegendre_repr_smul] using hilbertBasisLegendre.hasSum_repr f

/-- Natural-order Legendre partial sums converge in L² (DLMF 18.2(viii)). -/
theorem tendsto_sum_legendreCoefficient_polynomialToL2 (f : Lp ℝ 2 legendreMeasure) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, legendreCoefficient (IntegralCoefficientInput.ofLegendreL2 f n) •
      polynomialToL2 hasFiniteMoments_legendreMeasure (legendre ℝ n)) atTop (nhds f) :=
  (hasSum_legendreCoefficient_polynomialToL2 f).tendsto_sum_nat

end Polynomial
