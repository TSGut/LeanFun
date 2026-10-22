/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space

import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Algebra.Polynomial

/-!
# Completeness of first-kind Chebyshev polynomials

Polynomial density follows from Weierstrass approximation and density of bounded
continuous functions in the weighted L² space. References: ATAP, Chapters 1 and 3;
DLMF Table 18.3.1.
-/

public section

namespace Polynomial.Chebyshev

open Real MeasureTheory Filter
open scoped ENNReal InnerProductSpace

/-- The first-kind weight is finite (DLMF Table 18.3.1). -/
instance isFiniteMeasure_measureT : IsFiniteMeasure classicalMeasureT :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (integrable_classicalMeasureT (f := fun _ ↦ 1) (by fun_prop))

/-- The Chebyshev weight is supported on the approximation interval (DLMF Table 18.3.1). -/
theorem ae_mem_Icc_measureT : ∀ᵐ x ∂classicalMeasureT, x ∈ Set.Icc (-1) 1 := by
  let : IsFiniteMeasure measureT := by
    simpa only [classicalMeasureT_eq] using isFiniteMeasure_measureT
  rw [classicalMeasureT_eq, ae_iff]
  change measureT (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  rw [← measureReal_eq_zero_iff]
  rw [← integral_indicator_one measurableSet_Icc.compl, integral_measureT_eq_integral_cos]
  have hcos (θ : ℝ) : cos θ ∉ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    simpa only [Set.mem_compl_iff, not_not, Set.mem_Icc] using And.intro (neg_one_le_cos θ) (cos_le_one θ)
  simp only [Set.indicator_of_notMem (hcos _), intervalIntegral.integral_zero]

/-- Polynomials belong to the weighted L² space (DLMF Table 18.3.1). -/
theorem memLp_eval_measureT (p : ℝ[X]) : MemLp (fun x ↦ p.eval x) 2 classicalMeasureT := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact integrable_classicalMeasureT (by fun_prop)

/-- Polynomial evaluation as a linear map to weighted L² (ATAP, Chapters 1 and 3). -/
noncomputable def polynomialToL2 : ℝ[X] →ₗ[ℝ] Lp ℝ 2 classicalMeasureT where
  toFun p := (memLp_eval_measureT p).toLp (fun x ↦ p.eval x)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(memLp_eval_measureT (p + q)).coeFn_toLp,
      (memLp_eval_measureT p).coeFn_toLp, (memLp_eval_measureT q).coeFn_toLp,
      Lp.coeFn_add ((memLp_eval_measureT p).toLp _) ((memLp_eval_measureT q).toLp _)]
      with x hpq hp hq hadd
    rw [hpq, hadd]
    simp only [Pi.add_apply, hp, hq, eval_add]
  map_smul' c p := by
    change (memLp_eval_measureT (c • p)).toLp _ = c • (memLp_eval_measureT p).toLp _
    apply Lp.ext
    filter_upwards [(memLp_eval_measureT (c • p)).coeFn_toLp,
      (memLp_eval_measureT p).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_eval_measureT p).toLp _)] with x hcp hp hsmul
    rw [hcp, hsmul]
    simp only [Pi.smul_apply, hp, eval_smul, smul_eq_mul]

/-- An almost-everywhere representative of polynomial evaluation (ATAP, Chapter 3). -/
theorem coe_polynomialToL2 (p : ℝ[X]) : polynomialToL2 p =ᵐ[classicalMeasureT] fun x ↦ p.eval x :=
  (memLp_eval_measureT p).coeFn_toLp

/-- The polynomial L² inner product is the weighted product integral (DLMF Table 18.3.1). -/
theorem inner_polynomialToL2 (p q : ℝ[X]) :
    ⟪polynomialToL2 p, polynomialToL2 q⟫_ℝ = ∫ x, p.eval x * q.eval x ∂classicalMeasureT := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2 p, coe_polynomialToL2 q] with x hp hq
  simp [hp, hq, mul_comm]

/-- Weierstrass approximation gives dense polynomial classes in weighted L² (ATAP, Chapter 1). -/
theorem polynomialToL2_denseRange : DenseRange polynomialToL2 := by
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ classicalMeasureT ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  apply Dense.of_closure (hd.mono ?_)
  rintro _ ⟨f, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  let K : ℝ := (measureUnivNNReal classicalMeasureT : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hK : 0 ≤ K := by positivity
  let δ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f
    f.continuous.continuousOn δ hδ
  refine ⟨polynomialToL2 p, ⟨p, rfl⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hb : ‖polynomialToL2 p - BoundedContinuousFunction.toLp 2 classicalMeasureT ℝ f‖ ≤ K * δ := by
    apply Lp.norm_le_of_ae_bound hδ.le
    filter_upwards [ae_mem_Icc_measureT, coe_polynomialToL2 p,
      f.coeFn_toLp 2 classicalMeasureT ℝ,
      Lp.coeFn_sub (polynomialToL2 p) (BoundedContinuousFunction.toLp 2 classicalMeasureT ℝ f)]
      with x hx hpx hfx hsub
    rw [hsub]
    simp only [Pi.sub_apply, hpx, hfx, Real.norm_eq_abs]
    exact (hp x hx).le
  apply hb.trans_lt
  dsimp [δ]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0 < K + 1)).mpr
  nlinarith

/-- First-kind squared norms as L² inner products (DLMF Table 18.3.1). -/
theorem inner_polynomialToL2_T (n m : ℕ) :
    ⟪polynomialToL2 (T ℝ n), polynomialToL2 (T ℝ m)⟫_ℝ =
      if n = m then (if n = 0 then π else π / 2) else 0 := by
  rw [inner_polynomialToL2]
  exact (classicalMeasureT_orthogonality n m).2

/-- Normalised first-kind Chebyshev classes (DLMF Table 18.3.1). -/
noncomputable def normalizedT (n : ℕ) : Lp ℝ 2 classicalMeasureT :=
  (√(if n = 0 then π else π / 2))⁻¹ • polynomialToL2 (T ℝ n)

/-- The normalised first-kind family is orthonormal (DLMF Table 18.3.1). -/
theorem orthonormal_normalizedT : Orthonormal ℝ normalizedT := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedT, inner_smul_left, inner_smul_right, conj_trivial,
    inner_polynomialToL2_T]
  by_cases h : n = m
  · subst m
    simp only [↓reduceIte]
    have hp : 0 < (if n = 0 then π else π / 2 : ℝ) := by split_ifs <;> positivity
    have hs := Real.sq_sqrt hp.le
    have hz : √(if n = 0 then π else π / 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    field_simp
    nlinarith [hs]
  · simp [h]

/-- Chebyshev polynomial classes span the polynomial image in L² (ATAP, Chapter 3). -/
theorem span_polynomialToL2_T :
    Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 (T ℝ n))) =
      LinearMap.range polynomialToL2 := by
  have hs : Submodule.span ℝ (Set.range (fun n : ℕ ↦ T ℝ n)) = ⊤ := by
    apply (chebyshevTsequence ℝ).span
    intro n
    apply isUnit_iff_ne_zero.mpr
    exact leadingCoeff_ne_zero.mpr ((chebyshevTsequence ℝ).ne_zero n)
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.map_top]
    using congrArg (Submodule.map polynomialToL2) hs

/-- The normalised Chebyshev family has dense span (ATAP, Chapters 1 and 3). -/
theorem normalizedT_dense_span :
    (Submodule.span ℝ (Set.range normalizedT)).topologicalClosure = ⊤ := by
  have hd : (Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 (T ℝ n)))).topologicalClosure = ⊤ := by
    rw [span_polynomialToL2_T]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp polynomialToL2_denseRange
  have hs : Submodule.span ℝ (Set.range (fun n : ℕ ↦ polynomialToL2 (T ℝ n))) ≤
      Submodule.span ℝ (Set.range normalizedT) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    have hp : 0 < (if n = 0 then π else π / 2 : ℝ) := by split_ifs <;> positivity
    have hz : √(if n = 0 then π else π / 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hm := (Submodule.span ℝ (Set.range normalizedT)).smul_mem
      (√(if n = 0 then π else π / 2)) (Submodule.subset_span (Set.mem_range_self n))
    simpa only [SetLike.mem_coe, normalizedT, smul_smul, mul_inv_cancel₀ hz, one_smul] using hm
  apply top_unique
  rw [← hd]
  exact Submodule.topologicalClosure_mono hs

/-- The Chebyshev Hilbert basis of weighted L² (DLMF Table 18.3.1; ATAP, Chapters 1 and 3). -/
noncomputable def hilbertBasisT : HilbertBasis ℕ ℝ (Lp ℝ 2 classicalMeasureT) :=
  HilbertBasis.mk orthonormal_normalizedT (by rw [normalizedT_dense_span])

/-- The Hilbert basis vectors are the normalised Chebyshev classes (DLMF Table 18.3.1). -/
@[simp] theorem hilbertBasisT_apply (n : ℕ) : hilbertBasisT n = normalizedT n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

/-- The zero-index normalisation (DLMF Table 18.3.1). -/
@[simp] theorem normalizedT_zero :
    normalizedT 0 = (√π)⁻¹ • polynomialToL2 1 := by
  simp [normalizedT]

/-- The positive-index normalisation agrees with `√(2 / π)` (DLMF Table 18.3.1). -/
theorem normalizedT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    normalizedT n = √(2 / π) • polynomialToL2 (T ℝ n) := by
  simp only [normalizedT, hn, ↓reduceIte, ← Real.sqrt_inv, inv_div]

/-- Polynomial inner products with arbitrary L² classes (DLMF Table 18.3.1). -/
theorem inner_polynomialToL2_left (p : ℝ[X]) (f : Lp ℝ 2 classicalMeasureT) :
    ⟪polynomialToL2 p, f⟫_ℝ = ∫ x, f x * p.eval x ∂classicalMeasureT := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2 p] with x hp
  simp [hp]

/-- L² inputs have an integrable coefficient integrand at every index. -/
theorem coefficientInput_integrable_L2 (f : Lp ℝ 2 classicalMeasureT) (n : ℕ) :
    Integrable (fun x ↦ f x * (T ℝ n).eval x) classicalMeasureT := by
  have hf : Integrable (fun x ↦ f x) classicalMeasureT :=
    MemLp.integrable (by norm_num) (Lp.memLp f)
  apply integrable_classicalMeasureT_mul_T ⟨_, ?_⟩ n
  exact hf

/-- Hilbert-basis summands use the full-constant-term Chebyshev coefficients
(ATAP, Chapter 3; DLMF Table 18.3.1). -/
theorem hilbertBasisT_repr_smul (f : Lp ℝ 2 classicalMeasureT) (n : ℕ) :
    hilbertBasisT.repr f n • hilbertBasisT n = (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f n⟩) • polynomialToL2 (T ℝ n) := by
  rw [HilbertBasis.repr_apply_apply, hilbertBasisT_apply, normalizedT,
    inner_smul_left, inner_polynomialToL2_left]
  simp only [conj_trivial, smul_smul]
  congr 1
  have hp : 0 < (if n = 0 then π else π / 2 : ℝ) := by split_ifs <;> positivity
  calc
    _ = ((√(if n = 0 then π else π / 2))⁻¹ * (√(if n = 0 then π else π / 2))⁻¹) *
        (∫ x, f x * (T ℝ n).eval x ∂classicalMeasureT) := by ring
    _ = (if n = 0 then π else π / 2)⁻¹ * (∫ x, f x * (T ℝ n).eval x ∂classicalMeasureT) := by
      rw [← mul_inv, Real.mul_self_sqrt hp.le]
    _ = (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f n⟩) := by
      by_cases hn : n = 0
      · subst n
        simp only [↓reduceIte, Nat.cast_zero, T_zero, eval_one, mul_one, coefficient]
        ring
      · simp only [coefficient, hn, ↓reduceIte, inv_div]

/-- Every weighted L² function is the sum of its Chebyshev expansion in L²
(DLMF 18.2(viii); ATAP, Chapter 3). -/
theorem hasSum_coefficient_polynomialToL2 (f : Lp ℝ 2 classicalMeasureT) :
    HasSum (fun n : ℕ ↦ (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f n⟩) • polynomialToL2 (T ℝ n)) f := by
  simpa only [hilbertBasisT_repr_smul] using hilbertBasisT.hasSum_repr f

/-- Natural-order Chebyshev partial sums converge in weighted L²
(DLMF 18.2(viii); ATAP, Chapter 3). -/
theorem tendsto_sum_coefficient_polynomialToL2 (f : Lp ℝ 2 classicalMeasureT) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f n⟩) • polynomialToL2 (T ℝ n))
      atTop (nhds f) :=
  (hasSum_coefficient_polynomialToL2 f).tendsto_sum_nat

/-- The weighted L² norm of the Chebyshev truncation error tends to zero
(DLMF 18.2(viii); ATAP, Chapter 3). -/
theorem tendsto_norm_sub_sum_coefficient_polynomialToL2 (f : Lp ℝ 2 classicalMeasureT) :
    Tendsto (fun N : ℕ ↦ ‖f - ∑ n ∈ Finset.range N, (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f n⟩) • polynomialToL2 (T ℝ n)‖)
      atTop (nhds 0) := by
  simpa only [sub_self, norm_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f) atTop (nhds f)).sub
      (tendsto_sum_coefficient_polynomialToL2 f)).norm

end Polynomial.Chebyshev
