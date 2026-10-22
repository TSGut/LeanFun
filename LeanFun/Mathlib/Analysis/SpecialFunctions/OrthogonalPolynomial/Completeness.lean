/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Polynomial density in L² for compactly supported measures

Only the density theorem assumes support in a bounded interval. The polynomial
map applies to any measure with finite polynomial moments. References: DLMF
18.2(viii); Weierstrass approximation and density of bounded continuous functions.
-/
public section
namespace Polynomial
open Real MeasureTheory Filter
open scoped ENNReal InnerProductSpace
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
include hμ

/-- Finite polynomial moments put every polynomial in L² (DLMF 18.2(viii)). -/
theorem memLp_eval_of_hasFiniteMoments (p : ℝ[X]) : MemLp (fun x ↦ p.eval x) 2 μ := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).mpr (hμ p)

/-- Polynomial evaluation as a linear map to weighted L² (DLMF 18.2(viii)). -/
noncomputable def polynomialToL2 : ℝ[X] →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (memLp_eval_of_hasFiniteMoments hμ p).toLp (fun x ↦ p.eval x)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(memLp_eval_of_hasFiniteMoments hμ (p + q)).coeFn_toLp,
      (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp, (memLp_eval_of_hasFiniteMoments hμ q).coeFn_toLp,
      Lp.coeFn_add ((memLp_eval_of_hasFiniteMoments hμ p).toLp _) ((memLp_eval_of_hasFiniteMoments hμ q).toLp _)]
      with x hpq hp hq hadd
    rw [hpq, hadd]
    simp only [Pi.add_apply, hp, hq, eval_add]
  map_smul' c p := by
    change (memLp_eval_of_hasFiniteMoments hμ (c • p)).toLp _ = c • (memLp_eval_of_hasFiniteMoments hμ p).toLp _
    apply Lp.ext
    filter_upwards [(memLp_eval_of_hasFiniteMoments hμ (c • p)).coeFn_toLp,
      (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_eval_of_hasFiniteMoments hμ p).toLp _)] with x hcp hp hsmul
    rw [hcp, hsmul]
    simp only [Pi.smul_apply, hp, eval_smul, smul_eq_mul]

/-- An almost-everywhere representative of polynomial evaluation (DLMF 18.2(viii)). -/
theorem coe_polynomialToL2 (p : ℝ[X]) : polynomialToL2 hμ p =ᵐ[μ] fun x ↦ p.eval x :=
  (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp

/-- The polynomial L² inner product is the weighted product integral (DLMF Table 18.3.1). -/
theorem inner_polynomialToL2 (p q : ℝ[X]) :
    ⟪polynomialToL2 hμ p, polynomialToL2 hμ q⟫_ℝ = ∫ x, p.eval x * q.eval x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2 hμ p, coe_polynomialToL2 hμ q] with x hp hq
  simp [hp, hq, mul_comm]

/-- Weierstrass approximation gives dense polynomial classes in weighted L² (ATAP, Chapter 1). -/
theorem polynomialToL2_denseRange (a b : ℝ)
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : DenseRange (polynomialToL2 hμ) := by
  let _ := hμ.isFiniteMeasure
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  apply Dense.of_closure (hd.mono ?_)
  rintro _ ⟨f, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  let K : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hK : 0 ≤ K := by positivity
  let δ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f
    f.continuous.continuousOn δ hδ
  refine ⟨polynomialToL2 hμ p, ⟨p, rfl⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hb : ‖polynomialToL2 hμ p - BoundedContinuousFunction.toLp 2 μ ℝ f‖ ≤ K * δ := by
    apply Lp.norm_le_of_ae_bound hδ.le
    filter_upwards [hsupp, coe_polynomialToL2 hμ p,
      f.coeFn_toLp 2 μ ℝ,
      Lp.coeFn_sub (polynomialToL2 hμ p) (BoundedContinuousFunction.toLp 2 μ ℝ f)]
      with x hx hpx hfx hsub
    rw [hsub]
    simp only [Pi.sub_apply, hpx, hfx, Real.norm_eq_abs]
    exact (hp x hx).le
  apply hb.trans_lt
  dsimp [δ]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0 < K + 1)).mpr
  nlinarith

/-- Polynomial inner products with arbitrary L² functions (DLMF 18.2(viii)). -/
theorem inner_polynomialToL2_left (p : ℝ[X]) (f : Lp ℝ 2 μ) :
    ⟪polynomialToL2 hμ p, f⟫_ℝ = ∫ x, f x * p.eval x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2 hμ p] with x hp
  simp [hp]

end Polynomial
