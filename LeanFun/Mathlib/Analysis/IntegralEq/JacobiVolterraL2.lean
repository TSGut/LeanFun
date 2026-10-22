/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.MarginalKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiVolterraMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCompleteness
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousVolterraPrimitive
public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiLocalIntegrability
/-! # Weighted reflected Volterra operators in raw Jacobi function space

The operator is represented by the scaled reflected triangle. Its weak pairing
retains the endpoint factor: on polynomial inputs the output is the reflected
Volterra integral divided by 1-s. Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

open MeasureTheory Polynomial Set
open scoped ENNReal InnerProductSpace
@[expose] public noncomputable section
namespace Real
/-- Weighted Jacobi L² data supply each row strictly before the vanishing endpoint. -/
def VolterraIntegralInput.ofJacobiOneZeroLp
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    (f : Lp ℝ 2 (unitJacobiMeasure 1 0)) (x : Ico (0 : ℝ) 1) :
    VolterraIntegralInput (x : ℝ) :=
  .ofContinuousKernel hK (f := fun y ↦ f y) ⟨x, x.property.1, x.property.2.le⟩ (by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le x.property.1]
    exact (integrableOn_coe_jacobiOneZeroLp f x.property.2).mono_set Ioc_subset_Icc_self)
end Real
namespace MvPolynomial
local notation "μ" => unitJacobiMeasure 1 0
local notation "κ" => Real.jacobiVolterraJoint
variable (K : MvPolynomial (Fin 2) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M)
include hb in
/-- A bound on the physical triangle bounds the reflected joint kernel. -/
theorem ae_norm_reflectedVolterraKernel_le :
    ∀ᵐ z ∂κ, ‖eval (![1-z.1,z.2] : Fin 2 → ℝ) K‖ ≤ M := by
  filter_upwards [Real.ae_mem_jacobiVolterraJoint] with z hz
  apply hb
  change (1-z.1) ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc 0 (1-z.1)
  exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩,
    ⟨hz.2.1.1, by linarith [hz.2.2]⟩⟩
/-- The averaged, reflected Volterra operator on the shifted Jacobi L² space. -/
def jacobiVolterraL2Operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  marginalKernelL2Operator μ μ κ Real.map_fst_jacobiVolterraJoint
    Real.map_snd_jacobiVolterraJoint (fun z ↦ eval ![1-z.1,z.2] K)
    (K.continuous_eval.comp (by fun_prop)).aestronglyMeasurable hM
    (ae_norm_reflectedVolterraKernel_le K hb)
/-- The physical kernel bound controls the weighted operator norm. -/
theorem norm_jacobiVolterraL2Operator_le : ‖jacobiVolterraL2Operator K hM hb‖ ≤ M :=
  norm_marginalKernelL2Operator_le ..
/-- The weak physical integral formula, including the shifted-measure factor four. -/
theorem inner_jacobiVolterraL2Operator (f g : Lp ℝ 2 μ) :
    ⟪g, jacobiVolterraL2Operator K hM hb f⟫_ℝ =
      4 * ∫ s : Ioo (0 : ℝ) 1, g s * Real.volterraIntegral
        (.ofJacobiOneZeroLp K.continuous_eval.continuousOn f
          ⟨1-(s : ℝ), by constructor <;> linarith [s.property.1, s.property.2]⟩)
        ∂(volume : Measure ℝ).comap Subtype.val := by
  simp only [Real.VolterraIntegralInput.ofJacobiOneZeroLp,
    Real.VolterraIntegralInput.ofContinuousKernel, Real.volterraIntegral_ofKernel]
  rw [integral_subtype_comap measurableSet_Ioo
    (fun s : ℝ ↦ g s * ∫ y in (0 : ℝ)..(1-s), eval ![1-s,y] K * f y),
    ← integral_Icc_eq_integral_Ioo]
  have hi : Integrable (fun z : ℝ × ℝ ↦ eval ![1-z.1,z.2] K * (g z.1*f z.2)) κ :=
    integrable_marginalKernelL2_pair μ μ κ Real.map_fst_jacobiVolterraJoint
      Real.map_snd_jacobiVolterraJoint _
      (K.continuous_eval.comp (by fun_prop)).aestronglyMeasurable hM
      (ae_norm_reflectedVolterraKernel_le K hb) f g
  rw [jacobiVolterraL2Operator, inner_marginalKernelL2Operator,
    Real.integral_jacobiVolterraJoint _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  ring
end MvPolynomial
namespace MvPolynomial
local notation "μ" => unitJacobiMeasure 1 0
local notation "κ" => Real.jacobiVolterraJoint
local notation "hm" => hasFiniteMoments_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 1)
  (by norm_num : (-1 : ℝ) < 0)
/-- A polynomial identity with the endpoint factor identifies the weighted L² output. -/
theorem jacobiVolterraL2Operator_polynomial (K : MvPolynomial (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M)
    (p q : ℝ[X])
    (hq : ∀ x ∈ Icc (0 : ℝ) 1,
      Real.volterraIntegral (.ofPolynomial K p.continuous.locallyIntegrable x) =
        x*q.eval (1-x)) :
    jacobiVolterraL2Operator K hM hb (polynomialToL2 hm p) = polynomialToL2 hm q := by
  apply ext_inner_left ℝ
  intro g
  have hp : ∀ᵐ z ∂κ, polynomialToL2 hm p z.2 = p.eval z.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (by
      rw [Real.map_snd_jacobiVolterraJoint]
      exact coe_polynomialToL2 hm p)
  have he : (fun z : ℝ × ℝ ↦ eval ![1-z.1,z.2] K * (g z.1 * polynomialToL2 hm p z.2)) =ᵐ[κ]
      (fun z ↦ eval ![1-z.1,z.2] K * (g z.1*p.eval z.2)) := by
    filter_upwards [hp] with z hz
    rw [hz]
  have hi := (integrable_marginalKernelL2_pair μ μ κ Real.map_fst_jacobiVolterraJoint
    Real.map_snd_jacobiVolterraJoint _
    (K.continuous_eval.comp (by fun_prop)).aestronglyMeasurable hM
    (ae_norm_reflectedVolterraKernel_le K hb) (polynomialToL2 hm p) g).congr he
  have hr : ⟪g, polynomialToL2 hm q⟫_ℝ =
      4 * ∫ s in Icc (0 : ℝ) 1, (1-s)*(q.eval s*g s) := by
    rw [L2.inner_def]
    trans ∫ s, q.eval s*g s ∂μ
    · apply integral_congr_ae
      filter_upwards [coe_polynomialToL2 hm q] with s hs
      simp only [Real.inner_apply, hs]
      ring
    · apply integral_unitJacobiMeasure_one_zero ⟨_, ?_⟩
      exact (L2.integrable_inner (𝕜 := ℝ) g (polynomialToL2 hm q)).congr (by
        filter_upwards [coe_polynomialToL2 hm q] with s hs
        simp only [Real.inner_apply, hs, mul_comm])
  rw [jacobiVolterraL2Operator, inner_marginalKernelL2Operator,
    integral_congr_ae he, Real.integral_jacobiVolterraJoint _ hi, hr]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hq' := hq (1-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩
  simp only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel,
    sub_sub_cancel] at hq'
  simp_rw [show ∀ y, eval (![1-s,y] : Fin 2 → ℝ) K * (g s*p.eval y) =
    g s*(eval ![1-s,y] K*p.eval y) by intro y; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [hq']
  ring
end MvPolynomial
