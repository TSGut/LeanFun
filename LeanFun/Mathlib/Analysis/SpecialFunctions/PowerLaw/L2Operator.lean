/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.KernelDomain
public import LeanFun.Mathlib.Analysis.IntegralEq.Schur
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClosedInterval
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerKernel
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Completeness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.SingularMass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalSingularMass



/-! # Bounded power-law operators on a common Gegenbauer L² space

The positive symmetric kernel has two equal marginal mass bounds. Schur's test
therefore gives a bounded operator, without polynomial compatibility.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology NNReal
namespace Real
structure PowerLawL2Data (α lam : ℝ) where
  exponent_mem : -1 < α
  weight_mem : -(1/2) < lam
  bound : ℝ≥0
  mass_le : ∀ x : Ioo (-1 : ℝ) 1,
    powerLawIntegral (.gegenbauerWeight ⟨α,exponent_mem⟩ ⟨lam,weight_mem⟩ x) ≤ bound






theorem PowerLawL2Data.kernel_marginals {α lam : ℝ} (p : PowerLawL2Data α lam) :
    (powerLawKernelMeasure α lam).map Prod.fst ≤ ENNReal.ofReal p.bound • gegenbauerMeasure lam ∧
    (powerLawKernelMeasure α lam).map Prod.snd ≤ ENNReal.ofReal p.bound • gegenbauerMeasure lam := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α
  have hk : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (w z : ℝ≥0∞)) := hμ lam lam
  constructor
  · rw [hk,map_fst_withDensity_prod _ _ _ hw.coe_nnreal_ennreal,← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam] with x hx
    rw [lintegral_safePowerLawKernel_row ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ ⟨x,hx⟩ w he]
    exact ENNReal.ofReal_le_ofReal (p.mass_le ⟨x,hx⟩)
  · rw [hk,map_snd_withDensity_prod _ _ _ hw.coe_nnreal_ennreal,← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam] with x hx
    have ht (z : PowerLawKernelDomain) :
        ((fun q : ℝ × ℝ ↦ w (q.2,q.1)) z.val : ℝ) = |z.val.1-z.val.2|^α := by
      rw [he ⟨(z.val.2,z.val.1),z.property.2.1,z.property.1,z.property.2.2.symm⟩,
        abs_sub_comm]
    rw [lintegral_safePowerLawKernel_row ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ ⟨x,hx⟩
      (fun q ↦ w (q.2,q.1)) ht]
    exact ENNReal.ofReal_le_ofReal (p.mass_le ⟨x,hx⟩)

/-- The power-law operator on the same weighted L² space for input and output. -/
def powerLawL2Operator {α lam : ℝ} (p : PowerLawL2Data α lam) :
    Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam) :=
  schurL2Operator _ _ (powerLawKernelMeasure α lam) (by simp) (by simp)
    p.kernel_marginals.1
    p.kernel_marginals.2







theorem norm_powerLawL2Operator_leOn {α lam : ℝ} (p : PowerLawL2Data α lam) :
    ‖powerLawL2Operator p‖ ≤ (p.bound : ℝ) := by
  apply (norm_schurL2Operator_le _ _ _ _ _ _ _).trans_eq
  erw [ENNReal.toReal_ofReal p.bound.property, Real.mul_self_sqrt p.bound.property]
  rfl

theorem powerLawL2Operator_spec {α lam : ℝ} (p : PowerLawL2Data α lam)
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
    ⟪g,powerLawL2Operator p f⟫_ℝ =
      ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam := by
  constructor
  · exact integrable_schurL2_pair _ _ (powerLawKernelMeasure α lam) (by simp) (by simp)
      p.kernel_marginals.1
      p.kernel_marginals.2 f g
  · exact inner_schurL2Operator _ _ (powerLawKernelMeasure α lam) (by simp) (by simp)
      p.kernel_marginals.1
      p.kernel_marginals.2 f g
end Real
namespace Real


theorem powerLawKernelMeasure_fst_leOn {α lam : ℝ} (p : PowerLawL2Data α lam) :
    (powerLawKernelMeasure α lam).map Prod.fst ≤ ENNReal.ofReal p.bound • gegenbauerMeasure lam :=
  p.kernel_marginals.1

theorem powerLawKernelMeasure_snd_leOn {α lam : ℝ} (p : PowerLawL2Data α lam) :
    (powerLawKernelMeasure α lam).map Prod.snd ≤ ENNReal.ofReal p.bound • gegenbauerMeasure lam :=
  p.kernel_marginals.2

theorem powerLawL2Operator_eqOn {α lam : ℝ} (p q : PowerLawL2Data α lam) :
    powerLawL2Operator p = powerLawL2Operator q := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [(powerLawL2Operator_spec p f g).2,(powerLawL2Operator_spec q f g).2]


theorem tendsto_powerLawL2Operator_gegenbauer_sumsOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hzero : lam ≠ 0) (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Tendsto (fun N : ℕ ↦ powerLawL2Operator p
      (∑ n ∈ Finset.range N, (gegenbauerCoefficient lam
        (IntegralCoefficientInput.ofGegenbauerL2 p.weight_mem hzero f n)) •
        polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem) (gegenbauer lam n)))
      atTop (𝓝 (powerLawL2Operator p f)) :=
  (powerLawL2Operator p).continuous.tendsto _ |>.comp
    (tendsto_sum_gegenbauerCoefficient_polynomialToL2 p.weight_mem hzero f)

theorem exists_powerLawL2Data (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (hregime : 0 ≤ α.val ∨ 1/2 ≤ lam.val) :
    ∃ p : PowerLawL2Data α.val lam.val, 0 < (p.bound : ℝ) := by
  have hs : -(1/2) < α.val+lam.val := by
    rcases hregime with ha | hl
    · have h : -(1/2 : ℝ) < lam.val := lam.property
      linarith
    · have h : (-1 : ℝ) < α.val := α.property
      linarith
  let q : PowerLawClosedParameters := ⟨(α.val,lam.val),α.property,lam.property,hs⟩
  obtain ⟨M,hM,hb⟩ := exists_powerLawIntegral_weightedMassClosed_bound q hregime
  refine ⟨⟨α.property,lam.property,⟨M,hM.le⟩,fun x ↦ ?_⟩,hM⟩
  convert hb ⟨x.val,Ioo_subset_Icc_self x.property⟩ using 1
  congr 1
  apply Subtype.ext
  funext y
  simp only [PowerLawInput.gegenbauerWeight_apply,PowerLawInput.gegenbauerWeightClosed_apply]
  rfl
  all_goals rfl

end Real
namespace Real

theorem exists_powerLawL2Data_of_endpoint (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (hs : -(1/2) < α.val+lam.val) :
    ∃ p : PowerLawL2Data α.val lam.val, 0 < (p.bound : ℝ) := by
  let q : PowerLawClosedParameters := ⟨(α.val,lam.val),α.property,lam.property,hs⟩
  obtain ⟨M,hM,hb⟩ := exists_powerLawIntegral_weightedMassClosed_bound_of_endpoint q
  refine ⟨⟨α.property,lam.property,⟨M,hM.le⟩,fun x ↦ ?_⟩,hM⟩
  convert hb ⟨x.val,Ioo_subset_Icc_self x.property⟩ using 1
  congr 1
  apply Subtype.ext
  funext y
  simp only [PowerLawInput.gegenbauerWeight_apply,PowerLawInput.gegenbauerWeightClosed_apply]
  rfl
  all_goals rfl

end Real
namespace Real


end Real
namespace Real

end Real
namespace Real
theorem powerLawL2Operator_hasPowerLawIntegral {α lam : ℝ} (p : PowerLawL2Data α lam)
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ∃ F : IntegrableInput (gegenbauerMeasure lam),
      (∀ᵐ x ∂gegenbauerMeasure lam, ∃ I : PowerLawInput α x,
        (∀ y : PowerLawDomain x, I.val y =
          g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) ∧
        F.val x = powerLawIntegral I) ∧
      ⟪g,powerLawL2Operator p f⟫_ℝ = ∫ x, F.val x ∂gegenbauerMeasure lam := by
  obtain ⟨F,hF,he⟩ := powerLawWeakFubini f g (powerLawL2Operator_spec p f g).1
  exact ⟨F,hF,(powerLawL2Operator_spec p f g).2.trans he.symm⟩

theorem lintegral_powerLaw_gegenbauerMeasureOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    (∫⁻ y : PowerLawDomain x.val, ENNReal.ofReal (|x.val-y.val|^α.val)
      ∂Measure.comap Subtype.val (gegenbauerMeasure lam.val)) =
      ENNReal.ofReal (powerLawIntegral (.gegenbauerWeight α lam x)) := by
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α.val
  let : NullSingletonClass (gegenbauerMeasure lam.val) := nullSingletonClass_gegenbauerMeasure _
  have hm := measurableSet_powerLawDomain x.val
  have hae : ∀ᵐ y ∂gegenbauerMeasure lam.val, y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val :=
    (ae_mem_Ioo_gegenbauerMeasure lam.val).and ((gegenbauerMeasure lam.val).ae_ne x.val)
  have ht := lintegral_subtype_comap (μ := gegenbauerMeasure lam.val) hm
    (fun y : ℝ ↦ (w (x.val,y) : ℝ≥0∞))
  erw [Measure.restrict_eq_self_of_ae_mem hae] at ht
  calc
    _ = ∫⁻ y : PowerLawDomain x.val, (w (x.val,y.val) : ℝ≥0∞)
        ∂Measure.comap Subtype.val (gegenbauerMeasure lam.val) := by
      apply lintegral_congr
      intro y
      have hh := he ⟨(x.val,y.val),x.property,y.property.1,y.property.2.symm⟩
      rw [← hh,ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ y, (w (x.val,y) : ℝ≥0∞) ∂gegenbauerMeasure lam.val := ht
    _ = _ := lintegral_safePowerLawKernel_row α lam x w he

end Real

namespace Real
theorem powerLawL2Operator_polynomial_compatibleOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hzero : lam ≠ 0) {k : ℕ} (hk : lam+α/2 = k) (q : ℝ[X]) :
    powerLawL2Operator p (polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem) q) =
      polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem)
        (powerLawGegenbauerOperator (.ofIntegrable ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ hzero) k q) := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  let f := polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem) q
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α
  have hprod : ∀ᵐ z ∂(gegenbauerMeasure lam).prod (gegenbauerMeasure lam), f z.2 = q.eval z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := gegenbauerMeasure lam)
      (ν := gegenbauerMeasure lam)).ae (coe_polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem) q)
  have hpair : ∀ᵐ z ∂powerLawKernelMeasure α lam, f z.2 = q.eval z.2 := by
    change ∀ᵐ z ∂twoWeightPowerLawKernelMeasure α lam lam, f z.2 = q.eval z.2
    rw [hμ lam lam]
    exact Measure.AbsolutelyContinuous.ae_eq (withDensity_absolutelyContinuous _ _) hprod
  apply ext_inner_left ℝ
  intro g
  have hi : Integrable (fun z : ℝ × ℝ ↦ g z.1*q.eval z.2) (powerLawKernelMeasure α lam) := by
    apply (powerLawL2Operator_spec p f g).1.congr
    filter_upwards [hpair] with z hz
    rw [hz]
  obtain ⟨F,hF,hI⟩ := powerLawWeakFubini (fun y ↦ q.eval y) g hi
  rw [(powerLawL2Operator_spec p f g).2,L2.inner_def]
  calc
    _ = ∫ z : ℝ × ℝ, g z.1*q.eval z.2 ∂powerLawKernelMeasure α lam := by
      apply integral_congr_ae
      filter_upwards [hpair] with z hz
      rw [hz]
    _ = ∫ x, F.val x ∂gegenbauerMeasure lam := hI.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam,hF,
        coe_polynomialToL2 (hasFiniteMoments_gegenbauerMeasure p.weight_mem)
          (powerLawGegenbauerOperator (.ofIntegrable ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ hzero) k q)] with x hx hF hq
      obtain ⟨I,hval,hFI⟩ := hF
      rw [hFI,Real.inner_apply,hq,
        eval_powerLawGegenbauerOperator ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ hzero hk ⟨x,hx⟩ q,
        powerLawPolynomial_apply]
      unfold powerLawIntegral
      erw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hval y,PowerLawInput.gegenbauerPolynomial_apply]
      ring
end Real
