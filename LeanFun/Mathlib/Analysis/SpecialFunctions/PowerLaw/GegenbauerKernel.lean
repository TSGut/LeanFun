/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerOperator
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.KernelDomain

/-! # Absolute integrability of compatible power-law kernels

The terminating zeroth-mode formula supplies the integrable majorant needed for
Fubini. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public section
open Polynomial Set MeasureTheory Filter
open scoped ENNReal NNReal
namespace Real



end Real

namespace Real
attribute [local instance] Measure.Subtype.measureSpace
theorem lintegral_safePowerLawKernel_row (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (w : ℝ × ℝ → ℝ≥0)
    (he : ∀ z : PowerLawKernelDomain, (w z.val : ℝ) = |z.val.1-z.val.2|^α.val) :
    (∫⁻ y, (w (x.val,y) : ℝ≥0∞) ∂gegenbauerMeasure lam.val) =
      ENNReal.ofReal (powerLawIntegral (.gegenbauerWeight α lam x)) := by
  obtain ⟨F,hF,hFI,hFV⟩ := PowerLawInput.exists_weightedIntervalRepresentative
    (PowerLawInput.gegenbauerWeight α lam x)
  have hiF := (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume) measurableSet_Ioo).mp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (f := F) (by norm_num : (-1 : ℝ) ≤ 1)).mp hFI)
  have hn : ∀ᵐ y : Ioo (-1 : ℝ) 1, y.val ≠ x.val := by
    change ∀ᵐ y ∂Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) (volume : Measure ℝ), y.val ≠ x.val
    exact (ae_restrict_iff_subtype (μ := (volume : Measure ℝ))
      (s := Ioo (-1 : ℝ) 1) (p := fun y : ℝ ↦ y ≠ x.val) measurableSet_Ioo).mp
      (ae_restrict_of_ae (volume.ae_ne x.val))
  have hrow : (fun y : Ioo (-1 : ℝ) 1 ↦
      (gegenbauerWeight lam.val y : ℝ)*(w (x.val,y.val) : ℝ)) =ᵐ[volume]
      (fun y ↦ F y.val) := by
    filter_upwards [hn] with y hy
    have hw := he ⟨(x.val,y.val),x.property,y.property,hy.symm⟩
    rw [hw,hF ⟨y.val,y.property,hy⟩,PowerLawInput.gegenbauerWeight_apply]
    ring
  have hi : Integrable (fun y : ℝ ↦ (w (x.val,y) : ℝ)) (gegenbauerMeasure lam.val) := by
    apply (integrable_gegenbauerMeasure_iff lam.val _).mpr
    exact hiF.congr hrow.symm
  have hv : (∫ y, (w (x.val,y) : ℝ) ∂gegenbauerMeasure lam.val) =
      powerLawIntegral (.gegenbauerWeight α lam x) := by
    calc
      _ = ∫ y : Ioo (-1 : ℝ) 1,
          (gegenbauerWeight lam.val y : ℝ)*(w (x.val,y.val) : ℝ) :=
        integral_gegenbauerMeasure lam.val ⟨(fun y ↦ (w (x.val,y) : ℝ)),hi⟩
      _ = ∫ y : Ioo (-1 : ℝ) 1, F y.val := integral_congr_ae hrow
      _ = ∫ y in Ioo (-1 : ℝ) 1, F y := integral_subtype_comap measurableSet_Ioo F
      _ = ∫ y in (-1 : ℝ)..1, F y := by
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
      _ = _ := hFV.symm
  have h := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun y ↦ (w (x.val,y)).coe_nonneg))
  rw [hv] at h
  simpa only [ENNReal.ofReal_coe_nnreal] using h.symm
end Real

namespace MeasureTheory
private theorem exists_integrable_rows {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (k : X × Y → ℝ) (hi : Integrable k (μ.prod ν)) :
    ∃ K : X × Y → ℝ, Integrable K (μ.prod ν) ∧
      (∀ x, Integrable (fun y ↦ K (x,y)) ν) ∧
      K =ᵐ[μ.prod ν] k ∧
      (∀ᵐ x ∂μ, ∀ y, K (x,y) = k (x,y)) := by
  classical
  let K : X × Y → ℝ := fun z ↦ if Integrable (fun y ↦ k (z.1,y)) ν then k z else 0
  have hrow : ∀ᵐ x ∂μ, ∀ y, K (x,y) = k (x,y) := by
    filter_upwards [hi.prod_right_ae] with x hx
    intro y
    simp only [K,ite_eq_left hx]
  have he : K =ᵐ[μ.prod ν] k := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hrow] with z hz
    exact hz z.2
  refine ⟨K,hi.congr he.symm,?_,he,hrow⟩
  intro x
  by_cases hx : Integrable (fun y ↦ k (x,y)) ν
  · simpa only [K,ite_eq_left hx] using hx
  · have hzero : (fun y ↦ K (x,y)) = (0 : Y → ℝ) := by
      funext y
      simp only [K,ite_eq_right hx,Pi.zero_apply]
    rw [hzero]
    exact integrable_zero Y ℝ ν
end MeasureTheory
namespace Real
attribute [local instance] Measure.Subtype.measureSpace
theorem twoWeightPowerLawWeakFubini {α lam tau : ℝ}
    (f g : ℝ → ℝ)
    (hi : Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (twoWeightPowerLawKernelMeasure α tau lam)) :
    ∃ F : IntegrableInput (gegenbauerMeasure tau),
      (∀ᵐ x ∂gegenbauerMeasure tau, ∃ I : PowerLawInput α x,
        (∀ y : PowerLawDomain x, I.val y =
          g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) ∧
        F.val x = powerLawIntegral I) ∧
      (∫ x, F.val x ∂gegenbauerMeasure tau) =
        ∫ z : ℝ × ℝ, g z.1*f z.2 ∂twoWeightPowerLawKernelMeasure α tau lam := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  let : SFinite (gegenbauerMeasure tau) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α
  have hk : twoWeightPowerLawKernelMeasure α tau lam =
      ((gegenbauerMeasure tau).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (w z : ℝ≥0∞)) := hμ tau lam
  have hiw : Integrable (fun z : ℝ × ℝ ↦ (w z : ℝ)*(g z.1*f z.2))
      ((gegenbauerMeasure tau).prod (gegenbauerMeasure lam)) := by
    rw [hk,integrable_withDensity_iff hw.coe_nnreal_ennreal (by simp)] at hi
    simpa only [ENNReal.coe_toReal,smul_eq_mul,mul_comm] using hi
  obtain ⟨K,hKI,hKr,hKe,hKrow⟩ := MeasureTheory.exists_integrable_rows
    (gegenbauerMeasure tau) (gegenbauerMeasure lam) _ hiw
  let F : IntegrableInput (gegenbauerMeasure tau) := ⟨fun x ↦ ∫ y, K (x,y)
    ∂gegenbauerMeasure lam,hKI.integral_prod_left⟩
  refine ⟨F,?_,?_⟩
  · filter_upwards [ae_mem_Ioo_gegenbauerMeasure tau,hKrow] with x hx hrow
    have ht := (integrable_gegenbauerMeasure_iff lam _).mp (hKr x)
    have hj := integrable_integral_powerLawDomain x ⟨_,ht⟩
    have hval (y : PowerLawDomain x) :
        (gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*K (x,y.val) =
        |x-y.val|^α*(g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) := by
      rw [hrow y.val,he ⟨(x,y.val),hx,y.property.1,y.property.2.symm⟩]
      ring
    let I : PowerLawInput α x := ⟨fun y ↦
      g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val,by
        apply hj.1.congr
        exact Eventually.of_forall hval⟩
    refine ⟨I,fun _ ↦ rfl,?_⟩
    calc
      _ = ∫ y : Ioo (-1 : ℝ) 1, (gegenbauerWeight lam y : ℝ)*K (x,y.val) :=
        integral_gegenbauerMeasure lam ⟨_,hKr x⟩
      _ = ∫ y : PowerLawDomain x,
          (gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*K (x,y.val)
          ∂Measure.comap Subtype.val volume := hj.2.symm
      _ = _ := integral_congr_ae (Eventually.of_forall hval)
  · calc
      _ = ∫ z, K z ∂(gegenbauerMeasure tau).prod (gegenbauerMeasure lam) := (integral_prod _ hKI).symm
      _ = ∫ z, (w z : ℝ)*(g z.1*f z.2) ∂(gegenbauerMeasure tau).prod (gegenbauerMeasure lam) :=
        integral_congr_ae hKe
      _ = _ := by
        rw [hk,integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal (by simp)]
        simp only [ENNReal.coe_toReal,smul_eq_mul]

theorem powerLawWeakFubini {α lam : ℝ}
    (f g : ℝ → ℝ)
    (hi : Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam)) :
    ∃ F : IntegrableInput (gegenbauerMeasure lam),
      (∀ᵐ x ∂gegenbauerMeasure lam, ∃ I : PowerLawInput α x,
        (∀ y : PowerLawDomain x, I.val y =
          g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) ∧
        F.val x = powerLawIntegral I) ∧
      (∫ x, F.val x ∂gegenbauerMeasure lam) =
        ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam := by
  exact twoWeightPowerLawWeakFubini (α := α) (lam := lam) (tau := lam) f g hi

end Real

namespace Real
private theorem isFiniteMeasure_compatiblePowerLawKernel {α lam : ℝ} {k : ℕ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hk : lam+α/2 = k) :
    IsFiniteMeasure (powerLawKernelMeasure α lam) := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  obtain ⟨K,hK,he,_,hμ⟩ := exists_powerLawKernel_density α
  let P := powerLawGegenbauerInitialPolynomial (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩) k
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  have hbound : (∫⁻ z, (K z : ℝ≥0∞) ∂(gegenbauerMeasure lam).prod (gegenbauerMeasure lam)) ≤
      ∫⁻ _ : ℝ, ENNReal.ofReal M ∂gegenbauerMeasure lam := by
    rw [lintegral_prod _ hK.coe_nnreal_ennreal.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam] with x hx
    rw [lintegral_safePowerLawKernel_row ⟨α,hα⟩ ⟨lam,hlam⟩ ⟨x,hx⟩ K he,
      ← eval_powerLawGegenbauerInitialPolynomial ⟨α,hα⟩ ⟨lam,hlam⟩ hk ⟨x,hx⟩]
    exact ENNReal.ofReal_le_ofReal ((le_norm_self (P.eval x)).trans (hM x (Ioo_subset_Icc_self hx)))
  have hfinite : (∫⁻ _ : ℝ, ENNReal.ofReal M ∂gegenbauerMeasure lam) < ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  constructor
  change twoWeightPowerLawKernelMeasure α lam lam univ < ∞
  rw [hμ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact hbound.trans_lt hfinite

/-- Polynomial pairings are integrable for a compatible power-law kernel measure.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2. -/
theorem integrable_powerLawKernelMeasure_polynomial_of_compatible {α lam : ℝ} {k : ℕ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hk : lam+α/2 = k) (p q : ℝ[X]) :
    Integrable (fun z : ℝ × ℝ ↦ q.eval z.1*p.eval z.2) (powerLawKernelMeasure α lam) := by
  let := isFiniteMeasure_compatiblePowerLawKernel hα hlam hk
  obtain ⟨K,_,_,_,hμ⟩ := exists_powerLawKernel_density α
  have hm : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ lam lam
  have hs : ∀ᵐ z ∂powerLawKernelMeasure α lam,
      z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2 := by
    rw [hm]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_powerLawKernelDomain lam lam)
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    q.continuous.continuousOn
  obtain ⟨N,hN⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by constructor <;> norm_num))
  apply Integrable.of_bound (by fun_prop) (M*N)
  filter_upwards [hs] with z hz
  rw [norm_mul]
  exact mul_le_mul (hM z.1 (Ioo_subset_Icc_self hz.1))
    (hN z.2 (Ioo_subset_Icc_self hz.2.1)) (norm_nonneg _) hM0
end Real
