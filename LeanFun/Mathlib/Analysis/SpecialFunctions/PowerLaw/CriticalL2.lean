/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.ClassicalIdentities

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.KernelDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.CriticalMass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.EndpointL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Density
public import LeanFun.Mathlib.Analysis.IntegralEq.WeightedL2



/-! # Bounded power-law operators at the critical endpoint parameters

The exact positive Schur weight proves boundedness at `α + λ = -1/2`.
This uses the weighted Schur test and the binomial specialization of the
Gutleb–Carrillo–Olver power-law formula (arXiv:2011.00045, Section 2).
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace NNReal
namespace Real

def powerLawSchurWeight (α : ℝ) : C(Ioo (-1 : ℝ) 1, ℝ≥0) :=
  Polynomial.gegenbauerWeight ((α+1)/2)

theorem powerLawSchurWeight_apply (α : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (powerLawSchurWeight α x : ℝ) = (1-x.val^2)^(α/2) := by
  rw [powerLawSchurWeight, Polynomial.gegenbauerWeight_apply]
  congr 1
  ring

theorem powerLawSchurWeight_pos (α : ℝ) (x : Ioo (-1 : ℝ) 1) :
    0 < (powerLawSchurWeight α x : ℝ) := by
  rw [powerLawSchurWeight_apply]
  exact rpow_pos_of_pos (by nlinarith [x.property.1,x.property.2]) _

abbrev PowerLawSchurParameter := {α : ℝ //
  (∀ n : ℕ, (α+1)/2 ≠ -(n : ℝ)) ∧ (∀ n : ℕ, -α/2 ≠ -(n : ℝ))}

def PowerLawSchurParameter.ofCritical (α : Ioo (-1 : ℝ) 0) : PowerLawSchurParameter :=
  ⟨α.val, (GammaPoint.ofPos ((α.val+1)/2) (by linarith [α.property.1])).property,
    (GammaPoint.ofPos (-α.val/2) (by linarith [α.property.2])).property⟩

def powerLawSchurConstant (α : PowerLawSchurParameter) : ℝ :=
  GammaOn ⟨(α.val+1)/2,α.property.1⟩*GammaOn ⟨-α.val/2,α.property.2⟩/
    GammaOn (.ofPos (1/2) (by norm_num))

theorem powerLawSchurConstant_pos (α : Ioo (-1 : ℝ) 0) :
    0 < powerLawSchurConstant (.ofCritical α) := by
  apply div_pos
  · apply mul_pos
    · apply GammaOn_pos
      change 0 < (α.val+1)/2
      linarith [α.property.1]
    · apply GammaOn_pos
      change 0 < -α.val/2
      linarith [α.property.2]
  · apply GammaOn_pos
    norm_num [GammaPoint.ofPos]

def powerLawSchurMeasure (α lam : ℝ) : Measure (ℝ × ℝ) :=
  powerLawKernelMeasure α (lam+α/2)


end Real
namespace Real

theorem powerLawSchurConstant_apply (α : PowerLawSchurParameter) :
    powerLawSchurConstant α =
      GammaOn ⟨(α.val+1)/2,α.property.1⟩*GammaOn ⟨-α.val/2,α.property.2⟩/
        GammaOn (.ofPos (1/2) (by norm_num)) := rfl

theorem powerLawIntegral_gegenbauerWeight_criticalOn (α : Ioo (-1 : ℝ) 0)
    (x : Ioo (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeight ⟨α.val,α.property.1⟩
      ⟨-α.val/2-1/2,by change -(1/2) < -α.val/2-1/2; linarith [α.property.2]⟩ x) =
      powerLawSchurConstant (.ofCritical α)*(powerLawSchurWeight α.val x : ℝ) := by
  rw [powerLawIntegral_gegenbauerWeight_hypergeometricSqOn,powerLawSchurWeight_apply]
  simp only [GaussParameters.ofNoPole,
    GammaOn,GammaPoint.ofPos,powerLawSchurConstant,PowerLawSchurParameter.ofCritical]
  simp only [show -α.val/2-1/2+1/2 = -α.val/2 by ring,
    show -α.val/2-1/2+α.val/2+1 = (1/2 : ℝ) by ring]
  have hz : |x.val^2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x.val)]
    nlinarith [x.property.1,x.property.2,sq_nonneg (x.val+1),sq_nonneg (x.val-1)]
  have hc := ordinaryHypergeometricOn_cancel_of_pos (-α.val/2)
    ⟨(1/2 : ℝ),by norm_num⟩ ⟨x.val^2,by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hz⟩
  simp only [GaussParameters.ofNoPole] at hc
  erw [show -(-α.val/2-1/2)-α.val/2 = (1/2 : ℝ) by ring, hc]
  congr 2
  ring
end Real

namespace Real








attribute [local instance] Measure.Subtype.measureSpace

private theorem exists_positive_gegenbauer_density_shift (p : ℝ) :
    ∃ w : ℝ → ℝ≥0, Measurable w ∧
      (∀ x : Ioo (-1 : ℝ) 1, w x.val = gegenbauerWeight (p+1/2) x) ∧
      (∀ x : ℝ, 0 < (w x : ℝ)) ∧ ∀ lam : ℝ,
      (gegenbauerMeasure lam).withDensity (fun x ↦ (w x : ℝ≥0∞)) =
        gegenbauerMeasure (lam+p) := by
  let w : ℝ → ℝ≥0 := Function.extend Subtype.val (gegenbauerWeight (p+1/2)) (fun _ ↦ 1)
  have hw : Measurable w :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurable_extend
      (gegenbauerWeight (p+1/2)).continuous.measurable measurable_const
  have he (x : Ioo (-1 : ℝ) 1) : w x.val = gegenbauerWeight (p+1/2) x :=
    Subtype.val_injective.extend_apply _ _ x
  refine ⟨w,hw,he,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · rw [he ⟨x,hx⟩,gegenbauerWeight_apply]
      exact Real.rpow_pos_of_pos (by nlinarith [hx.1,hx.2]) _
    · have hz : w x = 1 := by
        apply Function.extend_apply'
        rintro ⟨y,hy⟩
        exact hx (hy ▸ y.property)
      rw [hz]
      norm_num
  · intro lam
    rw [← gegenbauerMeasure_shift lam p]
    apply Measure.ext_of_lintegral
    intro φ hφ
    rw [lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal hφ]
    change (∫⁻ x, (w x : ℝ≥0∞)*φ x ∂Measure.map Subtype.val
      (volume.withDensity (fun x : Ioo (-1 : ℝ) 1 ↦ (gegenbauerWeight lam x : ℝ≥0∞)))) = _
    change _ = ∫⁻ x, φ x ∂Measure.map Subtype.val
      (volume.withDensity (fun x : Ioo (-1 : ℝ) 1 ↦
        ((gegenbauerWeight lam * gegenbauerWeight (p+1/2)) x : ℝ≥0∞)))
    erw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).lintegral_map,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioo).lintegral_map,
      lintegral_withDensity_eq_lintegral_mul _
        (gegenbauerWeight lam).continuous.measurable.coe_nnreal_ennreal
        ((hw.coe_nnreal_ennreal.comp measurable_subtype_coe).mul (hφ.comp measurable_subtype_coe)),
      lintegral_withDensity_eq_lintegral_mul _
        (gegenbauerWeight lam * gegenbauerWeight (p+1/2)).continuous.measurable.coe_nnreal_ennreal
        (hφ.comp measurable_subtype_coe)]
    apply lintegral_congr
    intro x
    simp only [Function.comp_apply,Pi.mul_apply,ContinuousMap.mul_apply,ENNReal.coe_mul,he]
    ring

private theorem exists_schurOperator_of_positive_density (μ : Measure ℝ) [SFinite μ]
    (κ : Measure (ℝ × ℝ)) (hκ : κ ≪ μ.prod μ)
    (w : ℝ → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < (w x : ℝ)) (C : ℝ≥0)
    (hf : (κ.withDensity (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞))).map Prod.fst ≤
      (C : ℝ≥0∞) • μ.withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)))
    (hs : (κ.withDensity (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞))).map Prod.snd ≤
      (C : ℝ≥0∞) • μ.withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2))) :
    ∃ T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, ‖T‖ ≤ (C : ℝ) ∧
      ∀ f g : Lp ℝ 2 μ, Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) κ ∧
        ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂κ := by
  let wp : PositiveWeight μ := ⟨fun x ↦ (w x : ℝ),hw.coe_nnreal_real,Eventually.of_forall hp⟩
  let κw := κ.withDensity (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞))
  let T := weightedSchurL2Operator μ κw wp (C := (C : ℝ≥0∞)) (by simp) hf hs
  refine ⟨T,?_,?_⟩
  · simpa only [T,ENNReal.coe_toReal] using
      norm_weightedSchurL2Operator_le μ κw wp (C := (C : ℝ≥0∞)) (by simp) hf hs
  · intro f g
    have hwp := wp.property.1
    have hbase (u : Lp ℝ 2 μ) : ∀ᵐ x ∂μ, divWeightL2 μ wp u x*(w x : ℝ) = u x := by
      have h := (ae_withDensity_iff (by fun_prop : Measurable
        (fun x ↦ ENNReal.ofReal (wp.val x^2)))).mp (divWeightL2_spec μ wp u)
      filter_upwards [h] with x hx
      exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hp x))))
    have hpair : ∀ᵐ z : ℝ × ℝ ∂κ,
        divWeightL2 μ wp g z.1*(w z.1 : ℝ) = g z.1 ∧
        divWeightL2 μ wp f z.2*(w z.2 : ℝ) = f z.2 :=
      hκ.ae_le ((Measure.quasiMeasurePreserving_fst.ae (hbase g)).and
        (Measure.quasiMeasurePreserving_snd.ae (hbase f)))
    have heq : (fun z : ℝ × ℝ ↦
        (divWeightL2 μ wp g z.1*divWeightL2 μ wp f z.2)*
          ((w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞)).toReal) =ᵐ[κ]
        (fun z ↦ g z.1*f z.2) := by
      filter_upwards [hpair] with z hz
      simp only [ENNReal.toReal_mul,ENNReal.coe_toReal]
      calc
        _ = (divWeightL2 μ wp g z.1*(w z.1 : ℝ))*
          (divWeightL2 μ wp f z.2*(w z.2 : ℝ)) := by ring
        _ = _ := by rw [hz.1,hz.2]
    have hi := integrable_weightedSchurL2_pair μ κw wp (C := (C : ℝ≥0∞))
      (by simp) hf hs f g
    constructor
    · rw [show κw = κ.withDensity (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞)) from rfl,
        integrable_withDensity_iff (by fun_prop) (by simp [ENNReal.mul_lt_top])] at hi
      exact hi.congr heq
    · change ⟪g,weightedSchurL2Operator μ κw wp (C := (C : ℝ≥0∞)) (by simp) hf hs f⟫_ℝ = _
      rw [inner_weightedSchurL2Operator]
      change (∫ z, divWeightL2 μ wp g z.1*divWeightL2 μ wp f z.2
        ∂κ.withDensity (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞))) = _
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp [ENNReal.mul_lt_top])]
      apply integral_congr_ae
      simpa only [smul_eq_mul,mul_comm] using heq

private theorem powerLawSchurMeasure_eq_safe_density (α lam : ℝ) (w : ℝ → ℝ≥0) (hw : Measurable w)
    (hshift : ∀ t : ℝ, (gegenbauerMeasure t).withDensity (fun x ↦ (w x : ℝ≥0∞)) =
      gegenbauerMeasure (t+α/2)) :
    powerLawSchurMeasure α lam = (powerLawKernelMeasure α lam).withDensity
      (fun z ↦ (w z.1 : ℝ≥0∞)*(w z.2 : ℝ≥0∞)) := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  obtain ⟨K,hK,_,_,hμ⟩ := exists_powerLawKernel_density α
  have hk (t : ℝ) : powerLawKernelMeasure α t =
      ((gegenbauerMeasure t).prod (gegenbauerMeasure t)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ t t
  rw [powerLawSchurMeasure,hk,← hshift lam,
    prod_withDensity hw.coe_nnreal_ennreal hw.coe_nnreal_ennreal,
    ← withDensity_mul _ (by fun_prop) hK.coe_nnreal_ennreal,
    hk,← withDensity_mul _ hK.coe_nnreal_ennreal (by fun_prop)]
  congr 1
  funext z
  simp only [Pi.mul_apply]
  ring

private theorem powerLawSchurMeasure_marginals_safe_density (α : Ioo (-1 : ℝ) 0) (lam : ℝ)
    (hcrit : α.val+lam = -(1/2)) (w : ℝ → ℝ≥0) (hw : Measurable w)
    (he : ∀ x : Ioo (-1 : ℝ) 1, (w x.val : ℝ) = (powerLawSchurWeight α.val x : ℝ))
    (hshift : ∀ t : ℝ, (gegenbauerMeasure t).withDensity (fun x ↦ (w x : ℝ≥0∞)) =
      gegenbauerMeasure (t+α.val/2)) :
    (powerLawSchurMeasure α.val lam).map Prod.fst =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) •
        (gegenbauerMeasure lam).withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) ∧
    (powerLawSchurMeasure α.val lam).map Prod.snd =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) •
        (gegenbauerMeasure lam).withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) := by
  let t := lam+α.val/2
  have ht : t = -α.val/2-1/2 := by dsimp only [t]; linarith
  have htm : -(1/2 : ℝ) < t := by rw [ht]; linarith [α.property.2]
  let : SFinite (gegenbauerMeasure t) := sFinite_gegenbauerMeasure _
  let C := powerLawSchurConstant (.ofCritical α)
  have hC : 0 ≤ C := (powerLawSchurConstant_pos α).le
  obtain ⟨K,hK,hKe,_,hμ⟩ := exists_powerLawKernel_density α.val
  have hk : powerLawSchurMeasure α.val lam =
      ((gegenbauerMeasure t).prod (gegenbauerMeasure t)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ t t
  have hrow (x : Ioo (-1 : ℝ) 1) (G : ℝ × ℝ → ℝ≥0)
      (hG : ∀ z : PowerLawKernelDomain, (G z.val : ℝ) = |z.val.1-z.val.2|^α.val) :
      (∫⁻ y, (G (x.val,y) : ℝ≥0∞) ∂gegenbauerMeasure t) =
        ENNReal.ofReal C*(w x.val : ℝ≥0∞) := by
    rw [lintegral_safePowerLawKernel_row ⟨α.val,α.property.1⟩ ⟨t,htm⟩ x G hG]
    have hm := powerLawIntegral_gegenbauerWeight_criticalOn α x
    have hp : (⟨t,htm⟩ : Ioi (-(1/2) : ℝ)) =
        ⟨-α.val/2-1/2,by change -(1/2 : ℝ) < -α.val/2-1/2; linarith [α.property.2]⟩ :=
      Subtype.ext ht
    rw [hp,hm,← he x,ENNReal.ofReal_mul hC,ENNReal.ofReal_coe_nnreal]
  have hd : (gegenbauerMeasure t).withDensity
        (fun x ↦ ENNReal.ofReal C*(w x : ℝ≥0∞)) =
      ENNReal.ofReal C • (gegenbauerMeasure lam).withDensity
        (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) := by
    rw [show gegenbauerMeasure t = (gegenbauerMeasure lam).withDensity
      (fun x ↦ (w x : ℝ≥0∞)) from (hshift lam).symm,
      ← withDensity_mul _ hw.coe_nnreal_ennreal (by fun_prop),
      ← withDensity_smul _ (by fun_prop)]
    congr 1
    funext x
    simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul,
      ENNReal.ofReal_pow (w x).coe_nonneg,ENNReal.ofReal_coe_nnreal]
    ring
  constructor
  · rw [hk,map_fst_withDensity_prod _ _ _ hK.coe_nnreal_ennreal,← hd]
    apply withDensity_congr_ae
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure t] with x hx
    exact hrow ⟨x,hx⟩ K hKe
  · rw [hk,map_snd_withDensity_prod _ _ _ hK.coe_nnreal_ennreal,← hd]
    apply withDensity_congr_ae
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure t] with x hx
    apply hrow ⟨x,hx⟩ (fun z ↦ K (z.2,z.1))
    intro z
    rw [hKe ⟨(z.val.2,z.val.1),z.property.2.1,z.property.1,z.property.2.2.symm⟩,
      abs_sub_comm]

private theorem gegenbauerMeasure_safe_density_square (α lam : ℝ) (w : ℝ → ℝ≥0) (hw : Measurable w)
    (hshift : ∀ t : ℝ, (gegenbauerMeasure t).withDensity (fun x ↦ (w x : ℝ≥0∞)) =
      gegenbauerMeasure (t+α/2)) :
    (gegenbauerMeasure lam).withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) =
      gegenbauerMeasure (lam+α) := by
  calc
    _ = ((gegenbauerMeasure lam).withDensity (fun x ↦ (w x : ℝ≥0∞))).withDensity
        (fun x ↦ (w x : ℝ≥0∞)) := by
      rw [← withDensity_mul _ hw.coe_nnreal_ennreal hw.coe_nnreal_ennreal]
      congr 1
      funext x
      simp only [Pi.mul_apply,pow_two,ENNReal.ofReal_mul (w x).coe_nonneg,
        ENNReal.ofReal_coe_nnreal]
    _ = gegenbauerMeasure (lam+α/2+α/2) := by rw [hshift,hshift]
    _ = _ := by congr 1; ring

private theorem powerLawSchurMeasure_marginals_critical (α : Ioo (-1 : ℝ) 0) :
    (powerLawSchurMeasure α.val (-α.val-1/2)).map Prod.fst =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) • gegenbauerMeasure (-(1/2)) ∧
    (powerLawSchurMeasure α.val (-α.val-1/2)).map Prod.snd =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) • gegenbauerMeasure (-(1/2)) := by
  obtain ⟨w,hw,he,_,hshift⟩ := exists_positive_gegenbauer_density_shift (α.val/2)
  have heW (x : Ioo (-1 : ℝ) 1) :
      (w x.val : ℝ) = (powerLawSchurWeight α.val x : ℝ) := by
    rw [he]
    change (gegenbauerWeight (α.val/2+1/2) x : ℝ) =
      (gegenbauerWeight ((α.val+1)/2) x : ℝ)
    rw [show α.val/2+1/2 = (α.val+1)/2 by ring]
  have hm := powerLawSchurMeasure_marginals_safe_density α (-α.val-1/2) (by ring) w hw heW hshift
  have hsq := gegenbauerMeasure_safe_density_square α.val (-α.val-1/2) w hw hshift
  rw [show -α.val-1/2+α.val = -(1/2 : ℝ) by ring] at hsq
  simpa only [hsq] using hm

theorem powerLawSchurMeasure_fstOn (α : Ioo (-1 : ℝ) 0) :
    (powerLawSchurMeasure α.val (-α.val-1/2)).map Prod.fst =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) • gegenbauerMeasure (-(1/2)) := by
  exact (powerLawSchurMeasure_marginals_critical α).1

theorem powerLawSchurMeasure_sndOn (α : Ioo (-1 : ℝ) 0) :
    (powerLawSchurMeasure α.val (-α.val-1/2)).map Prod.snd =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)) • gegenbauerMeasure (-(1/2)) := by
  exact (powerLawSchurMeasure_marginals_critical α).2


theorem exists_criticalPowerLawL2Operator_classical {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2)) :
    ∃ T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam),
      ‖T‖ ≤ powerLawSchurConstant (.ofCritical ⟨α,hα,by linarith⟩) ∧
      ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
        Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
        ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam := by
  let αt : Ioo (-1 : ℝ) 0 := ⟨α,hα,by linarith⟩
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,_,hp,hshift⟩ := exists_positive_gegenbauer_density_shift (α/2)
  have hparam : lam = -α-1/2 := by linarith
  have hsq := gegenbauerMeasure_safe_density_square α lam w hw hshift
  rw [show lam+α = -(1/2 : ℝ) by linarith] at hsq
  have hm :
      (powerLawSchurMeasure α lam).map Prod.fst =
        ENNReal.ofReal (powerLawSchurConstant (.ofCritical αt)) •
          (gegenbauerMeasure lam).withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) ∧
      (powerLawSchurMeasure α lam).map Prod.snd =
        ENNReal.ofReal (powerLawSchurConstant (.ofCritical αt)) •
          (gegenbauerMeasure lam).withDensity (fun x ↦ ENNReal.ofReal ((w x : ℝ)^2)) := by
    rw [hsq,hparam]
    exact ⟨powerLawSchurMeasure_fstOn αt,powerLawSchurMeasure_sndOn αt⟩
  have ht := powerLawSchurMeasure_eq_safe_density α lam w hw hshift
  obtain ⟨K,_,_,_,hμ⟩ := exists_powerLawKernel_density α
  have hk : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ lam lam
  have hκ : powerLawKernelMeasure α lam ≪
      (gegenbauerMeasure lam).prod (gegenbauerMeasure lam) := by
    rw [hk]
    exact withDensity_absolutelyContinuous _ _
  let C : ℝ≥0 := ⟨powerLawSchurConstant (.ofCritical αt),(powerLawSchurConstant_pos αt).le⟩
  have hC : ENNReal.ofReal (powerLawSchurConstant (.ofCritical αt)) = (C : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (powerLawSchurConstant_pos αt).le
  apply exists_schurOperator_of_positive_density (gegenbauerMeasure lam)
    (powerLawKernelMeasure α lam) hκ w hw hp C
  · rw [← ht]
    simpa only [hC] using hm.1.le
  · rw [← ht]
    simpa only [hC] using hm.2.le

def criticalPowerLawL2Operator {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2)) :
    Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam) :=
  (exists_criticalPowerLawL2Operator_classical hα hlam hcrit).choose

theorem norm_criticalPowerLawL2Operator_leOn {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2)) :
    ‖criticalPowerLawL2Operator hα hlam hcrit‖ ≤
      powerLawSchurConstant (.ofCritical ⟨α,hα,by linarith⟩) :=
  (exists_criticalPowerLawL2Operator_classical hα hlam hcrit).choose_spec.1

theorem criticalPowerLawL2Operator_spec {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2))
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
    ⟪g,criticalPowerLawL2Operator hα hlam hcrit f⟫_ℝ =
      ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam :=
  (exists_criticalPowerLawL2Operator_classical hα hlam hcrit).choose_spec.2 f g






end Real
namespace Real

theorem powerLawSchurMeasure_apply (α lam : ℝ) :
    powerLawSchurMeasure α lam = powerLawKernelMeasure α (lam+α/2) := rfl

theorem exists_powerLawL2Operator_of_le_endpointOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (hsum : -(1/2) ≤ α.val+lam.val) :
    ∃ (M : ℝ) (T : Lp ℝ 2 (gegenbauerMeasure lam.val) →L[ℝ]
        Lp ℝ 2 (gegenbauerMeasure lam.val)),
      0 < M ∧ ‖T‖ ≤ M ∧ ∀ f g,
        Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α.val lam.val) ∧
        ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α.val lam.val := by
  rcases hsum.eq_or_lt with hc | hs
  · refine ⟨powerLawSchurConstant (.ofCritical ⟨α.val,α.property,by have hl : -(1/2) < lam.val := lam.property; linarith⟩),
      criticalPowerLawL2Operator α.property lam.property hc.symm, ?_,
      norm_criticalPowerLawL2Operator_leOn α.property lam.property hc.symm,
      criticalPowerLawL2Operator_spec α.property lam.property hc.symm⟩
    exact powerLawSchurConstant_pos _
  · obtain ⟨p,hp⟩ := exists_powerLawL2Data_of_endpoint α lam hs
    exact ⟨p.bound,powerLawL2Operator p,hp,norm_powerLawL2Operator_leOn p,
      powerLawL2Operator_spec p⟩

end Real
namespace Real

theorem lintegral_powerLaw_critical_weightOn (α : Ioo (-1 : ℝ) 0)
    (x : Ioo (-1 : ℝ) 1) :
    (∫⁻ y : PowerLawDomain x.val,
      ENNReal.ofReal (powerLawSchurWeight α.val ⟨y.val,y.property.1⟩ : ℝ) *
        ENNReal.ofReal (|x.val-y.val|^α.val)
      ∂Measure.comap Subtype.val (gegenbauerMeasure (-α.val-1/2))) =
      ENNReal.ofReal (powerLawSchurConstant (.ofCritical α)*
        (powerLawSchurWeight α.val x : ℝ)) := by
  let lam : ℝ := -α.val-1/2
  obtain ⟨w,hw,he,_,hs⟩ := exists_positive_gegenbauer_density_shift (α.val/2)
  have heW (y : Ioo (-1 : ℝ) 1) :
      (w y.val : ℝ) = (powerLawSchurWeight α.val y : ℝ) := by
    rw [he]
    change (gegenbauerWeight (α.val/2+1/2) y : ℝ) =
      (gegenbauerWeight ((α.val+1)/2) y : ℝ)
    rw [show α.val/2+1/2 = (α.val+1)/2 by ring]
  obtain ⟨K,hK,hKe,_,_⟩ := exists_powerLawKernel_density α.val
  let : NullSingletonClass (gegenbauerMeasure lam) := nullSingletonClass_gegenbauerMeasure _
  have hae : ∀ᵐ y ∂gegenbauerMeasure lam, y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val :=
    (ae_mem_Ioo_gegenbauerMeasure lam).and ((gegenbauerMeasure lam).ae_ne x.val)
  have ht := lintegral_subtype_comap (μ := gegenbauerMeasure lam)
    (measurableSet_powerLawDomain x.val)
    (fun y : ℝ ↦ (w y : ℝ≥0∞)*(K (x.val,y) : ℝ≥0∞))
  erw [Measure.restrict_eq_self_of_ae_mem hae] at ht
  calc
    _ = ∫⁻ y : PowerLawDomain x.val,
        (w y.val : ℝ≥0∞)*(K (x.val,y.val) : ℝ≥0∞)
        ∂Measure.comap Subtype.val (gegenbauerMeasure lam) := by
      apply lintegral_congr
      intro y
      rw [← heW ⟨y.val,y.property.1⟩,
        ← hKe ⟨(x.val,y.val),x.property,y.property.1,y.property.2.symm⟩,
        ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ y, (w y : ℝ≥0∞)*(K (x.val,y) : ℝ≥0∞) ∂gegenbauerMeasure lam := ht
    _ = ∫⁻ y, (K (x.val,y) : ℝ≥0∞) ∂gegenbauerMeasure (lam+α.val/2) := by
      rw [← hs lam,lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal
        (show Measurable (fun y : ℝ ↦ (K (x.val,y) : ℝ≥0∞)) from
          hK.coe_nnreal_ennreal.comp (measurable_const.prodMk measurable_id))]
      rfl
    _ = _ := by
      have hparam : lam+α.val/2 = -α.val/2-1/2 := by dsimp [lam]; ring
      rw [lintegral_safePowerLawKernel_row ⟨α.val,α.property.1⟩
        ⟨lam+α.val/2,by change -(1/2 : ℝ) < lam+α.val/2; rw [hparam]; linarith [α.property.2]⟩ x K hKe]
      have hp : (⟨lam+α.val/2,by change -(1/2 : ℝ) < lam+α.val/2; rw [hparam]; linarith [α.property.2]⟩ : Ioi (-(1/2) : ℝ)) =
          ⟨-α.val/2-1/2,by change -(1/2 : ℝ) < -α.val/2-1/2; linarith [α.property.2]⟩ :=
        Subtype.ext hparam
      rw [hp,powerLawIntegral_gegenbauerWeight_criticalOn]

end Real
namespace Real

theorem criticalPowerLawL2Operator_unique {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2))
    (T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam))
    (hT : ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
      ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam) :
    T = criticalPowerLawL2Operator hα hlam hcrit := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [hT,(criticalPowerLawL2Operator_spec hα hlam hcrit f g).2]
end Real
namespace Real

theorem inner_criticalPowerLawL2Operator_hasPowerLawIntegral {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hcrit : α+lam = -(1/2))
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ∃ F : IntegrableInput (gegenbauerMeasure lam),
      (∀ᵐ x ∂gegenbauerMeasure lam, ∃ I : PowerLawInput α x,
        (∀ y : PowerLawDomain x, I.val y =
          g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) ∧
        F.val x = powerLawIntegral I) ∧
      ⟪g,criticalPowerLawL2Operator hα hlam hcrit f⟫_ℝ = ∫ x, F.val x ∂gegenbauerMeasure lam := by
  obtain ⟨F,hF,he⟩ := powerLawWeakFubini f g
    (criticalPowerLawL2Operator_spec hα hlam hcrit f g).1
  exact ⟨F,hF,(criticalPowerLawL2Operator_spec hα hlam hcrit f g).2.trans he.symm⟩
end Real
