/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.KernelDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.FullCoefficients
public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisMap

/-! # Power-law operators between two Gegenbauer measures

The input measure is μ_lam and the output measure is μ_tau. Separate uniform
row masses give a sufficient Schur bound sqrt(M N). This is not a sharp
classification of two-weight boundedness. Reference: the classical Schur test;
Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real
variable {α lam tau : ℝ}

theorem PowerLawL2Data.twoWeight_kernel_fst {α lam : ℝ} (p : PowerLawL2Data α lam) (tau : ℝ) :
    (twoWeightPowerLawKernelMeasure α tau lam).map Prod.fst ≤
      ENNReal.ofReal p.bound • gegenbauerMeasure tau := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α
  rw [hμ tau lam,map_fst_withDensity_prod _ _ _ hw.coe_nnreal_ennreal,← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_mem_Ioo_gegenbauerMeasure tau] with x hx
  rw [lintegral_safePowerLawKernel_row ⟨α,p.exponent_mem⟩ ⟨lam,p.weight_mem⟩ ⟨x,hx⟩ w he]
  exact ENNReal.ofReal_le_ofReal (p.mass_le ⟨x,hx⟩)

theorem PowerLawL2Data.twoWeight_kernel_snd {α tau : ℝ} (q : PowerLawL2Data α tau) (lam : ℝ)
    (hLam : SFinite (gegenbauerMeasure lam)) :
    (twoWeightPowerLawKernelMeasure α tau lam).map Prod.snd ≤
      ENNReal.ofReal q.bound • gegenbauerMeasure lam := by
  let : SFinite (gegenbauerMeasure lam) := hLam
  let : SFinite (gegenbauerMeasure tau) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,he,hz,hμ⟩ := exists_powerLawKernel_density α
  rw [hμ tau lam,map_snd_withDensity_prod _ _ _ hw.coe_nnreal_ennreal,← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam] with x hx
  have ht (z : PowerLawKernelDomain) :
      ((fun z : ℝ × ℝ ↦ w (z.2,z.1)) z.val : ℝ) = |z.val.1-z.val.2|^α := by
    rw [he ⟨(z.val.2,z.val.1),z.property.2.1,z.property.1,z.property.2.2.symm⟩,abs_sub_comm]
  rw [lintegral_safePowerLawKernel_row ⟨α,q.exponent_mem⟩ ⟨tau,q.weight_mem⟩ ⟨x,hx⟩
    (fun z ↦ w (z.2,z.1)) ht]
  exact ENNReal.ofReal_le_ofReal (q.mass_le ⟨x,hx⟩)

def twoWeightPowerLawL2Operator (p : PowerLawL2Data α lam) (q : PowerLawL2Data α tau) :
    Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure tau) :=
  schurL2Operator _ _ (twoWeightPowerLawKernelMeasure α tau lam) (by simp) (by simp)
    (p.twoWeight_kernel_fst tau)
    (q.twoWeight_kernel_snd lam (sFinite_gegenbauerMeasure lam))

def twoWeightPowerLawCoefficientOperator (p : PowerLawL2Data α lam) (q : PowerLawL2Data α tau) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (powerLawHilbertBasis p.weight_mem).coefficientMap (powerLawHilbertBasis q.weight_mem)
    (twoWeightPowerLawL2Operator p q)

theorem twoWeightPowerLawL2Operator_spec (p : PowerLawL2Data α lam) (q : PowerLawL2Data α tau)
    (f : Lp ℝ 2 (gegenbauerMeasure lam)) (g : Lp ℝ 2 (gegenbauerMeasure tau)) :
    Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (twoWeightPowerLawKernelMeasure α tau lam) ∧
    ⟪g,twoWeightPowerLawL2Operator p q f⟫_ℝ =
      ∫ z : ℝ × ℝ, g z.1*f z.2 ∂twoWeightPowerLawKernelMeasure α tau lam := by
  constructor
  · exact integrable_schurL2_pair _ _ (twoWeightPowerLawKernelMeasure α tau lam) (by simp) (by simp)
      (p.twoWeight_kernel_fst tau)
      (q.twoWeight_kernel_snd lam (sFinite_gegenbauerMeasure lam)) f g
  · exact inner_schurL2Operator _ _ (twoWeightPowerLawKernelMeasure α tau lam) (by simp) (by simp)
      (p.twoWeight_kernel_fst tau)
      (q.twoWeight_kernel_snd lam (sFinite_gegenbauerMeasure lam)) f g

theorem norm_twoWeightPowerLawL2Operator_leOn (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) :
    ‖twoWeightPowerLawL2Operator p q‖ ≤ sqrt (p.bound : ℝ)*sqrt (q.bound : ℝ) := by
  apply (norm_schurL2Operator_le _ _ _ _ _ _ _).trans_eq
  erw [ENNReal.toReal_ofReal p.bound.property,ENNReal.toReal_ofReal q.bound.property]
  all_goals rfl

theorem norm_twoWeightPowerLawCoefficientOperatorOn (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) :
    ‖twoWeightPowerLawCoefficientOperator p q‖ = ‖twoWeightPowerLawL2Operator p q‖ :=
  (powerLawHilbertBasis p.weight_mem).norm_coefficientMap (powerLawHilbertBasis q.weight_mem) _

theorem twoWeightPowerLawCoefficientOperator_reprOn (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    twoWeightPowerLawCoefficientOperator p q ((powerLawHilbertBasis p.weight_mem).repr f) =
      (powerLawHilbertBasis q.weight_mem).repr (twoWeightPowerLawL2Operator p q f) :=
  (powerLawHilbertBasis p.weight_mem).coefficientMap_repr (powerLawHilbertBasis q.weight_mem) _ f

theorem twoWeightPowerLawCoefficientOperator_singleOn (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) (i j : ℕ) :
    twoWeightPowerLawCoefficientOperator p q (lp.single 2 j 1) i =
      ∫ z : ℝ × ℝ, (powerLawHilbertBasis q.weight_mem i z.1 * powerLawHilbertBasis p.weight_mem j z.2)
        ∂twoWeightPowerLawKernelMeasure α tau lam := by
  rw [twoWeightPowerLawCoefficientOperator,HilbertBasis.coefficientMap_single]
  exact (twoWeightPowerLawL2Operator_spec p q _ _).2

theorem tendsto_twoWeightPowerLawCoefficientOperator_finiteSectionsOn (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) (c : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun n ↦ lp.initialL2Projection n
      (twoWeightPowerLawCoefficientOperator p q (lp.initialL2Projection n c)))
      atTop (𝓝 (twoWeightPowerLawCoefficientOperator p q c)) := by
  simpa only [lp.initialL2Projection_apply] using
    lp.tendsto_initialL2Sections (twoWeightPowerLawCoefficientOperator p q) c

theorem twoWeightPowerLawL2Operator_hasPowerLawIntegral (p : PowerLawL2Data α lam)
    (q : PowerLawL2Data α tau) (f : Lp ℝ 2 (gegenbauerMeasure lam))
    (g : Lp ℝ 2 (gegenbauerMeasure tau)) :
    ∃ F : IntegrableInput (gegenbauerMeasure tau),
      (∀ᵐ x ∂gegenbauerMeasure tau, ∃ I : PowerLawInput α x,
        (∀ y : PowerLawDomain x, I.val y =
          g x*(gegenbauerWeight lam ⟨y.val,y.property.1⟩ : ℝ)*f y.val) ∧
        F.val x = powerLawIntegral I) ∧
      ⟪g,twoWeightPowerLawL2Operator p q f⟫_ℝ = ∫ x, F.val x ∂gegenbauerMeasure tau := by
  obtain ⟨F,hF,hI⟩ := twoWeightPowerLawWeakFubini f g (twoWeightPowerLawL2Operator_spec p q f g).1
  exact ⟨F,hF,(twoWeightPowerLawL2Operator_spec p q f g).2.trans hI.symm⟩

end Real
namespace Real
variable {α lam tau : ℝ}

theorem twoWeightPowerLawKernelMeasure_fst_leOn (p : PowerLawL2Data α lam) (tau : ℝ) :
    (twoWeightPowerLawKernelMeasure α tau lam).map Prod.fst ≤
      ENNReal.ofReal p.bound • gegenbauerMeasure tau :=
  p.twoWeight_kernel_fst tau

theorem twoWeightPowerLawKernelMeasure_snd_leOn (p : PowerLawL2Data α lam) (q : PowerLawL2Data α tau) :
    (twoWeightPowerLawKernelMeasure α tau lam).map Prod.snd ≤
      ENNReal.ofReal q.bound • gegenbauerMeasure lam := by
  let : IsFiniteMeasure (gegenbauerMeasure lam) := isFiniteMeasure_gegenbauerMeasure p.weight_mem
  exact q.twoWeight_kernel_snd lam inferInstance

theorem exists_twoWeightPowerLawL2Operator_of_endpointOn (α : Ioi (-1 : ℝ))
    (lam tau : Ioi (-(1/2) : ℝ)) (hl : -(1/2) < α.val+lam.val)
    (ht : -(1/2) < α.val+tau.val) :
    ∃ (p : PowerLawL2Data α.val lam.val) (q : PowerLawL2Data α.val tau.val),
      0 < (p.bound : ℝ) ∧ 0 < (q.bound : ℝ) ∧
      ‖twoWeightPowerLawL2Operator p q‖ ≤ sqrt (p.bound : ℝ)*sqrt (q.bound : ℝ) := by
  obtain ⟨p,hp⟩ := exists_powerLawL2Data_of_endpoint α lam hl
  obtain ⟨q,hq⟩ := exists_powerLawL2Data_of_endpoint α tau ht
  exact ⟨p,q,hp,hq,norm_twoWeightPowerLawL2Operator_leOn p q⟩

end Real
