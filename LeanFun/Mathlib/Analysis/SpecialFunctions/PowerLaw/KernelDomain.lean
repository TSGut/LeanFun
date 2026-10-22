/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure
public import LeanFun.Mathlib.MeasureTheory.Measure.NonnegativeDensity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
/-! # Power-law kernel measures on their classical domain

The kernel density is evaluated only on the off-diagonal open square. Its
pushforward gives the joint measure without assigning singular values. No
finiteness or lower bound on the exponents is needed for these measures.
Reference: the positive-kernel form of Schur's test;
Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/
open MeasureTheory Polynomial Set Filter
open scoped ENNReal NNReal
@[expose] public noncomputable section
namespace Real
abbrev PowerLawKernelDomain := {z : ℝ × ℝ //
  z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2}

theorem measurableSet_powerLawKernelDomain : MeasurableSet
    {z : ℝ × ℝ | z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2} := by
  measurability

theorem ae_mem_powerLawKernelDomain (tau lam : ℝ) :
    ∀ᵐ z ∂(gegenbauerMeasure tau).prod (gegenbauerMeasure lam),
      z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2 := by
  let : SFinite (gegenbauerMeasure tau) :=
    sFinite_gegenbauerMeasure _
  let : SFinite (gegenbauerMeasure lam) :=
    sFinite_gegenbauerMeasure _
  let : NullSingletonClass (gegenbauerMeasure lam) :=
    nullSingletonClass_gegenbauerMeasure _
  have hn : ∀ᵐ z ∂(gegenbauerMeasure tau).prod (gegenbauerMeasure lam), z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Eventually.of_forall (fun x ↦ ((gegenbauerMeasure lam).ae_ne x).mono (fun _ h ↦ h.symm))
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gegenbauerMeasure tau)
    (ν := gegenbauerMeasure lam)).ae (ae_mem_Ioo_gegenbauerMeasure tau)
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gegenbauerMeasure tau)
    (ν := gegenbauerMeasure lam)).ae (ae_mem_Ioo_gegenbauerMeasure lam)
  filter_upwards [hx,hy,hn] with z hx hy hn
  exact ⟨hx,hy,hn⟩

def twoWeightPowerLawKernelMeasure (α tau lam : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map Subtype.val
    ((Measure.comap (Subtype.val : PowerLawKernelDomain → ℝ × ℝ)
      ((gegenbauerMeasure tau).prod (gegenbauerMeasure lam))).withDensity
        (fun z ↦ ENNReal.ofReal (|z.val.1-z.val.2|^α)))
end Real
namespace Real


end Real
namespace Real

theorem powerLawKernelDomain_base_pos (z : PowerLawKernelDomain) :
    0 < |z.val.1-z.val.2| := abs_pos.mpr (sub_ne_zero.mpr z.property.2.2)

theorem twoWeightPowerLawKernelMeasure_lintegral (α tau lam : ℝ)
    (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ z, φ z ∂twoWeightPowerLawKernelMeasure α tau lam) =
      ∫⁻ z : PowerLawKernelDomain, ENNReal.ofReal (|z.val.1-z.val.2|^α)*φ z.val
        ∂Measure.comap Subtype.val ((gegenbauerMeasure tau).prod (gegenbauerMeasure lam)) := by
  have hm : Measurable (fun z : PowerLawKernelDomain ↦ ENNReal.ofReal (|z.val.1-z.val.2|^α)) := by fun_prop
  erw [twoWeightPowerLawKernelMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_powerLawKernelDomain).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul _ hm
      (hφ.comp measurable_subtype_coe)]
  rfl

def powerLawKernelMeasure (α lam : ℝ) : Measure (ℝ × ℝ) :=
  twoWeightPowerLawKernelMeasure α lam lam


theorem twoWeightPowerLawKernelMeasure_self (α lam : ℝ) :
    twoWeightPowerLawKernelMeasure α lam lam = powerLawKernelMeasure α lam := rfl
end Real

namespace Real
/-- Internal transport witness for the typed kernel measure. -/
theorem exists_powerLawKernel_density (α : ℝ) :
    ∃ w : ℝ × ℝ → ℝ≥0, Measurable w ∧
      (∀ z : PowerLawKernelDomain, (w z.val : ℝ) = |z.val.1-z.val.2|^α) ∧
      (∀ z : ℝ × ℝ, ¬(z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2) → w z = 0) ∧
      ∀ tau lam : ℝ, twoWeightPowerLawKernelMeasure α tau lam =
        ((Polynomial.gegenbauerMeasure tau).prod (Polynomial.gegenbauerMeasure lam)).withDensity
          (fun z ↦ (w z : ℝ≥0∞)) := by
  let f : PowerLawKernelDomain → ℝ≥0 := fun z ↦
    NNReal.mk (|z.val.1-z.val.2|^α) (rpow_pos_of_pos (powerLawKernelDomain_base_pos z) α).le
  have hf : Measurable f := by
    apply measurable_coe_nnreal_real_iff.mp
    change Measurable (fun z : PowerLawKernelDomain ↦ |z.val.1-z.val.2|^α)
    fun_prop
  obtain ⟨w,hw,he,hz,hμ⟩ := MeasureTheory.exists_subtypeNonnegativeDensity_extension measurableSet_powerLawKernelDomain f hf
  refine ⟨w,hw,fun z ↦ ?_,hz,fun tau lam ↦ ?_⟩
  · rw [he z]
    rfl
  · rw [← hμ]
    unfold twoWeightPowerLawKernelMeasure
    congr 2
    funext z
    exact ENNReal.ofReal_eq_coe_nnreal (rpow_nonneg (abs_nonneg _) _)
end Real
