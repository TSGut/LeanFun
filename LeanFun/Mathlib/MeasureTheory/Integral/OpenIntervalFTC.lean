/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-! # Fundamental theorem on an open integration domain
The continuous primitive includes the endpoints; the integrable derivative is
only evaluated in the open interval. Reference: the classical fundamental theorem
of calculus used in the Pearson identities of DLMF Section 18.8.
-/
public section
open MeasureTheory Set Filter
attribute [local instance] Measure.Subtype.measureSpace
namespace intervalIntegral
/-- Integrate a certified interior derivative of a continuous primitive. -/
theorem integral_eq_sub_of_hasDerivAtOnOpen {a b : ℝ} (hab : a < b) (F : C(Icc a b, ℝ))
    (g : IntegrableInput (volume : Measure (Ioo a b)))
    (hd : ∀ x : Ioo a b, HasDerivAtOnOpen ⟨Ioo a b, isOpen_Ioo⟩
      (fun y ↦ F ⟨y, Ioo_subset_Icc_self y.property⟩) (g.val x) x) :
    (∫ x : Ioo a b, g.val x) = F ⟨b, hab.le, le_rfl⟩ - F ⟨a, le_rfl, hab.le⟩ := by
  classical
  let f : ℝ → ℝ := fun t ↦ if h : t ∈ Icc a b then F ⟨t, h⟩ else 0
  let G : ℝ → ℝ := fun t ↦ if h : t ∈ Ioo a b then g.val ⟨t, h⟩ else 0
  have hf (x : Ioo a b) : f x = F ⟨x, Ioo_subset_Icc_self x.property⟩ := by
    simp only [f, dite_eq_left (Ioo_subset_Icc_self x.property)]
  have hG (x : Ioo a b) : G x = g.val x := by simp only [G, dite_eq_left x.property]
  have hc : ContinuousOn f (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun x : Icc a b ↦ f x) = F := by
      funext x
      simp only [f, dite_eq_left x.property]
    change Continuous (fun x : Icc a b ↦ f x)
    rw [he]
    exact F.continuous
  have hdF : ∀ x ∈ Ioo a b, HasDerivAt f (G x) x := by
    intro x hx
    rw [hG ⟨x, hx⟩]
    exact (hasDerivAtOnOpen_iff _ _ _ ⟨x,hx⟩ f hf).mp (hd ⟨x,hx⟩)
  have hiG : IntegrableOn G (Ioo a b) := by
    apply (integrableOn_iff_comap_subtypeVal (f := G) measurableSet_Ioo).mpr
    change Integrable (fun x : Ioo a b ↦ G x) volume
    exact g.property.congr (Eventually.of_forall fun x ↦ (hG x).symm)
  have hint : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hiG
  have hi := integral_eq_sub_of_hasDerivAt_of_le hab.le hc hdF hint
  simp only [f, dite_eq_left (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩),
    dite_eq_left (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)] at hi
  calc
    (∫ x : Ioo a b, g.val x) = ∫ x : Ioo a b, G x :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall fun x ↦ (hG x).symm)
    _ = ∫ x in Ioo a b, G x := integral_subtype measurableSet_Ioo G
    _ = ∫ x in a..b, G x := by
      rw [integral_of_le hab.le, restrict_Ioo_eq_restrict_Ioc]
    _ = _ := hi
end intervalIntegral
