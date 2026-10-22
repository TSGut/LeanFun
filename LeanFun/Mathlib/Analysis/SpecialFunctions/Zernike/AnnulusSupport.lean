/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusMeasure

/-! # Support bounds for annular measures
The polar pushforward lies in the closed unit disk. This supports polynomial
energy estimates for the annular methods of Papadopoulos–Gutleb–Slevinsky–Olver.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Annular measures are supported in the closed unit disk. -/
theorem ae_sq_radius_le_one_zernikeAnnulusMeasure {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (a b : ℝ) : ∀ᵐ v ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b, v 0^2+v 1^2 ≤ 1 := by
  apply Measure.ae_smul_measure (μ := zernikeAnnulusProductMeasure ⟨q,hq.1.le,ne_of_lt hq.2⟩ a b)
  let C : Icc (0 : ℝ) 1 × ℝ → Fin 2 → ℝ := fun v ↦
    zernikeAnnulusCoordinates ⟨q,ne_of_lt hq.2⟩
      ⟨((v.1 : ℝ),v.2),zernikeAnnulusCoordinates_radical_nonneg
        ⟨q,hq.1.le,ne_of_lt hq.2⟩ v.1⟩
  have hC : Continuous C := continuous_zernikeAnnulusCoordinates _ |>.comp (by fun_prop)
  change ∀ᵐ v ∂Measure.map C _, v 0^2+v 1^2 ≤ 1
  rw [ae_map_iff hC.measurable.aemeasurable
    ((isClosed_le (by fun_prop : Continuous (fun v : Fin 2 → ℝ ↦ v 0^2+v 1^2))
      continuous_const).measurableSet)]
  filter_upwards [] with v
  have hr := zernikeAnnulusCoordinates_radical_nonneg ⟨q,hq.1.le,ne_of_lt hq.2⟩ v.1
  change (Real.sqrt (1-(v.1 : ℝ)/annulusParameter ⟨q,ne_of_lt hq.2⟩)*Real.cos v.2)^2 +
    (Real.sqrt (1-(v.1 : ℝ)/annulusParameter ⟨q,ne_of_lt hq.2⟩)*Real.sin v.2)^2 ≤ 1
  simp only [mul_pow]
  rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sq_sqrt hr]
  have ht : 0 < annulusParameter ⟨q,ne_of_lt hq.2⟩ :=
    lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have := div_nonneg v.1.property.1 ht.le
  linarith

/-- A polynomial nonnegative on the unit disk has nonnegative annular integral. -/
theorem integral_nonneg_zernikeAnnulusMeasure {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (a b : ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ v : Fin 2 → ℝ, v 0^2+v 1^2 ≤ 1 → 0 ≤ eval v p)
    (_hi : Integrable (fun v ↦ eval v p) (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    0 ≤ ∫ v, eval v p ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_sq_radius_le_one_zernikeAnnulusMeasure hq a b] with v hv
  exact hp v hv

end MvPolynomial
