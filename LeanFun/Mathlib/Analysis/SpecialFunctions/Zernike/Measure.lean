/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitInterval
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanFun.Mathlib.MeasureTheory.Measure.ClassicalProduct
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Polar product coordinates for real Zernike polynomials
The auxiliary product measure uses squared radius and preserves Jacobi mass.
The standard disk density and its normalization are established separately.
Reference: DLMF 18.37.1–2 and MultivariateOrthogonalPolynomials.jl, disk.jl.
-/

@[expose] public section
open MeasureTheory Set Polynomial
open scoped NNReal
namespace MvPolynomial

/-- Polar coordinates on the full nonnegative squared-radius domain. -/
noncomputable def zernikeCoordinates (v : ℝ≥0 × ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt (v.1 : ℝ)*Real.cos v.2, Real.sqrt (v.1 : ℝ)*Real.sin v.2]

/-- The polar coordinate map is continuous at the disk center as well. -/
theorem continuous_zernikeCoordinates : Continuous zernikeCoordinates := by
  unfold zernikeCoordinates
  simp_rw [← Real.coe_sqrt]
  fun_prop

/-- The auxiliary squared-radius/angle pushforward, before removing the Jacobi mass factor. -/
noncomputable def zernikeProductMeasure (a b : ℝ) : Measure (Fin 2 → ℝ) :=
  let μ := Measure.comap NNReal.toReal (unitJacobiMeasure b a)
  let ν := ProductMeasureInput.ofSFinite μ (volume.restrict (Ioo (-Real.pi) Real.pi))
  Measure.map zernikeCoordinates (μ.prod ν.inner)

private theorem map_comap_nonnegative_unitJacobiMeasure (a b : ℝ) :
    (Measure.comap NNReal.toReal (unitJacobiMeasure b a)).map NNReal.toReal =
      unitJacobiMeasure b a := by
  have hμ : ∀ᵐ x ∂unitJacobiMeasure b a, x ∈ Ici (0 : ℝ) :=
    (ae_mem_Icc_unitJacobiMeasure b a).mono (fun _ hx ↦ hx.1)
  have he := map_comap_subtype_coe (s := Ici (0 : ℝ))
    (μ := unitJacobiMeasure b a) measurableSet_Ici
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at he
  exact he

/-- Continuous disk functions pull back to integrable functions on the compact parameter support. -/
theorem integrable_zernikeProductMeasure {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (zernikeProductMeasure a b) := by
  let := isFiniteMeasure_unitJacobiMeasure hb ha
  rw [zernikeProductMeasure, integrable_map_measure hf.aestronglyMeasurable
    continuous_zernikeCoordinates.measurable.aemeasurable]
  have hi := (hf.comp continuous_zernikeCoordinates).continuousOn.integrableOn_compact
    (μ := (Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0 : NNReal) 1 ×ˢ Icc (-Real.pi) Real.pi))
  have hr : ∀ᵐ r ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a), r ∈ Icc (0 : NNReal) 1 := by
    have hh := ae_of_ae_map (μ := Measure.comap NNReal.toReal (unitJacobiMeasure b a))
      (f := NNReal.toReal) (by fun_prop)
      (show ∀ᵐ x ∂(Measure.comap NNReal.toReal (unitJacobiMeasure b a)).map NNReal.toReal,
        x ∈ Icc (0 : ℝ) 1 by rw [map_comap_nonnegative_unitJacobiMeasure]; exact ae_mem_Icc_unitJacobiMeasure b a)
    exact hh.mono (fun r hr ↦ ⟨bot_le, hr.2⟩)
  have hs : ∀ᵐ v ∂(Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)),
      v ∈ Icc (0 : NNReal) 1 ×ˢ Icc (-Real.pi) Real.pi := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hr,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)] with v hv hθ
    exact ⟨hv, hθ.1.le, hθ.2.le⟩
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi

/-- The polar product measure has all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_zernikeProductMeasure {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    HasFiniteMoments (zernikeProductMeasure a b) := by
  intro p
  exact integrable_zernikeProductMeasure ha hb (p.continuous_eval.pow 2)

/-- The auxiliary measure has finite total mass. -/
theorem isFiniteMeasure_zernikeProductMeasure {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IsFiniteMeasure (zernikeProductMeasure a b) :=
  (hasFiniteMoments_zernikeProductMeasure ha hb).isFiniteMeasure

end MvPolynomial
