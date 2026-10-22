/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Measure

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The Gegenbauer measure
The ultraspherical weight is identified with the symmetric Jacobi weight on the
orthogonality interval. This transfers the measure theory, including singular
endpoint weights. Reference: DLMF Table 18.3.1.
-/

@[expose] public section
open MeasureTheory Set Real
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial


/-- The ultraspherical weight on its classical open domain (DLMF Table 18.3.1). -/
noncomputable def gegenbauerWeight (lam : ℝ) : C(Ioo (-1 : ℝ) 1, ℝ≥0) :=
  jacobiWeight (lam - 1 / 2) (lam - 1 / 2)

/-- The Gegenbauer measure, obtained from its domain-typed density. -/
noncomputable def gegenbauerMeasure (lam : ℝ) : Measure ℝ :=
  openIntervalWeightMeasure (-1) 1 (gegenbauerWeight lam)


/-- Equality with the symmetric Jacobi measure (DLMF Table 18.3.1). -/
theorem gegenbauerMeasure_eq_jacobiMeasure (lam : ℝ) :
    gegenbauerMeasure lam = jacobiMeasure (lam - 1 / 2) (lam - 1 / 2) := rfl

/-- The density formula at an interior point has a strictly positive power base. -/
theorem gegenbauerWeight_apply (lam : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (gegenbauerWeight lam x : ℝ) = (1 - (x : ℝ) ^ 2) ^ (lam - 1 / 2) := by
  change (jacobiWeight (lam - 1 / 2) (lam - 1 / 2) x : ℝ) = _
  rw [jacobiWeight_apply, ← Real.mul_rpow
    (by linarith [x.property.2] : 0 ≤ 1 - (x : ℝ))
    (by linarith [x.property.1] : 0 ≤ 1 + (x : ℝ))]
  congr 1
  ring


/-- Integrability is equivalent to integrability of the classical density product. -/
theorem integrable_gegenbauerMeasure_iff (lam : ℝ) (f : ℝ → ℝ) :
    Integrable f (gegenbauerMeasure lam) ↔
      Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (gegenbauerWeight lam x : ℝ) * f x) volume :=
  integrable_openIntervalWeightMeasure_iff _ _ _ _

/-- Integral transport for an input bundled with its integrability witness. -/
theorem integral_gegenbauerMeasure (lam : ℝ)
    (f : IntegrableInput (gegenbauerMeasure lam)) :
    ∫ x, f.val x ∂gegenbauerMeasure lam =
      ∫ x : Ioo (-1 : ℝ) 1, (gegenbauerWeight lam x : ℝ) * f.val x :=
  integral_openIntervalWeightMeasure _ _ _ _

/-- Integrability of the open-domain ultraspherical density in its full range. -/
theorem integrable_gegenbauerWeight {lam : ℝ} (hlam : -(1 / 2) < lam) :
    Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (gegenbauerWeight lam x : ℝ)) volume :=
  integrable_jacobiWeight (by linarith) (by linarith)


/-- Continuous functions on the closed interval are integrable (DLMF Table 18.3.1). -/
theorem integrable_gegenbauerMeasure {lam : ℝ} (hlam : -(1 / 2) < lam)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    Integrable f (gegenbauerMeasure lam) := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  exact integrable_jacobiMeasure (by linarith) (by linarith) hf

/-- All polynomial moments are finite (DLMF Table 18.3.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_gegenbauerMeasure {lam : ℝ} (hlam : -(1 / 2) < lam) :
    HasFiniteMoments (gegenbauerMeasure lam) := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  exact hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)

/-- The Gegenbauer measure is finite (DLMF Table 18.3.1). -/
theorem isFiniteMeasure_gegenbauerMeasure {lam : ℝ} (hlam : -(1 / 2) < lam) :
    IsFiniteMeasure (gegenbauerMeasure lam) :=
  (hasFiniteMoments_gegenbauerMeasure hlam).isFiniteMeasure

/-- The measure is concentrated on the open interval (DLMF Table 18.3.1). -/
theorem ae_mem_Ioo_gegenbauerMeasure (lam : ℝ) :
    ∀ᵐ x ∂gegenbauerMeasure lam, x ∈ Ioo (-1) 1 := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  exact ae_mem_Ioo_jacobiMeasure _ _

/-- The polynomial integral pairing is positive definite (DLMF Table 18.3.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_gegenbauerMeasure {lam : ℝ}
    (hlam : -(1 / 2) < lam) : HasPositiveDefiniteIntegral (gegenbauerMeasure lam) := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  exact hasPositiveDefiniteIntegral_jacobiMeasure (by linarith) (by linarith)

/-- The symmetric Jacobi identity is an equality of domain-typed weights. -/
theorem gegenbauerWeight_eq_jacobiWeight (lam : ℝ) :
    gegenbauerWeight lam = jacobiWeight (lam - 1 / 2) (lam - 1 / 2) := rfl

/-- The Gegenbauer measure is s-finite for every real parameter. -/
theorem sFinite_gegenbauerMeasure (lam : ℝ) : SFinite (gegenbauerMeasure lam) :=
  sFinite_openIntervalWeightMeasure (-1) 1 (gegenbauerWeight lam)

/-- The Gegenbauer measure has no atoms for every real parameter. -/
theorem nullSingletonClass_gegenbauerMeasure (lam : ℝ) :
    NullSingletonClass (gegenbauerMeasure lam) :=
  nullSingletonClass_openIntervalWeightMeasure (-1) 1 (gegenbauerWeight lam)

end Polynomial
