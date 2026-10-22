/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.QuadraticReflection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Positive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.QuadraticSeparation

/-! # Admissibility of quadratic modifications of Cartesian disk measures
Nonnegative diagonal quadratics with nonzero boundary value preserve all moments
and strict polynomial positivity. Reference: polynomial measure modification.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The Cartesian pushforward is supported on the closed unit disk. -/
theorem ae_sq_add_sq_le_one_cartesianDiskMeasure {μ ν : Measure ℝ} [SFinite ν]
    (_hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), (v 0) ^ 2 + (v 1) ^ 2 ≤ 1 := by
  unfold cartesianDiskMeasure
  apply (ae_map_iff continuous_diskCoordinates.measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).2
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hz] with v hv
  change (v.1 : ℝ)^2+(Real.sqrt (1-(v.1 : ℝ)^2)*v.2)^2 ≤ 1
  rw [mul_pow, Real.sq_sqrt (diskCoordinates_sq_nonneg v.1)]
  have hz2 : v.2^2 ≤ 1 := by nlinarith [hv.1,hv.2]
  nlinarith [sq_nonneg (v.1 : ℝ),
    mul_nonneg (diskCoordinates_sq_nonneg v.1) (show 0 ≤ 1-v.2^2 by linarith)]

/-- The elementary three scalar inequalities give a nonnegative quadratic density. -/
theorem ae_coordinateQuadratic_nonneg_cartesianDiskMeasure {μ ν : Measure ℝ}
    [SFinite ν] (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1) (A B C : ℝ)
    (hA : 0 ≤ A) (hAB : 0 ≤ A + B) (hAC : 0 ≤ A + C) :
    ∀ᵐ v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), 0 ≤ eval v (coordinateQuadratic A B C) := by
  filter_upwards [ae_sq_add_sq_le_one_cartesianDiskMeasure hx hz] with v hv
  simpa [coordinateQuadratic] using
    (quadraticDisk_nonneg_iff A B C).2 ⟨hA, hAB, hAC⟩ (v 0) (v 1) hv

/-- A nonzero value at (1,0) certifies that the quadratic polynomial is nonzero. -/
theorem coordinateQuadratic_ne_zero_of_boundary_ne_zero (A B C : ℝ) (hAB : A + B ≠ 0) :
    coordinateQuadratic A B C ≠ 0 := by
  intro he
  have h := congrArg (eval (![1, 0] : Fin 2 → ℝ)) he
  apply hAB
  simpa [coordinateQuadratic] using h

/-- Every admissible nonzero quadratic modification remains positive on nonzero polynomials. -/
theorem CartesianDiskSystem.hasPositiveDefiniteIntegral_coordinateQuadratic
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1) (A B C : ℝ)
    (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) :
    MvPolynomial.HasPositiveDefiniteIntegral (MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) (((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))).comap Subtype.val)) :=
  (S.hasPositiveDefiniteIntegral hx hz).withDensity_polynomial
    (hasFiniteMoments_cartesianDiskMeasure hx hz) (coordinateQuadratic A B C)
    (coordinateQuadratic_ne_zero_of_boundary_ne_zero A B C hAB.ne')
    (ae_coordinateQuadratic_nonneg_cartesianDiskMeasure hx hz A B C hA hAB.le hAC)

end MvPolynomial
