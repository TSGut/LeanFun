/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.EvenMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskOuterMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Deformation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System

/-! # Admissible Jacobi factor measures for disk deformation
The deformed outer factor is finite, atomless and positive on nonzero
polynomials throughout 0<delta<=1. This supplies actual Cartesian source systems.
Reference: Jacobi measures, DLMF Table 18.3.1; Cartesian disk transport.
-/

@[expose] public section
open MeasureTheory Set
namespace Polynomial

/-- Jacobi weights have no atoms, including weights with endpoint singularities. -/
instance (α β : ℝ) : NullSingletonClass (jacobiMeasure α β) := by
  exact nullSingletonClass_openIntervalWeightMeasure (-1) 1 (jacobiWeight α β)

/-- Every admissible Jacobi factor remains polynomially positive after deformation. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_diskDeformed_jacobiMeasure {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasPositiveDefiniteIntegral (diskDeformedMeasure δ ((jacobiMeasure α β).comap Subtype.val)) := by
  let := isFiniteMeasure_jacobiMeasure hα hβ
  have hμ : jacobiMeasure α β ≠ 0 := by
    intro he
    have h := hasPositiveDefiniteIntegral_jacobiMeasure hα hβ 1 one_ne_zero
    rw [he] at h
    simp at h
  exact hasPositiveDefiniteIntegral_diskDeformedMeasure hμ hδ hδ1 (ae_mem_Icc_jacobiMeasure _ _)

end Polynomial
namespace MvPolynomial
open Polynomial

/-- The actual canonical Cartesian system with the deformed Jacobi outer factor. -/
noncomputable def dunklXuDeformedCartesianSystem {β δ : ℝ} (hβ : -1 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
      (jacobiMeasure β β) := by
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isNegInvariant_jacobiMeasure β
  exact cartesianDiskSystem _ _
    (hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure _ _))
    (hasPositiveDefiniteIntegral_diskDeformed_jacobiMeasure hβ' hβ' hδ hδ1)
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure _ _))

end MvPolynomial
