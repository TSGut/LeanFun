/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskLift
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import LeanFun.Mathlib.MeasureTheory.Measure.ClassicalProduct
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.FunProp

/-!
# Cartesian disk coordinates

The square-to-disk map is shared by classical and modified Cartesian families.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Set
namespace MvPolynomial

/-- Cartesian coordinates on the full classical strip. -/
noncomputable def diskCoordinates (v : Icc (-1 : ℝ) 1 × ℝ) : Fin 2 → ℝ :=
  ![(v.1 : ℝ), Real.sqrt (1-(v.1 : ℝ)^2)*v.2]

theorem continuous_diskCoordinates : Continuous diskCoordinates := by
  unfold diskCoordinates
  fun_prop

theorem diskCoordinates_sq_nonneg (x : Icc (-1 : ℝ) 1) : 0 ≤ 1-(x : ℝ)^2 := by
  nlinarith [x.property.1,x.property.2]

/-- Pushforward of an interval outer measure and an unrestricted inner measure. -/
noncomputable def cartesianDiskMeasure (μ : Measure (Icc (-1 : ℝ) 1)) (ν : ProductMeasureInput (β := ℝ) μ) : Measure (Fin 2 → ℝ) :=
  Measure.map diskCoordinates (μ.prod ν.inner)

theorem cartesianDiskMeasure_integral (μ : Measure (Icc (-1 : ℝ) 1)) (ν : ProductMeasureInput (β := ℝ) μ)
    (f : IntegrableInput (cartesianDiskMeasure μ ν)) :
    Integrable (fun v ↦ f.val (diskCoordinates v)) (μ.prod ν.inner) ∧
      (∫ v, f.val v ∂cartesianDiskMeasure μ ν) = ∫ v, f.val (diskCoordinates v) ∂μ.prod ν.inner := by
  constructor
  · exact (integrable_map_measure f.integrable.aestronglyMeasurable
      continuous_diskCoordinates.measurable.aemeasurable).mp f.integrable
  · exact integral_map continuous_diskCoordinates.measurable.aemeasurable f.integrable.aestronglyMeasurable

end MvPolynomial
