/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Independent reflections of product measures
Even factor measures preserve the product under reflection in one coordinate.
Reference: change of variables for product measures.
-/

public section
namespace MeasureTheory

/-- An even first factor makes the product measure invariant under first-coordinate
reflection. Reference: change of variables for product measures. -/
theorem map_prod_neg_left (μ ν : Measure ℝ) [SFinite ν] [μ.IsNegInvariant] :
    Measure.map (fun z : ℝ × ℝ => (-z.1,z.2)) (μ.prod ν) = μ.prod ν := by
  change Measure.map (Prod.map Neg.neg id) (μ.prod ν) = _
  rw [← Measure.map_prod_map μ ν measurable_neg measurable_id]
  simp [Measure.map_neg_eq_self]

/-- An even second factor makes the product measure invariant under second-coordinate
reflection. Reference: change of variables for product measures. -/
theorem map_prod_neg_right (μ ν : Measure ℝ) [SFinite ν] [ν.IsNegInvariant] :
    Measure.map (fun z : ℝ × ℝ => (z.1,-z.2)) (μ.prod ν) = μ.prod ν := by
  change Measure.map (Prod.map id Neg.neg) (μ.prod ν) = _
  rw [← Measure.map_prod_map μ ν measurable_id measurable_neg]
  simp [Measure.map_neg_eq_self]


end MeasureTheory
