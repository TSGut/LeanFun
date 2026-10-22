/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import LeanFun.Mathlib.MeasureTheory.Measure.NonnegativeDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial density measures on their nonnegative domains

Reference: Gautschi, *Orthogonal Polynomials: Computation and Approximation*,
polynomial modifications of orthogonality measures.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- Weight a measure on the nonnegative locus of a polynomial and return its coordinate measure. -/
noncomputable def polynomialDensityMeasure (p : MvPolynomial σ ℝ)
    (μ : Measure {x : σ → ℝ // 0 ≤ eval x p}) : Measure (σ → ℝ) :=
  Measure.map Subtype.val
    (μ.withDensity (fun x => ENNReal.ofNNReal (NNReal.mk (eval (x : σ → ℝ) p) x.property)))

omit [Fintype σ] in
/-- Evaluation on measurable sets is the nonnegative weighted source measure. -/
theorem polynomialDensityMeasure_apply (p : MvPolynomial σ ℝ)
    (μ : Measure {x : σ → ℝ // 0 ≤ eval x p}) {s : Set (σ → ℝ)} (hs : MeasurableSet s) :
    polynomialDensityMeasure p μ s =
      ∫⁻ x in Subtype.val ⁻¹' s, ENNReal.ofNNReal (NNReal.mk (eval (x : σ → ℝ) p) x.property) ∂μ := by
  rw [polynomialDensityMeasure, Measure.map_apply measurable_subtype_coe hs,
    withDensity_apply _ (measurable_subtype_coe hs)]

/-- Supported real measures transport without loss to a polynomial's nonnegative locus. -/
theorem map_comap_polynomial_nonneg (p : MvPolynomial σ ℝ) (μ : Measure (σ → ℝ))
    (hp : ∀ᵐ x ∂μ, 0 ≤ eval x p) :
    Measure.map (Subtype.val : {x : σ → ℝ // 0 ≤ eval x p} → (σ → ℝ))
      (μ.comap Subtype.val) = μ := by
  have he := map_comap_subtype_coe (s := {x : σ → ℝ | 0 ≤ eval x p})
    (measurableSet_le measurable_const p.continuous_eval.measurable) μ
  exact he.trans (Measure.restrict_eq_self_of_ae_mem hp)


/-- A measurable nonnegative extension transports the typed polynomial density. -/
theorem exists_polynomialDensityMeasure_extension (p : MvPolynomial σ ℝ) :
    ∃ w : (σ → ℝ) → ℝ≥0, Measurable w ∧
      (∀ x (hx : 0 ≤ eval x p), w x = NNReal.mk (eval x p) hx) ∧
      (∀ x, ¬ 0 ≤ eval x p → w x = 0) ∧
      ∀ μ : Measure (σ → ℝ), polynomialDensityMeasure p (μ.comap Subtype.val) =
        μ.withDensity (fun x => (w x : ℝ≥0∞)) :=
  exists_nonnegativeDensity_extension (fun x => eval x p) p.continuous_eval.measurable


end MvPolynomial
