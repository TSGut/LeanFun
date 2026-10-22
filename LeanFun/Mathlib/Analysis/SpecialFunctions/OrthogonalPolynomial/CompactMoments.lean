/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Polynomial

/-! # Polynomial moments on a finite interval
A finite measure supported almost everywhere on a compact interval has all
polynomial moments. Reference: Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

public section
open MeasureTheory Set
namespace Polynomial

/-- Finite interval support supplies every polynomial moment. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 70% apply]
theorem hasFiniteMoments_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hx : ∀ᵐ x ∂μ, x ∈ Icc a b) : HasFiniteMoments μ := by
  intro p
  have hi := (p.continuous.pow 2).integrableOn_Icc (μ := μ) (a := a) (b := b)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hx] at hi

end Polynomial
