/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Structure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Quadrature

/-!
# Gauss--Jacobi quadrature

For every `α, β > -1`, the degree-`n` Jacobi roots carry positive quadrature
weights and the rule integrates every polynomial of degree below `2*n` exactly.
Reference: DLMF §3.5(v), https://dlmf.nist.gov/3.5#v.
-/

@[expose] public section

open MeasureTheory

namespace Polynomial

/-- The Gauss--Jacobi weight, in the original Jacobi measure normalisation
(DLMF §3.5(v)). -/
noncomputable def jacobiGaussWeight (α β : ℝ) (n : ℕ) (x : ℝ)
    (d : Lagrange.QuadratureInput (jacobiMeasure α β) (jacobi α β n).roots.toFinset id x) : ℝ :=
  Lagrange.quadratureWeight (jacobiMeasure α β) (jacobi α β n).roots.toFinset id x d

/-- Classical Gauss--Jacobi weight integral. -/
theorem jacobiGaussWeight_apply (α β : ℝ) (n : ℕ) (x : ℝ)
    (d : Lagrange.QuadratureInput (jacobiMeasure α β) (jacobi α β n).roots.toFinset id x) :
    jacobiGaussWeight α β n x d =
      ∫ y, (Lagrange.classicalBasis (jacobi α β n).roots.toFinset id x d.basis).eval y
        ∂jacobiMeasure α β := rfl

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
include hα hβ

/-- The rule has precisely `n` distinct nodes (DLMF §3.5(v)). -/
theorem card_jacobiGaussNodes (n : ℕ) : (jacobi α β n).roots.toFinset.card = n :=
  (isOrthogonal_jacobiSequence hα hβ).card_gaussNodes
    (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n

/-- All Gauss--Jacobi nodes lie strictly inside `(-1, 1)` (DLMF §3.5(v)). -/
theorem jacobiGaussNodes_subset_Ioo (n : ℕ) :
    ↑(jacobi α β n).roots.toFinset ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  apply root_jacobi_mem_Ioo hα hβ
  exact (mem_roots ((jacobiSequence hα hβ).ne_zero n)).mp (Multiset.mem_toFinset.mp hx)

/-- Gauss--Jacobi exactness throughout the real orthogonality range (DLMF §3.5(v)). -/
theorem integral_eq_sum_jacobiGaussWeight_mul_eval {n : ℕ} {p : ℝ[X]}
    (hp : p.degree < (2 * n : ℕ)) :
    ∫ x, p.eval x ∂jacobiMeasure α β =
      ∑ x ∈ (jacobi α β n).roots.toFinset, jacobiGaussWeight α β n x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) * p.eval x := by
  simpa [jacobiGaussWeight, Sequence.gaussWeight] using
    (isOrthogonal_jacobiSequence hα hβ).integral_eq_sum_gaussWeight_mul_eval
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hp

/-- Each Gauss--Jacobi weight is strictly positive (DLMF §3.5(v)). -/
theorem jacobiGaussWeight_pos {n : ℕ} {x : ℝ}
    (hx : x ∈ (jacobi α β n).roots.toFinset) : 0 < jacobiGaussWeight α β n x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) := by
  simpa [jacobiGaussWeight, Sequence.gaussWeight] using
    (isOrthogonal_jacobiSequence hα hβ).gaussWeight_pos
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hx

/-- The Gauss--Jacobi weights sum to the total Jacobi mass (DLMF §3.5(v)). -/
theorem sum_jacobiGaussWeight {n : ℕ} (hn : 1 ≤ n) :
    ∑ x ∈ (jacobi α β n).roots.toFinset, jacobiGaussWeight α β n x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) =
      (jacobiMeasure α β).real Set.univ := by
  simpa [jacobiGaussWeight, Sequence.gaussWeight] using
    (isOrthogonal_jacobiSequence hα hβ).sum_gaussWeight
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hn

end Polynomial
