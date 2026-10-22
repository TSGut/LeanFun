/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Quadrature
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.JacobiSpectral

/-! # Spectral representation of Gauss--Jacobi quadrature
These specializations retain the original Jacobi measure mass.
Reference: DLMF §3.5(vi).
-/

public section
open Matrix
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- Gauss--Jacobi nodes are the spectrum of the normalized Jacobi section. -/
theorem mem_spectrum_jacobi_iff (n : ℕ) (x : ℝ) :
    x ∈ spectrum ℝ ((jacobiSequence hα hβ).normalizedJacobiMatrix (jacobiMeasure α β) n) ↔
      (jacobi α β n).IsRoot x :=
  (isOrthogonal_jacobiSequence hα hβ).mem_spectrum_normalizedJacobiMatrix_iff
    (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n x

/-- Golub--Welsch for Jacobi weights throughout α,β>-1. -/
theorem jacobi_golubWelsch {n : ℕ} {x : ℝ}
    (hx : x ∈ (jacobi α β (n + 1)).roots.toFinset) :
    ∃ v : Fin (n + 1) → ℝ,
      (∑ i, v i ^ 2 = 1) ∧
      (jacobiSequence hα hβ).normalizedJacobiMatrix (jacobiMeasure α β) (n + 1) *ᵥ v = x • v ∧
      jacobiGaussWeight α β (n + 1) x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) = (jacobiMeasure α β).real Set.univ * v 0 ^ 2 := by
  simpa only [jacobiGaussWeight, Sequence.gaussWeight, jacobiSequence_apply] using
    (isOrthogonal_jacobiSequence hα hβ).golubWelsch
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hx

/-- The Jacobi weight formula holds for any normalized eigenvector. -/
theorem jacobiGaussWeight_eq_of_unit_eigenvector {n : ℕ} {x : ℝ}
    (hx : x ∈ (jacobi α β (n + 1)).roots.toFinset) (v : Fin (n + 1) → ℝ)
    (hv : (jacobiSequence hα hβ).normalizedJacobiMatrix (jacobiMeasure α β) (n + 1) *ᵥ v =
      x • v) (hvN : ∑ i, v i ^ 2 = 1) :
    jacobiGaussWeight α β (n + 1) x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) = (jacobiMeasure α β).real Set.univ * v 0 ^ 2 := by
  simpa only [jacobiGaussWeight, Sequence.gaussWeight, jacobiSequence_apply] using
    (isOrthogonal_jacobiSequence hα hβ).gaussWeight_eq_of_unit_eigenvector
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hx v hv hvN

end Polynomial
