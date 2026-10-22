/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ClassicalMeasures
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Sequence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.JacobiSpectral

/-! # Chebyshev Gaussian spectral quadrature
Reuse the Jacobi measure bridge and Mathlib's Chebyshev sequence.
Reference: DLMF §3.5(vi).
-/

public section
open Matrix
namespace Polynomial.Chebyshev

/-- All moments exist for the Chebyshev first-kind measure. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_measureT : HasFiniteMoments classicalMeasureT := by
  rw [measureT_eq_jacobiMeasure]
  exact hasFiniteMoments_jacobiMeasure (by norm_num) (by norm_num)

/-- The Chebyshev integral is positive definite on polynomials. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_measureT : HasPositiveDefiniteIntegral classicalMeasureT := by
  rw [measureT_eq_jacobiMeasure]
  exact hasPositiveDefiniteIntegral_jacobiMeasure (by norm_num) (by norm_num)

/-- Chebyshev roots are eigenvalues of the symmetric multiplication section. -/
theorem mem_spectrum_normalizedJacobiMatrix_iff (n : ℕ) (x : ℝ) :
    x ∈ spectrum ℝ ((chebyshevTsequence ℝ).normalizedJacobiMatrix classicalMeasureT n) ↔
      (T ℝ (n : ℕ)).IsRoot x :=
  isOrthogonal_chebyshevTsequence.mem_spectrum_normalizedJacobiMatrix_iff
    hasFiniteMoments_measureT hasPositiveDefiniteIntegral_measureT n x

/-- Chebyshev Gaussian weights from any unit eigenvector, in the original measure. -/
theorem gaussWeight_eq_of_unit_eigenvector {n : ℕ} {x : ℝ}
    (hx : x ∈ (T ℝ (n + 1 : ℕ)).roots.toFinset) (v : Fin (n + 1) → ℝ)
    (hv : (chebyshevTsequence ℝ).normalizedJacobiMatrix classicalMeasureT (n + 1) *ᵥ v = x • v)
    (hvN : ∑ i, v i ^ 2 = 1) :
    (chebyshevTsequence ℝ).gaussWeight classicalMeasureT (n + 1) x (Lagrange.QuadratureInput.ofMoments hasFiniteMoments_measureT (Lagrange.BasisInput.id _ _)) =
      classicalMeasureT.real Set.univ * v 0 ^ 2 :=
  isOrthogonal_chebyshevTsequence.gaussWeight_eq_of_unit_eigenvector
    hasFiniteMoments_measureT hasPositiveDefiniteIntegral_measureT hx v hv hvN

end Polynomial.Chebyshev
