/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCompleteness

/-! # Polynomial and normalized shifted Jacobi coordinates

The finite algebraic coordinates and the normalized L² basis represent the
same polynomials with explicit norm scaling. Reference: DLMF 18.2(viii).
-/

@[expose] public noncomputable section
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- The shifted Jacobi sequence as an algebraic polynomial basis. -/
def shiftedJacobiBasis : Module.Basis ℕ ℝ ℝ[X] :=
  (shiftedJacobiSequence hα hβ).basis (shiftedJacobiSequence hα hβ).isUnit_leadingCoeff

/-- Algebraic basis vectors are the existing shifted Jacobi polynomials. -/
@[simp] theorem shiftedJacobiBasis_apply (n : ℕ) :
    shiftedJacobiBasis hα hβ n = shiftedJacobi α β n := by
  exact (shiftedJacobiSequence hα hβ).basis_eq_self _ n

/-- Finite shifted Jacobi coordinates reconstruct the original polynomial. -/
theorem linearCombination_shiftedJacobi_repr (p : ℝ[X]) :
    Finsupp.linearCombination ℝ (shiftedJacobi α β)
      ((shiftedJacobiBasis hα hβ).repr p) = p := by
  simpa only [show shiftedJacobi α β = shiftedJacobiBasis hα hβ from
    _root_.funext (fun n ↦ (shiftedJacobiBasis_apply hα hβ n).symm)] using
    (shiftedJacobiBasis hα hβ).linearCombination_repr p

/-- The polynomial representative of the normalized shifted Jacobi Hilbert vector. -/
def normalizedShiftedJacobi (n : ℕ) : ℝ[X] :=
  (Real.sqrt ((shiftedJacobiSequence hα hβ).squaredNorm (unitJacobiMeasure α β) n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ •
    shiftedJacobi α β n

/-- Normalizing at the polynomial level gives exactly the existing Hilbert basis. -/
@[simp] theorem polynomialToL2_normalizedShiftedJacobi (n : ℕ) :
    polynomialToL2 (hasFiniteMoments_unitJacobiMeasure hα hβ)
      (normalizedShiftedJacobi hα hβ n) = hilbertBasisShiftedJacobi hα hβ n := by
  simp only [normalizedShiftedJacobi, map_smul, hilbertBasisShiftedJacobi_apply,
    Sequence.normalizedToL2, shiftedJacobiSequence_apply]

end Polynomial
