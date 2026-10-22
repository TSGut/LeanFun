/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalSequence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.HilbertBasis
import Mathlib.Topology.Algebra.Polynomial

/-! # Complete normalized shifted Jacobi bases

Affine transport preserves positivity; compact support supplies polynomial
density. Reference: DLMF Table 18.3.1 and 18.2(viii).
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Polynomial

/-- Strict positivity of polynomial squares for the affine Jacobi measure. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_unitJacobiMeasure {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) : HasPositiveDefiniteIntegral (unitJacobiMeasure α β) := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  let q : ℝ[X] := p.comp ((X+1)*C (1/2))
  have hq : q ≠ 0 := by
    intro hz
    apply hp
    apply Polynomial.funext
    intro x
    have he := congrArg (fun r : ℝ[X] ↦ r.eval (2*x-1)) hz
    simpa only [q, eval_comp, eval_mul, eval_add, eval_X, eval_one, eval_C, eval_zero,
      show (2*x-1+1)*(1/2 : ℝ)=x by ring] using he
  have h := hasPositiveDefiniteIntegral_jacobiMeasure hα hβ q hq
  rw [integral_unitJacobiMeasure α β ⟨fun x ↦ p.eval x ^ 2,
    hasFiniteMoments_unitJacobiMeasure hα hβ p⟩]
  simpa [q, eval_comp, div_eq_mul_inv] using h

/-- The normalized shifted Jacobi sequence is a Hilbert basis on the unit interval. -/
def hilbertBasisShiftedJacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (unitJacobiMeasure α β)) :=
  (isOrthogonal_shiftedJacobiSequence hα hβ).hilbertBasis
    (hasFiniteMoments_unitJacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_unitJacobiMeasure hα hβ)
    (polynomialToL2_denseRange (hasFiniteMoments_unitJacobiMeasure hα hβ) 0 1
      (ae_mem_Icc_unitJacobiMeasure α β))

/-- The basis vectors are the existing shifted polynomials normalized by their squared norms. -/
@[simp] theorem hilbertBasisShiftedJacobi_apply {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) : hilbertBasisShiftedJacobi hα hβ n =
      (shiftedJacobiSequence hα hβ).normalizedToL2
        (hasFiniteMoments_unitJacobiMeasure hα hβ)
        ⟨n, Sequence.squaredNorm_pos (hasPositiveDefiniteIntegral_unitJacobiMeasure hα hβ)
          (shiftedJacobiSequence hα hβ) n⟩ :=
  (isOrthogonal_shiftedJacobiSequence hα hβ).hilbertBasis_apply _ _ _ n

end Polynomial
