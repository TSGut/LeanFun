/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Legendre.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Interlacing
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

/-!
# Legendre structure from general orthogonal-polynomial theory

Positivity of the unit-weight pairing, recurrence, kernels, and zeros.
References: DLMF 18.2(iv), 18.2(vi), and Table 18.9.1.
-/
public section
open MeasureTheory Set
namespace Polynomial

private theorem exists_eval_ne_zero_Ioo {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, p.eval x ≠ 0 := by
  by_contra h
  push Not at h
  exact hp (p.eq_zero_of_infinite_isRoot ((Set.Ioo_infinite hab).mono h))

/-- The Legendre integral pairing is positive definite (DLMF 18.2(i)). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_legendreMeasure : HasPositiveDefiniteIntegral legendreMeasure := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  obtain ⟨x, hx, hpx⟩ := exists_eval_ne_zero_Ioo hp (show (-1 : ℝ) < 1 by norm_num)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (-1 : ℝ) < 1 by norm_num) continuous_const.continuousOn
    (p.continuous.pow 2).continuousOn (fun _ _ ↦ sq_nonneg _) ⟨x, Ioo_subset_Icc_self hx, sq_pos_of_ne_zero hpx⟩
  simpa only [intervalIntegral.integral_zero, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    legendreMeasure, MeasureTheory.integral_zero, Pi.pow_apply] using hi

/-- The Legendre weight is finite (DLMF Table 18.3.1). -/
instance isFiniteMeasure_legendreMeasure : IsFiniteMeasure legendreMeasure :=
  hasFiniteMoments_legendreMeasure.isFiniteMeasure

/-- The known Legendre squared norms in the general sequence API (DLMF Table 18.3.1). -/
theorem squaredNorm_legendreSequence (n : ℕ) :
    (legendreSequence ℝ).squaredNorm legendreMeasure n (Polynomial.Sequence.IntegrableSquare.of _ _) = 2 / (2 * (n : ℝ) + 1) := by
  simpa only [Sequence.squaredNorm, integralInner_self, legendreSequence_apply]
    using integral_sq_legendre_measure n

/-- Legendre polynomials split into real linear factors (DLMF 18.2(vi)). -/
theorem splits_legendre (n : ℕ) : (legendre ℝ n).Splits :=
  isOrthogonal_legendreSequence.splits hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n

/-- A Legendre polynomial has exactly its degree many real roots (DLMF 18.2(vi)). -/
theorem card_roots_legendre (n : ℕ) : (legendre ℝ n).roots.card = n :=
  isOrthogonal_legendreSequence.card_roots hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n

/-- Every Legendre root is simple (DLMF 18.2(vi)). -/
theorem separable_legendre (n : ℕ) : (legendre ℝ n).Separable :=
  isOrthogonal_legendreSequence.separable hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n

end Polynomial
