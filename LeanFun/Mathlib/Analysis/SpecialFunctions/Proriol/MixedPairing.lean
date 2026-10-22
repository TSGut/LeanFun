/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MeasureModification

import Mathlib.Topology.Algebra.Polynomial

/-! # Inner-index sparsity of Proriol measure conversion
Changing the outer parameter preserves the inner Jacobi orthogonality.
Reference: DLMF 18.37.7–8 and separated measure modification.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Arbitrary outer parameters leave the inner index sectors orthogonal. -/
theorem integralInner_proriol_mixed_outer_eq_zero {η β γ : ℝ}
    (hη : -1 < η) (hβ : -1 < β) (hγ : -1 < γ) (α α' : ℝ)
    (n k m j : ℕ) (hkj : k ≠ j) :
    integralInner (proriolMeasure η β γ) (IntegrablePair.of (proriolMeasure η β γ) (proriol α β γ n k) (proriol α' β γ m j)) = 0 := by
  let := isFiniteMeasure_unitJacobiMeasure hη (show -1 < β+γ+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hβ hγ
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hη hβ hγ).integrable_mul _ _⟩]
  simp only
  apply mul_eq_zero_of_right
  have hi := (koornwinderMeasure_integral_univ (fun x => x) continuous_id
    (unitJacobiMeasure η (β+γ+1)) (unitJacobiMeasure β γ)
    ⟨fun v ↦ eval v (proriol α β γ n k * proriol α' β γ m j), by
      simpa only [proriolProductMeasure, map_one, mul_one] using
        (hasFiniteMoments_proriolProductMeasure hη hβ hγ).integrable_mul (proriol α β γ n k * proriol α' β γ m j) 1⟩).2
  simp only [map_mul] at hi
  rw [proriolProductMeasure, hi]
  have he : (∫ v, eval ((![v.1, v.1*v.2] : Fin 2 → ℝ)) (proriol α β γ n k) *
      eval ((![v.1, v.1*v.2] : Fin 2 → ℝ)) (proriol α' β γ m j)
      ∂(unitJacobiMeasure η (β+γ+1)).prod (unitJacobiMeasure β γ)) =
      (∫ x, (shiftedJacobi α (β+γ+2*k+1) (n-k)).eval x *
        (shiftedJacobi α' (β+γ+2*j+1) (m-j)).eval x * x^(k+j)
        ∂unitJacobiMeasure η (β+γ+1)) *
      Polynomial.integralInner (unitJacobiMeasure β γ) (Polynomial.IntegrablePair.of (unitJacobiMeasure β γ) (shiftedJacobi β γ k) (shiftedJacobi β γ j)) := by
    rw [Polynomial.integralInner, ← integral_prod_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [eval_proriol_scaled, eval_proriol_scaled, pow_add]
    ring
  rw [he, integralInner_shiftedJacobi β γ k j
    (hi := (hasFiniteMoments_jacobiMeasure hβ hγ).integrable_mul _ _), Polynomial.integralInner,
    integral_mul_jacobi_eq_zero hβ hγ hkj, mul_zero]

/-- Integer alpha raising has both finite total bandwidth and diagonal inner blocks. -/
theorem integralInner_proriol_alpha_shift_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (r : ℕ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hgap : k ≠ j ∨ n < m ∨ m+r < n) :
    integralInner (proriolMeasure (α+r) β γ) (IntegrablePair.of (proriolMeasure (α+r) β γ) (proriol α β γ n k) (proriol (α+r) β γ m j) (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hβ hγ).integrable_mul _ _)) = 0 := by
  rcases hgap with h | h
  · exact integralInner_proriol_mixed_outer_eq_zero
      (by linarith [Nat.cast_nonneg (α := ℝ) r]) hβ hγ _ _ _ _ _ _ h
  · exact integralInner_proriol_alpha_shift_eq_zero_of_total_gap hα hβ hγ r hk hj h

end MvPolynomial
