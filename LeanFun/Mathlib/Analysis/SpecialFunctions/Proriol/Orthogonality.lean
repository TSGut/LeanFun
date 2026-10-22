/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.NormBounds

/-! # Orthogonality and norms of Proriol polynomials
The separated Jacobi proof of DLMF 18.37.8. The auxiliary measure retains the
Jacobi affine mass factor, stated explicitly in the norm identity.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Distinct valid triangular indices are orthogonal. -/
theorem integralInner_proriol_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hne : (n,k) ≠ (m,j)) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (proriol α β γ n k) (proriol α β γ m j)) = 0 := by
  by_cases hkj : k=j
  · subst j
    rw [integralInner_proriol_same_inner hα hβ hγ, Polynomial.integralInner,
      integral_mul_jacobi_eq_zero hα (by linarith [Nat.cast_nonneg (α := ℝ) k])]
    · simp
    · intro he
      exact hne (by congr 1; omega)
  · rw [integralInner_proriol_separated hα hβ hγ, Polynomial.integralInner,
      integral_mul_jacobi_eq_zero hβ hγ hkj, mul_zero]

/-- Exact squared norm as a product of two standard Jacobi squared norms. -/
theorem integral_sq_proriol {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k : ℕ) :
    ∫ v, (eval v (proriol α β γ n k))^2 ∂proriolProductMeasure α β γ =
      ((2 : ℝ)^(2*k))⁻¹ *
        (∫ x, (jacobi α (β+γ+2*k+1) (n-k)).eval x ^ 2
          ∂jacobiMeasure α (β+γ+2*k+1)) *
        (∫ z, (jacobi β γ k).eval z ^ 2 ∂jacobiMeasure β γ) := by
  rw [← integralInner_self _ _ (h := (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul _ _), integralInner_proriol_same_inner hα hβ hγ,
    Polynomial.integralInner_self, Polynomial.integralInner_self]

/-- The squared norm is strictly positive throughout the full parameter range. -/
theorem integral_sq_proriol_pos {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k : ℕ) :
    0 < ∫ v, (eval v (proriol α β γ n k))^2 ∂proriolProductMeasure α β γ := by
  rw [integral_sq_proriol hα hβ hγ]
  have houter : -1 < β+γ+2*(k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_pos (mul_pos (by positivity) (integral_sq_jacobi_pos hα houter _))
    (integral_sq_jacobi_pos hβ hγ _)

end MvPolynomial
