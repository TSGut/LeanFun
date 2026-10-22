/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Multiplication
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates

/-! # Multiplication coefficients in the standard Proriol normalization
Projection divides by the target squared norm. Reference: DLMF 18.37 and the
multivariate three-term recurrence.
-/

@[expose] public section
open MeasureTheory
namespace MvPolynomial

/-- Classical mixed-pairing and nonzero target-norm data for one multiplication entry. -/
structure ProriolMultiplicationInput (α β γ : ℝ) (coord : Fin 2) (n k m j : ℕ) : Prop where
  mixed : Integrable (fun x => eval x (X coord * proriol α β γ n k)*eval x (proriol α β γ m j))
    (proriolMeasure α β γ)
  square : Integrable (fun x => (eval x (proriol α β γ m j))^2) (proriolMeasure α β γ)
  positive : 0 < ∫ x, (eval x (proriol α β γ m j))^2 ∂proriolMeasure α β γ

/-- The full orthogonality range supplies every classical Proriol multiplication entry. -/
theorem ProriolMultiplicationInput.of_neg_one_lt {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (coord : Fin 2) (n k m j : ℕ) :
    ProriolMultiplicationInput α β γ coord n k m j :=
  ⟨(hasFiniteMoments_proriolMeasure hα hβ hγ).integrable_mul _ _,
    hasFiniteMoments_proriolMeasure hα hβ hγ _, integral_sq_proriolMeasure_pos hα hβ hγ m j⟩

/-- The classical coefficient of the target Proriol polynomial in coordinate multiplication. -/
noncomputable def proriolMultiplicationEntry (α β γ : ℝ) (coord : Fin 2)
    (n k m j : ℕ) (d : ProriolMultiplicationInput α β γ coord n k m j := by
      exact ProriolMultiplicationInput.of_neg_one_lt (by assumption) (by assumption) (by assumption) _ _ _ _ _) : ℝ :=
  integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ)
    (X coord * proriol α β γ n k) (proriol α β γ m j) d.mixed) /
    (∫ v, (eval v (proriol α β γ m j))^2 ∂proriolMeasure α β γ)

/-- The nonzero target norm recovers the classical mixed pairing. -/
theorem proriolMultiplicationEntry_mul_norm (α β γ : ℝ) (coord : Fin 2)
    (n k m j : ℕ) (d : ProriolMultiplicationInput α β γ coord n k m j) :
    proriolMultiplicationEntry α β γ coord n k m j d *
      (∫ v, (eval v (proriol α β γ m j))^2 ∂proriolMeasure α β γ) =
    integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ)
      (X coord * proriol α β γ n k) (proriol α β γ m j) d.mixed) :=
  div_mul_cancel₀ _ d.positive.ne'

/-- These entries agree with coordinates in any containing complete degree space. -/
theorem proriolMultiplicationEntry_eq_repr {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (coord : Fin 2) (n k N : ℕ)
    (p : restrictTotalDegree (Fin 2) ℝ N) (hp : (p : MvPolynomial (Fin 2) ℝ) =
      X coord * proriol α β γ n k)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    proriolMultiplicationEntry α β γ coord n k (i.1 0+i.1 1) (i.1 1) =
      (proriolDegreeBasis hα hβ hγ N).repr p i := by
  rw [proriolDegreeBasis_repr]
  simp only [hp]
  rfl

/-- Block tridiagonality and the exact inner-index support hold for the actual coefficients. -/
theorem proriolMultiplicationEntry_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (coord : Fin 2)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hgap : (n+1 < m ∨ m+1 < n) ∨ (coord = 0 ∧ k ≠ j) ∨
      (coord = 1 ∧ (k+1 < j ∨ j+1 < k))) :
    proriolMultiplicationEntry α β γ coord n k m j = 0 := by
  have hz : integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (X coord * proriol α β γ n k) (proriol α β γ m j)) = 0 := by
    rcases hgap with h | ⟨hc,h⟩ | ⟨hc,h⟩
    · exact integralInner_X_mul_proriol_eq_zero_of_total_gap hα hβ hγ coord hk hj h
    · subst coord
      exact integralInner_X_zero_mul_proriol_eq_zero hα hβ hγ n k m j h
    · subst coord
      exact integralInner_X_one_mul_proriol_eq_zero hα hβ hγ n k m j h
  unfold proriolMultiplicationEntry
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul _ _⟩]
  change (_ * integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) _ _)) / _ = 0
  rw [hz, mul_zero, zero_div]

end MvPolynomial
