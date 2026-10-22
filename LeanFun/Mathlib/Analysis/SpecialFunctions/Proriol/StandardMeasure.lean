/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Density
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Orthogonality

/-! # Standard Proriol measure and norms
The DLMF 18.37.8 measure has weight (1-x)^alpha (x-y)^beta y^gamma on 0<y<x<1.
The affine mass factor is removed from the auxiliary product-coordinate measure.
-/

@[expose] public section
open MeasureTheory Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- The Proriol triangle measure with the standard, unnormalized DLMF weight. -/
noncomputable def proriolMeasure (α β γ : ℝ) : Measure (Fin 2 → ℝ) :=
  ENNReal.ofReal (((2 : ℝ)^(α+2*β+2*γ+3))⁻¹) • proriolProductMeasure α β γ

/-- The standard Proriol measure has all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_proriolMeasure {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) :
    HasFiniteMoments (proriolMeasure α β γ) := by
  intro p
  exact (hasFiniteMoments_proriolProductMeasure hα hβ hγ p).smul_measure ENNReal.ofReal_ne_top

/-- Removing the affine mass factor from an integrable input. -/
theorem integral_proriolMeasure (α β γ : ℝ)
    (f : IntegrableInput (proriolProductMeasure α β γ)) :
    ∫ v, f.val v ∂proriolMeasure α β γ =
      ((2 : ℝ)^(α+2*β+2*γ+3))⁻¹ * ∫ v, f.val v ∂proriolProductMeasure α β γ := by
  rw [proriolMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Polynomial integration is precisely integration against the standard triangle weight. -/
theorem integral_proriolMeasure_density {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂proriolMeasure α β γ =
      ∫ x : Set.Ioo (0 : ℝ) 1, (1-(x : ℝ))^α *
        ∫ y : Set.Ioo (0 : ℝ) (x : ℝ), ((x : ℝ)-(y : ℝ))^β * (y : ℝ)^γ *
          eval (![(x : ℝ),(y : ℝ)] : Fin 2 → ℝ) p := by
  rw [integral_proriolMeasure _ _ _ ⟨_, by
    simpa only [map_one, mul_one] using
      (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul p 1⟩]
  simp only
  rw [integral_proriolProductMeasure_density hα hβ hγ,
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Proriol orthogonality for the standard DLMF triangle measure. -/
theorem integralInner_proriolMeasure_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hne : (n,k) ≠ (m,j)) :
    integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (proriol α β γ n k) (proriol α β γ m j)) = 0 := by
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul _ _⟩]
  change _ * integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) _ _ (h := (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul _ _)) = 0
  rw [integralInner_proriol_eq_zero hα hβ hγ hk hj hne, mul_zero]

/-- Exact squared norm in the standard triangle measure, valid also in degree zero. -/
theorem integral_sq_proriolMeasure {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k : ℕ) :
    ∫ v, (eval v (proriol α β γ n k))^2 ∂proriolMeasure α β γ =
      ((2 : ℝ)^(α+2*β+2*γ+3))⁻¹ * (((2 : ℝ)^(2*k))⁻¹ *
        (∫ x, (jacobi α (β+γ+2*k+1) (n-k)).eval x ^ 2
          ∂jacobiMeasure α (β+γ+2*k+1)) *
        (∫ z, (jacobi β γ k).eval z ^ 2 ∂jacobiMeasure β γ)) := by
  rw [integral_proriolMeasure _ _ _ ⟨_, hasFiniteMoments_proriolProductMeasure hα hβ hγ _⟩]
  simp only
  rw [integral_sq_proriol hα hβ hγ]

/-- Squared norms in the standard measure are positive. -/
theorem integral_sq_proriolMeasure_pos {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k : ℕ) :
    0 < ∫ v, (eval v (proriol α β γ n k))^2 ∂proriolMeasure α β γ := by
  rw [integral_proriolMeasure _ _ _ ⟨_, hasFiniteMoments_proriolProductMeasure hα hβ hγ _⟩]
  simp only
  exact mul_pos (by positivity) (integral_sq_proriol_pos hα hβ hγ n k)

end MvPolynomial
