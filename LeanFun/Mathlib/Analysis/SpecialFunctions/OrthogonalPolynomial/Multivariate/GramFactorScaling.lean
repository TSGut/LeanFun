/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.MeasureModification

/-! # Positive scaling of canonical polynomial Gram factors
Scaling a Gram matrix by a positive constant scales its unique positive upper
triangular factor by the positive square root, and preserves every zero.
Reference: uniqueness of Cholesky factorization.
-/

public section
open MeasureTheory Module Matrix
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] {n : ℕ}

/-- Scaling a nonnegative polynomial density scales every finite Gram matrix. -/
theorem integralGram_withDensity_smul (μ : Measure (σ → ℝ))
    (u : MvPolynomial σ ℝ) (P : Fin n → MvPolynomial σ ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u) {c : ℝ} (hc : 0 ≤ c)
    (hi : ∀ i j, Integrable (fun x => eval x (u*P i)*eval x (P j)) μ := by
      intro i j
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralGram (MvPolynomial.polynomialDensityMeasure ((c • u)) ((μ).comap Subtype.val)) P
      (hP := fun i j => (integrable_mul_withDensity_polynomial_iff (c • u) (P i) (P j)
        (hu.mono (fun x hx => by simpa using mul_nonneg hc hx))).2 (by
          simpa only [smul_eq_C_mul, map_mul, eval_C, mul_assoc] using (hi i j).const_mul c)) =
      c • integralGram (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) P
        (hP := fun i j => (integrable_mul_withDensity_polynomial_iff u (P i) (P j) hu).2 (hi i j)) := by
  have hcu : ∀ᵐ x ∂μ, 0 ≤ eval x (c • u) := by
    filter_upwards [hu] with x hx
    simpa using mul_nonneg hc hx
  have hci (i j) : Integrable (fun x => eval x ((c • u)*P i)*eval x (P j)) μ := by
    simpa only [smul_eq_C_mul, map_mul, eval_C, mul_assoc] using (hi i j).const_mul c
  rw [integralGram_withDensity_polynomial _ _ hcu (hi := hci),
    integralGram_withDensity_polynomial _ _ hu (hi := hi)]
  ext i j
  change integralInner μ (IntegrablePair.of μ ((c • u) * P i) (P j) (h := hci i j)) =
    c * integralInner μ (IntegrablePair.of μ (u * P i) (P j) (h := hi i j))
  simp only [integralInner, smul_eq_C_mul, map_mul, eval_C, mul_assoc, integral_const_mul]

/-- Positive scalar Gram scaling gives exactly positive square-root factor scaling. -/
theorem integralGramFactor_eq_sqrt_smul_of_gram_eq
    (μ ν : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ) (hν : HasFiniteMoments ν)
    (hpμ : HasPositiveDefiniteIntegral μ) (hpν : HasPositiveDefiniteIntegral ν)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis (Fin n) ℝ V)
    {c : ℝ} (hc : 0 < c)
    (hG : integralGram μ (fun i ↦ (b i : MvPolynomial σ ℝ)) =
      c • integralGram ν (fun i ↦ (b i : MvPolynomial σ ℝ))) :
    integralGramFactor μ hμ hpμ b = Real.sqrt c • integralGramFactor ν hν hpν b := by
  obtain ⟨hR, hd, hg⟩ := integralGramFactor_spec ν hν hpν b
  apply integralGramFactor_eq
  · intro i j hij
    change Real.sqrt c * integralGramFactor ν hν hpν b i j = 0
    rw [hR hij, mul_zero]
  · intro i
    exact mul_pos (Real.sqrt_pos.mpr hc) (hd i)
  · rw [hG, hg]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← pow_two, Real.sq_sqrt hc.le]

/-- Positive Gram scaling does not change which factor entries vanish. -/
theorem integralGramFactor_eq_zero_iff_of_gram_scale
    (μ ν : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ) (hν : HasFiniteMoments ν)
    (hpμ : HasPositiveDefiniteIntegral μ) (hpν : HasPositiveDefiniteIntegral ν)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis (Fin n) ℝ V)
    {c : ℝ} (hc : 0 < c)
    (hG : integralGram μ (fun i ↦ (b i : MvPolynomial σ ℝ)) =
      c • integralGram ν (fun i ↦ (b i : MvPolynomial σ ℝ))) (i j : Fin n) :
    integralGramFactor μ hμ hpμ b i j = 0 ↔ integralGramFactor ν hν hpν b i j = 0 := by
  rw [integralGramFactor_eq_sqrt_smul_of_gram_eq μ ν hμ hν hpμ hpν b hc hG]
  change Real.sqrt c * integralGramFactor ν hν hpν b i j = 0 ↔ _
  simp [(Real.sqrt_pos.mpr hc).ne']

end MvPolynomial
