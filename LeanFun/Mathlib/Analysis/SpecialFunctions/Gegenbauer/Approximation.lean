/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Completeness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Norm
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UniformConvergence

/-!
# Weighted L² and uniform approximation by Gegenbauer expansions

The Jacobi bridge transfers the Christoffel kernel exactly: its scaling factors
cancel against the squared norms. Negative admissible parameters are included;
zero is excluded because it does not give a polynomial basis.
References: DLMF 18.7.1, 18.18; ATAP, Chapters 8 and 16.
-/

public section
open Real Complex MeasureTheory Set Filter
namespace Polynomial
variable {lam : ℝ} (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0)
include hlam hzero

/-- The Gegenbauer reproducing kernel is the symmetric Jacobi kernel. -/
theorem gegenbauer_kernel_eq_jacobi (N : ℕ) (x y : ℝ) :
    (gegenbauerSequence hlam hzero).kernel (gegenbauerMeasure lam) N x y (Polynomial.Sequence.KernelInput.of _ _ _ (hi := fun _ => (hasFiniteMoments_gegenbauerMeasure hlam).integrable_mul _ _)) =
      (jacobiSequence (show -1 < lam - 1 / 2 by linarith)
        (show -1 < lam - 1 / 2 by linarith)).kernel
        (jacobiMeasure (lam - 1 / 2) (lam - 1 / 2)) N x y (Polynomial.Sequence.KernelInput.of _ _ _ (hi := fun _ => (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _) (_hn := fun k => (Sequence.squaredNorm_pos
            (hasPositiveDefiniteIntegral_jacobiMeasure (by linarith) (by linarith)) _ k).ne')) := by
  rw [Sequence.kernel_of_positive (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
    (gegenbauerSequence hlam hzero),
    Sequence.kernel_of_positive (hasPositiveDefiniteIntegral_jacobiMeasure
      (show -1 < lam - 1 / 2 by linarith) (show -1 < lam - 1 / 2 by linarith))
      (jacobiSequence (show -1 < lam - 1 / 2 by linarith) (show -1 < lam - 1 / 2 by linarith))]
  simp only [gegenbauerSequence_apply, jacobiSequence_apply,
    squaredNorm_gegenbauerSequence, squaredNorm_jacobiSequence]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_sq_gegenbauer_eq_jacobi hlam, gegenbauer_eq_jacobi_mul hlam]
  simp only [eval_mul, eval_C]
  have hc := gegenbauer_jacobi_factor_ne_zero hlam hzero n
  have hn := (integral_sq_jacobi_pos (by linarith : -1 < lam - 1 / 2)
    (by linarith : -1 < lam - 1 / 2) n).ne'
  generalize (ascPochhammer ℝ n).eval (2 * lam) /
    (ascPochhammer ℝ n).eval (lam + 1 / 2) = c at *
  field_simp [hc, hn]

/-- Gegenbauer partial sums inherit the geometric weighted L² error bound. -/
theorem norm_sub_sum_gegenbauerCoefficient_le_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (gegenbauerMeasure lam))
    (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = (F x).re) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1), (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) •
      polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam i)‖ ≤
      √((gegenbauerMeasure lam).real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  simpa only [Sequence.integralCoefficient, squaredNorm_gegenbauerSequence, gegenbauerSequence_apply,
    gegenbauerCoefficient, IntegralCoefficientInput.ofGegenbauerL2, IntegralCoefficientInput.ofL2] using
    (isOrthogonal_gegenbauerSequence hlam hzero).norm_sub_sum_integralCoefficient_le_of_analytic
      (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
      ((ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Ioo_subset_Icc_self hx))
      hρ hF hM f hf N

/-- A uniform Gegenbauer error bound throughout lam > -1/2, lam nonzero,
with the same nonsharp polynomial factor as its Jacobi family. -/
theorem norm_sub_sum_gegenbauerCoefficient_le_uniform_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (gegenbauerMeasure lam))
    (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = (F x).re)
    (k : ℕ) (hk : lam + 1 / 2 ≤ k) (hks : 2 * lam ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(F x).re - ∑ i ∈ Finset.range (N + 1),
        (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) * (gegenbauer lam i).eval x‖ ≤
      (1 + √(jacobiKernelBound ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ k) *
        ((N : ℝ) + 1) ^ (3 * k + 3) * √((gegenbauerMeasure lam).real univ)) *
        (2 * M / (ρ ^ N * (ρ - 1))) := by
  have h := (isOrthogonal_gegenbauerSequence hlam hzero).norm_sub_eval_partialSum_le_kernel_of_analytic
    (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
    ((ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)) hρ hF hM f hf N hx
  simp only [Sequence.partialSum_ofL2, eval_finsetSum, eval_smul, smul_eq_mul,
    Sequence.integralCoefficient, squaredNorm_gegenbauerSequence, gegenbauerSequence_apply,
    IntegralCoefficientInput.ofL2,
    gegenbauer_kernel_eq_jacobi hlam hzero] at h
  have hM0 : 0 ≤ M := (norm_nonneg (F x)).trans (hM x (ofReal_mem_bernsteinEllipse hρ hx))
  apply h.trans
  gcongr
  exact sqrt_jacobi_kernel_le_polynomial (by linarith) (by linarith) k
    (by linarith) (by linarith) (by linarith) N hx

/-- Analytic Gegenbauer expansions converge uniformly, including the endpoints. -/
theorem tendstoUniformlyOn_sum_gegenbauerCoefficient_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (gegenbauerMeasure lam))
    (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = (F x).re) :
    TendstoUniformlyOn (fun N x ↦ ∑ i ∈ Finset.range (N + 1),
      (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) * (gegenbauer lam i).eval x)
      (fun x : ℝ ↦ (F x).re) atTop (Icc (-1) 1) := by
  obtain ⟨k, hk0, hks⟩ := exists_gegenbauerKernel_exponent lam
  apply tendstoUniformlyOn_of_polynomial_geometric_bound (3 * k + 3) hρ
    (A := √(jacobiKernelBound ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ k) *
      √((gegenbauerMeasure lam).real univ)) (B := ρ - 1) (C := 2 * M)
  intro N x hx
  convert norm_sub_sum_gegenbauerCoefficient_le_uniform_of_analytic hlam hzero hρ hF hM f hf
    k hk0 hks N hx using 1
  ring

end Polynomial
