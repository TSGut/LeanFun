/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.PolynomialBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.NormBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Completeness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.KernelBound

/-!
# Polynomial growth of the Jacobi Christoffel kernel

These global bounds include the endpoints and the entire alpha,beta > -1 range.
They are deliberately nonsharp; fixed polynomial growth suffices for analytic
spectral approximation. References: DLMF 18.2(v), Tables 18.3.1 and 18.6.1.
-/

@[expose] public section
namespace Polynomial
open Real MeasureTheory Set

/-- The explicit constant in the nonsharp polynomial kernel bound. -/
noncomputable def jacobiKernelBound (α β : Ioi (-1 : ℝ)) (k : ℕ) : ℝ :=
  (1 + 2 * (jacobiEndpointBound ⟨α.val + 1, (GammaPoint.ofPos (α.val + 1 + 1) (by have ha : -1 < α.val := α.property; linarith)).property⟩ k + jacobiEndpointBound ⟨β.val, (GammaPoint.ofPos (β.val + 1) (by have hb : -1 < β.val := β.property; linarith)).property⟩ k)) ^ 2 *
    jacobiReciprocalNormBound α β k

/-- A single natural exponent satisfies all three kernel-growth constraints. -/
theorem exists_jacobiKernel_exponent (α β : ℝ) :
    ∃ k : ℕ, α + 1 ≤ (k : ℝ) ∧ β ≤ (k : ℝ) ∧ α + β + 1 ≤ (k : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max (α + 1) (max β (α + β + 1)))
  exact ⟨k, (le_max_left _ _).trans hk,
    (le_max_left _ _).trans ((le_max_right _ _).trans hk),
    (le_max_right _ _).trans ((le_max_right _ _).trans hk)⟩

/-- The exponent constraints for the symmetric Gegenbauer specialization. -/
theorem exists_gegenbauerKernel_exponent (lam : ℝ) :
    ∃ k : ℕ, lam + 1 / 2 ≤ (k : ℝ) ∧ 2 * lam ≤ (k : ℝ) := by
  obtain ⟨k, hk, _, hs⟩ := exists_jacobiKernel_exponent (lam - 1 / 2) (lam - 1 / 2)
  exact ⟨k, by linarith, by linarith⟩

/-- The kernel-growth constant is nonnegative. -/
theorem jacobiKernelBound_nonneg {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    0 ≤ jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k :=
  mul_nonneg (sq_nonneg _) (jacobiReciprocalNormBound_pos hα hβ k).le

/-- Each diagonal kernel summand has a uniform polynomial bound. -/
theorem jacobi_kernel_term_le_polynomial {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (hks : α + β + 1 ≤ k)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (jacobi α β n).eval x * (jacobi α β n).eval x /
        (∫ t, (jacobi α β n).eval t ^ 2 ∂jacobiMeasure α β) ≤
      jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k * ((n : ℝ) + 1) ^ (3 * k + 2) := by
  have hv := abs_eval_jacobi_le_polynomial hα hβ k hkα hkβ n hx
  have hi := inv_integral_sq_jacobi_le_polynomial hα hβ k hks n
  have hp := (integral_sq_jacobi_pos hα hβ n).le
  calc
    _ = |(jacobi α β n).eval x| ^ 2 *
        (∫ t, (jacobi α β n).eval t ^ 2 ∂jacobiMeasure α β)⁻¹ := by
      rw [sq_abs]
      ring
    _ ≤ ((1 + 2 * (jacobiEndpointBound ⟨α + 1, (GammaPoint.ofPos (α + 1 + 1) (by linarith)).property⟩ k + jacobiEndpointBound ⟨β, (GammaPoint.ofPos (β + 1) (by linarith)).property⟩ k)) *
          ((n : ℝ) + 1) ^ k) ^ 2 *
        (jacobiReciprocalNormBound ⟨α, hα⟩ ⟨β, hβ⟩ k * ((n : ℝ) + 1) ^ (k + 2)) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hv 2) hi (inv_nonneg.mpr hp) (sq_nonneg _)
    _ = _ := by
      simp only [jacobiKernelBound, mul_pow, ← pow_mul]
      rw [show 3 * k + 2 = k * 2 + (k + 2) by omega, pow_add]
      ring

/-- Uniform polynomial growth of the diagonal Jacobi Christoffel kernel. -/
theorem jacobi_kernel_le_polynomial {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (hks : α + β + 1 ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (jacobiSequence hα hβ).kernel (jacobiMeasure α β) N x x (Polynomial.Sequence.KernelInput.of _ _ _ (hi := fun _ => (hasFiniteMoments_jacobiMeasure hα hβ).integrable_mul _ _)) ≤
      jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k * ((N : ℝ) + 1) ^ (3 * k + 3) := by
  simp only [Sequence.kernel_of_positive (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) (jacobiSequence hα hβ), jacobiSequence_apply, squaredNorm_jacobiSequence]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k * ((N : ℝ) + 1) ^ (3 * k + 2) := by
      apply Finset.sum_le_sum
      intro n hn
      apply (jacobi_kernel_term_le_polynomial hα hβ k hkα hkβ hks n hx).trans
      apply mul_le_mul_of_nonneg_left _ (jacobiKernelBound_nonneg hα hβ k)
      apply pow_le_pow_left₀ (by positivity)
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact_mod_cast Nat.add_le_add_right hn' 1
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [show 3 * k + 3 = (3 * k + 2) + 1 by omega, pow_succ]
      ring

/-- A polynomial bound for the square root of the kernel, sufficient for
uniform geometric convergence after multiplication by the analytic error. -/
theorem sqrt_jacobi_kernel_le_polynomial {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (hks : α + β + 1 ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    √((jacobiSequence hα hβ).kernel (jacobiMeasure α β) N x x (Polynomial.Sequence.KernelInput.of _ _ _ (hi := fun _ => (hasFiniteMoments_jacobiMeasure hα hβ).integrable_mul _ _))) ≤
      √(jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k) * ((N : ℝ) + 1) ^ (3 * k + 3) := by
  apply (Real.sqrt_le_sqrt (jacobi_kernel_le_polynomial hα hβ k hkα hkβ hks N hx)).trans
  rw [Real.sqrt_mul (jacobiKernelBound_nonneg hα hβ k)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])))

end Polynomial
