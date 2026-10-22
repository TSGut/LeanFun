/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Bounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.PolynomialBounds
import Mathlib.Tactic.GCongr

/-!
# Polynomial growth bounds throughout the Jacobi orthogonality range

Endpoint values and Gamma norms admit elementary, deliberately nonsharp bounds
by fixed powers of the degree. These are sufficient for geometric convergence
of spectral approximations. References: DLMF Tables 18.3.1 and 18.6.1.
-/

@[expose] public section
namespace Polynomial
open Real MeasureTheory Set

/-- An explicit endpoint-growth constant; the argument type excludes exactly the shifted Gamma poles. -/
noncomputable def jacobiEndpointBound (a : {a : ℝ // ∀ n : ℕ, a + 1 ≠ -(n : ℝ)}) (k : ℕ) : ℝ :=
  1 + |a.val + 1| + ((k : ℝ) + 1) ^ k / GammaOn ⟨a.val + 1, a.property⟩

/-- The endpoint-growth constant is positive throughout the integrable range. -/
theorem jacobiEndpointBound_pos {a : ℝ} (ha : -1 < a) (k : ℕ) :
    0 < jacobiEndpointBound ⟨a, (GammaPoint.ofPos (a + 1) (by linarith)).property⟩ k := by
  have hg := Gamma_pos_of_pos (show 0 < a + 1 by linarith)
  unfold jacobiEndpointBound
  change 0 < 1 + |a + 1| + ((k : ℝ) + 1) ^ k / Gamma (a + 1)
  positivity

/-- Polynomial growth of the endpoint value, with any integer exponent k ≥ alpha. -/
theorem abs_eval_jacobi_one_le_polynomial {α : ℝ} (hα : -1 < α) (β : ℝ)
    (k : ℕ) (hk : α ≤ k) (n : ℕ) :
    |(jacobi α β n).eval 1| ≤ jacobiEndpointBound ⟨α, (GammaPoint.ofPos (α + 1) (by linarith)).property⟩ k * ((n : ℝ) + 1) ^ k := by
  have hp := ascPochhammer_pos n (α + 1) (by linarith : 0 < α + 1)
  rw [eval_jacobi_one]
  norm_num only [map_inv₀, map_natCast, Rat.cast_natCast]
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hp.le)]
  simpa only [jacobiEndpointBound, GammaOn, GammaPoint.ofPos, div_eq_mul_inv, mul_comm] using
    ascPochhammer_div_factorial_le_polynomial (by linarith : 0 < α + 1) k (by linarith) n

/-- The negative endpoint has the same bound with beta replacing alpha. -/
theorem abs_eval_jacobi_neg_one_le_polynomial (α : ℝ) {β : ℝ} (hβ : -1 < β)
    (k : ℕ) (hk : β ≤ k) (n : ℕ) :
    |(jacobi α β n).eval (-1)| ≤ jacobiEndpointBound ⟨β, (GammaPoint.ofPos (β + 1) (by linarith)).property⟩ k * ((n : ℝ) + 1) ^ k := by
  rw [eval_jacobi_neg_one, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  simpa only [eval_jacobi_one] using abs_eval_jacobi_one_le_polynomial hβ α k hk n

/-- Both endpoint values are bounded by the sum of their growth constants. -/
theorem max_abs_eval_jacobi_endpoints_le_polynomial {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (k : ℕ) (hkα : α ≤ k) (hkβ : β ≤ k) (n : ℕ) :
    max |(jacobi α β n).eval (-1)| |(jacobi α β n).eval 1| ≤
      (jacobiEndpointBound ⟨α, (GammaPoint.ofPos (α + 1) (by linarith)).property⟩ k + jacobiEndpointBound ⟨β, (GammaPoint.ofPos (β + 1) (by linarith)).property⟩ k) * ((n : ℝ) + 1) ^ k := by
  apply max_le
  · apply (abs_eval_jacobi_neg_one_le_polynomial α hβ k hkβ n).trans
    gcongr
    exact le_add_of_nonneg_left (jacobiEndpointBound_pos hα k).le
  · apply (abs_eval_jacobi_one_le_polynomial hα β k hkα n).trans
    gcongr
    exact le_add_of_nonneg_right (jacobiEndpointBound_pos hβ k).le

/-- A uniform polynomial growth bound on [-1,1], valid for every alpha,beta > -1.
The integer exponent only needs to dominate alpha+1 and beta. -/
theorem abs_eval_jacobi_le_polynomial {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(jacobi α β n).eval x| ≤
      (1 + 2 * (jacobiEndpointBound ⟨α + 1, (GammaPoint.ofPos (α + 1 + 1) (by linarith)).property⟩ k + jacobiEndpointBound ⟨β, (GammaPoint.ofPos (β + 1) (by linarith)).property⟩ k)) *
        ((n : ℝ) + 1) ^ k := by
  have hα' : -1 < α + 1 := by linarith
  have hC : 0 ≤ jacobiEndpointBound ⟨α + 1, (GammaPoint.ofPos (α + 1 + 1) (by linarith)).property⟩ k + jacobiEndpointBound ⟨β, (GammaPoint.ofPos (β + 1) (by linarith)).property⟩ k :=
    add_nonneg (jacobiEndpointBound_pos hα' k).le (jacobiEndpointBound_pos hβ k).le
  rcases n with _ | n
  · simp only [jacobi_zero, eval_one, abs_one, Nat.cast_zero, zero_add, one_pow, mul_one]
    linarith
  have h := abs_eval_jacobi_succ_le_shifted_endpoints hα hβ n hx
  have h1 := max_abs_eval_jacobi_endpoints_le_polynomial hα' hβ k hkα hkβ (n + 1)
  have h0 := max_abs_eval_jacobi_endpoints_le_polynomial hα' hβ k hkα hkβ n
  apply (h.trans (add_le_add h1 h0)).trans
  have hp : ((n : ℝ) + 1) ^ k ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hp hC,
    pow_nonneg (show 0 ≤ (((n + 1 : ℕ) : ℝ) + 1) by positivity) k]

end Polynomial
