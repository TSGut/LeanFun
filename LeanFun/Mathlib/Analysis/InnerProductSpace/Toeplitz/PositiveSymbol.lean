/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.ContinuousSymbol
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Positive lower bounds for continuous Toeplitz symbols

A uniform positive real part of the symbol gives a coercive Toeplitz operator.
Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
-/

@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
namespace AddCircle
variable {T : ℝ} [Fact (0 < T)]
local notation "L" => Lp ℂ 2 (haarAddCircle (T := T))
local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

/-- A lower bound on the real part of a multiplier gives the same quadratic-form bound. -/
theorem re_inner_continuousSymbolMultiplier_le (f : C(AddCircle T, ℂ)) {a : ℝ}
    (hf : ∀ x, a ≤ (f x).re) (u : L) :
    a*‖u‖^2 ≤ (⟪u, continuousSymbolMultiplier f u⟫_ℂ).re := by
  have hsq : Integrable (fun x ↦ ‖u x‖^2) haarAddCircle := by
    simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using
      (L2.integrable_inner (𝕜 := ℂ) u u).re
  have he : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂haarAddCircle := by
    have hh := congrArg (RCLike.re (K := ℂ)) (L2.inner_def u u (𝕜 := ℂ))
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hh
    simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hh
  change a*‖u‖^2 ≤ RCLike.re (⟪u, continuousSymbolMultiplier f u⟫_ℂ)
  rw [he, ← integral_const_mul, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) u (continuousSymbolMultiplier f u))]
  apply integral_mono_ae (hsq.const_mul a)
    (L2.integrable_inner (𝕜 := ℂ) u (continuousSymbolMultiplier f u)).re
  filter_upwards [continuousSymbolMultiplier_ae f u] with x hx
  rw [hx]
  change a*‖u x‖^2 ≤ (⟪u x, (f x) • u x⟫_ℂ).re
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow]
  change a*‖u x‖^2 ≤ (f x * (↑(‖u x‖^2) : ℂ)).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (hf x) (sq_nonneg ‖u x‖)

/-- Compression preserves the positive real-part lower bound of a continuous symbol. -/
theorem re_inner_continuousToeplitz_le (f : C(AddCircle T, ℂ)) {a : ℝ}
    (hf : ∀ x, a ≤ (f x).re) (u : H) :
    a*‖u‖^2 ≤ (⟪u, continuousToeplitz f u⟫_ℂ).re := by
  have he := adjoint_inner_right
    (nonnegativeFourierIsometry (T := T)).toContinuousLinearMap u
    (continuousSymbolMultiplier f (nonnegativeFourierIsometry u))
  change a*‖u‖^2 ≤
    (⟪u, nonnegativeFourierIsometry.toContinuousLinearMap.adjoint
      (continuousSymbolMultiplier f (nonnegativeFourierIsometry u))⟫_ℂ).re
  rw [he]
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using
    re_inner_continuousSymbolMultiplier_le f hf (nonnegativeFourierIsometry u)

/-- A continuous symbol with uniformly positive real part has an invertible Toeplitz operator. -/
theorem isUnit_continuousToeplitz_of_re_pos (f : C(AddCircle T, ℂ)) {a : ℝ}
    (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re) : IsUnit (continuousToeplitz f) := by
  apply isUnit_of_forall_le_norm_inner_map (continuousToeplitz f) (c := ⟨a, ha.le⟩) ha
  intro u
  have h := (re_inner_continuousToeplitz_le f hf u).trans
    (Complex.re_le_norm _)
  change ‖u‖^2*a ≤ ‖⟪continuousToeplitz f u, u⟫_ℂ‖
  rw [norm_inner_symm, mul_comm]
  exact h

end AddCircle
