/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CompactSections
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Unilateral shifts on ℓ²

The forward shift and its adjoint provide the building blocks for Toeplitz
operators. Reference: Böttcher–Silbermann, Introduction to Large Truncated
Toeplitz Matrices, Chapter 1.
-/

@[expose] public noncomputable section
open scoped InnerProductSpace ENNReal
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The square of an ℓ² norm is the sum of the squared coordinate norms. -/
theorem norm_sq_eq_tsum_sq (u : lp (fun _ : ℕ ↦ 𝕜) 2) :
    ‖u‖^2 = ∑' n, ‖u n‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u

/-- Inserting a zero coordinate preserves square summability. -/
theorem memℓp_cons_zero (u : lp (fun _ : ℕ ↦ 𝕜) 2) :
    Memℓp (Nat.rec (motive := fun _ ↦ 𝕜) (0 : 𝕜) (fun n _ ↦ u n)) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  apply (summable_nat_add_iff 1).mp
  simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The unilateral forward shift is an isometric embedding. -/
def forwardShiftL2 : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 where
  toFun u := ⟨Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun n _ ↦ u n), memℓp_cons_zero u⟩
  map_add' u v := by
    apply lp.ext
    funext n
    change Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ u i+v i) n =
      Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ u i) n +
        Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ v i) n
    cases n <;> simp
  map_smul' c u := by
    apply lp.ext
    funext n
    change Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ c*u i) n =
      c*Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ u i) n
    cases n <;> simp
  norm_map' u := by
    have he : ‖(⟨Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun n _ ↦ u n), memℓp_cons_zero u⟩ : lp (fun _ : ℕ ↦ 𝕜) 2)‖^2 = ‖u‖^2 := by
      rw [norm_sq_eq_tsum_sq, norm_sq_eq_tsum_sq]
      rw [tsum_eq_zero_add' (f := fun n ↦ ‖Nat.rec (motive := fun _ ↦ 𝕜) 0 (fun i _ ↦ u i) n‖^2)
        (by simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))]
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- The new zeroth coefficient is zero. -/
@[simp] theorem forwardShiftL2_zero (u : lp (fun _ : ℕ ↦ 𝕜) 2) : forwardShiftL2 u 0 = 0 := rfl

/-- All other coefficients move one position to the right. -/
@[simp] theorem forwardShiftL2_succ (u : lp (fun _ : ℕ ↦ 𝕜) 2) (n : ℕ) :
    forwardShiftL2 u (n+1) = u n := rfl

/-- The backward shift is the Hilbert adjoint of the forward shift. -/
def backwardShiftL2 : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  forwardShiftL2.toContinuousLinearMap.adjoint

/-- A coordinate vector shifts to the next coordinate vector. -/
theorem forwardShiftL2_single (n : ℕ) (a : 𝕜) :
    forwardShiftL2 (lp.single 2 n a) = lp.single 2 (n+1) a := by
  apply lp.ext
  funext i
  cases i with
  | zero => simp
  | succ i => simp [lp.single_apply, Pi.single_apply]

/-- The adjoint deletes the zeroth coefficient. -/
@[simp] theorem backwardShiftL2_apply (u : lp (fun _ : ℕ ↦ 𝕜) 2) (n : ℕ) :
    backwardShiftL2 u n = u (n+1) := by
  have h := ContinuousLinearMap.adjoint_inner_right forwardShiftL2.toContinuousLinearMap
    (lp.single 2 n 1) u
  simpa only [backwardShiftL2, LinearIsometry.coe_toContinuousLinearMap,
    forwardShiftL2_single, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h

/-- Backward shift is a left inverse of forward shift. -/
theorem backwardShiftL2_comp_forwardShiftL2 :
    (backwardShiftL2 (𝕜 := 𝕜)).comp forwardShiftL2.toContinuousLinearMap = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext n
  simp

/-- Forward shift followed by backward shift loses exactly the zeroth coordinate. -/
theorem forwardShiftL2_comp_backwardShiftL2 :
    (forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap.comp backwardShiftL2 =
      1-lp.initialL2Projection 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext n
  change forwardShiftL2 (backwardShiftL2 u) n = u n - lp.initialL2Projection 1 u n
  cases n <;> simp [lp.initialL2Projection_apply, lp.single_apply]

end lp
