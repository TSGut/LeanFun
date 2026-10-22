/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisOperator

/-! # First-order weighted real coefficient space

The norm is the ℓ² norm of `(n+1) * u n`. This is the first-kind Volterra
range space of Gutleb–Olver, Definition 5.3, and Gutleb's thesis, §2.7.
It is a space of raw coefficients, not normalized physical L² coordinates.
-/

@[expose] public noncomputable section
namespace lp

/-- Real sequences whose degree-weighted coefficients are square summable. -/
def firstOrderL2Submodule : Submodule ℝ (ℕ → ℝ) where
  carrier := {u | Memℓp (fun n : ℕ ↦ ((n : ℝ)+1)*u n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℕ ↦ ((n : ℝ)+1)*0) 2
    simpa only [Pi.zero_apply, mul_zero] using (zero_mem_ℓp' : Memℓp (fun _ : ℕ ↦ (0 : ℝ)) 2)
  add_mem' {u v} hu hv := by
    change Memℓp (fun n : ℕ ↦ ((n : ℝ)+1)*(u n+v n)) 2
    simpa only [Pi.add_def, mul_add] using hu.add hv
  smul_mem' c u hu := by
    change Memℓp (fun n : ℕ ↦ ((n : ℝ)+1)*(c*u n)) 2
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using hu.const_smul c

/-- First-order weighted ℓ², with its own norm topology. -/
def FirstOrderL2 : Type := ↥firstOrderL2Submodule

instance : AddCommGroup FirstOrderL2 := inferInstanceAs (AddCommGroup ↥firstOrderL2Submodule)
instance : Module ℝ FirstOrderL2 := inferInstanceAs (Module ℝ ↥firstOrderL2Submodule)

/-- Degree weighting identifies the first-order coefficient space with ordinary ℓ². -/
def firstOrderL2Equiv : FirstOrderL2 ≃ₗ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 where
  toFun u := ⟨fun n : ℕ ↦ ((n : ℝ)+1)*u.1 n, u.2⟩
  invFun v := ⟨fun n : ℕ ↦ v n / ((n : ℝ)+1), by
    change Memℓp (fun n : ℕ ↦ ((n : ℝ)+1)*(v n / ((n : ℝ)+1))) 2
    have he (n : ℕ) : ((n : ℝ)+1)*(v n / ((n : ℝ)+1)) = v n := by
      field_simp
    simpa only [he] using lp.memℓp v⟩
  left_inv u := by
    apply Subtype.ext
    funext n
    change (((n : ℝ)+1)*u.1 n)/((n : ℝ)+1) = u.1 n
    field_simp
  right_inv v := by
    apply lp.ext
    funext n
    change ((n : ℝ)+1)*(v n / ((n : ℝ)+1)) = v n
    field_simp
  map_add' u v := by
    apply lp.ext
    funext n
    exact mul_add _ _ _
  map_smul' c u := by
    apply lp.ext
    funext n
    change ((n : ℝ)+1)*(c*u.1 n) = c*(((n : ℝ)+1)*u.1 n)
    ring

instance : NormedAddCommGroup FirstOrderL2 :=
  NormedAddCommGroup.induced _ _ firstOrderL2Equiv.toAddMonoidHom firstOrderL2Equiv.injective

instance : NormedSpace ℝ FirstOrderL2 :=
  NormedSpace.induced ℝ _ _ firstOrderL2Equiv.toLinearMap

/-- Degree weighting is an isometry for the weighted coefficient norm. -/
def firstOrderL2Isometry : FirstOrderL2 ≃ₗᵢ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  { firstOrderL2Equiv with norm_map' := fun _ ↦ rfl }

instance : CompleteSpace FirstOrderL2 :=
  firstOrderL2Isometry.toIsometryEquiv.completeSpace

/-- Weighted coefficient norm, expressed using Mathlib's existing ℓ² norm. -/
theorem norm_firstOrderL2 (u : FirstOrderL2) :
    ‖u‖ = ‖(⟨fun n : ℕ ↦ ((n : ℝ)+1)*u.1 n, u.2⟩ : lp (fun _ : ℕ ↦ ℝ) 2)‖ := rfl

end lp
