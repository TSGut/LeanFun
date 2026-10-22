/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Polynomially weighted coefficient spaces
The norm is the l2 norm of (n+1)^s u_n. Reference: Olver--Townsend §4.1.
-/

@[expose] public noncomputable section
namespace lp
variable (s : ℕ)

/-- Complex sequences whose degree-weighted coefficients are square summable. -/
def degreeWeightedL2Submodule : Submodule ℂ (ℕ → ℂ) where
  carrier := {u | Memℓp (fun n : ℕ ↦ ((n : ℂ)+1)^s*u n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℕ ↦ ((n : ℂ)+1)^s*0) 2
    simpa only [Pi.zero_apply, mul_zero] using (zero_mem_ℓp' : Memℓp (fun _ : ℕ ↦ (0 : ℂ)) 2)
  add_mem' {u v} hu hv := by
    change Memℓp (fun n : ℕ ↦ ((n : ℂ)+1)^s*(u n+v n)) 2
    simpa only [Pi.add_def, mul_add] using hu.add hv
  smul_mem' c u hu := by
    change Memℓp (fun n : ℕ ↦ ((n : ℂ)+1)^s*(c*u n)) 2
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using hu.const_smul c

/-- Polynomially weighted ℓ², with its own norm topology. -/
def DegreeWeightedL2 : Type := ↥(degreeWeightedL2Submodule s)

instance : AddCommGroup (DegreeWeightedL2 s) := inferInstanceAs (AddCommGroup ↥(degreeWeightedL2Submodule s))
instance : Module ℂ (DegreeWeightedL2 s) := inferInstanceAs (Module ℂ ↥(degreeWeightedL2Submodule s))

/-- Degree weighting identifies the weighted coefficient space with ordinary ℓ². -/
def degreeWeightedL2Equiv : DegreeWeightedL2 s ≃ₗ[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 where
  toFun u := ⟨fun n : ℕ ↦ ((n : ℂ)+1)^s*u.1 n, u.2⟩
  invFun v := ⟨fun n : ℕ ↦ v n / ((n : ℂ)+1)^s, by
    change Memℓp (fun n : ℕ ↦ ((n : ℂ)+1)^s*(v n / ((n : ℂ)+1)^s)) 2
    have he (n : ℕ) : ((n : ℂ)+1)^s*(v n / ((n : ℂ)+1)^s) = v n := by
      field_simp
    simpa only [he] using lp.memℓp v⟩
  left_inv u := by
    apply Subtype.ext
    funext n
    change (((n : ℂ)+1)^s*u.1 n)/((n : ℂ)+1)^s = u.1 n
    field_simp
  right_inv v := by
    apply lp.ext
    funext n
    change ((n : ℂ)+1)^s*(v n / ((n : ℂ)+1)^s) = v n
    field_simp
  map_add' u v := by
    apply lp.ext
    funext n
    exact mul_add _ _ _
  map_smul' c u := by
    apply lp.ext
    funext n
    change ((n : ℂ)+1)^s*(c*u.1 n) = c*(((n : ℂ)+1)^s*u.1 n)
    ring

instance : NormedAddCommGroup (DegreeWeightedL2 s) :=
  NormedAddCommGroup.induced _ _ (degreeWeightedL2Equiv s).toAddMonoidHom (degreeWeightedL2Equiv s).injective

instance : NormedSpace ℂ (DegreeWeightedL2 s) :=
  NormedSpace.induced ℂ _ _ (degreeWeightedL2Equiv s).toLinearMap

/-- Degree weighting is an isometry for the weighted coefficient norm. -/
def degreeWeightedL2Isometry : DegreeWeightedL2 s ≃ₗᵢ[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  { degreeWeightedL2Equiv s with norm_map' := fun _ ↦ rfl }

instance : CompleteSpace (DegreeWeightedL2 s) :=
  (degreeWeightedL2Isometry s).toIsometryEquiv.completeSpace

/-- Weighted coefficient norm, expressed using Mathlib's existing ℓ² norm. -/
theorem norm_degreeWeightedL2 (u : DegreeWeightedL2 s) :
    ‖u‖ = ‖(⟨fun n : ℕ ↦ ((n : ℂ)+1)^s*u.1 n, u.2⟩ : lp (fun _ : ℕ ↦ ℂ) 2)‖ := rfl

/-- The degree-weighted coefficient norm is complete. -/
theorem completeSpace_degreeWeightedL2 : CompleteSpace (DegreeWeightedL2 s) := inferInstance

end lp
