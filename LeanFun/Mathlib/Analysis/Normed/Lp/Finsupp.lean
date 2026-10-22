/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Finite coefficients as square-summable sequences

The canonical linear embedding preserves coefficients and coordinate vectors.
Reference: the finite-section coefficient convention of Olver--Townsend (2013).
-/

@[expose] public noncomputable section
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical embedding of finitely supported coefficients into ℓ². -/
def finsuppL2 : (ℕ →₀ 𝕜) →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 where
  toFun c := ⟨fun n ↦ c n, by
    apply Memℓp.of_exponent_ge (p := 2) (q := 0) _ (by norm_num)
    exact memℓp_zero_iff.mpr c.hasFiniteSupport⟩
  map_add' _ _ := by apply lp.ext; rfl
  map_smul' _ _ := by apply lp.ext; rfl

/-- Embedding leaves every coordinate unchanged. -/
@[simp] theorem finsuppL2_apply (c : ℕ →₀ 𝕜) (n : ℕ) : finsuppL2 c n = c n := rfl

/-- Coordinate vectors agree under the finite embedding. -/
@[simp] theorem finsuppL2_single (n : ℕ) (a : 𝕜) :
    finsuppL2 (Finsupp.single n a) = lp.single 2 n a := by
  apply lp.ext
  funext i
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- The finite embedding is injective. -/
theorem finsuppL2_injective : Function.Injective (finsuppL2 (𝕜 := 𝕜)) := by
  intro c d h
  ext n
  exact congrArg (fun u : lp (fun _ : ℕ ↦ 𝕜) 2 ↦ u n) h

end lp
