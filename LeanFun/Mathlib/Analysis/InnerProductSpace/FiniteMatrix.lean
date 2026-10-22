/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CompactSections
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual finite matrices of ℓ² operators

Zero extension identifies finite vectors with the initial coordinate range.
The matrix of a bounded operator then gives exactly its projected action.
Reference: finite-section Galerkin equations, Olver–Townsend (2013), §4.
-/

@[expose] public noncomputable section
open scoped Matrix
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Embed a finite vector by extending it with zeros. -/
def initialL2Vector {N : ℕ} (v : Fin N → 𝕜) : lp (fun _ : ℕ ↦ 𝕜) 2 :=
  ∑ j : Fin N, lp.single 2 (j : ℕ) (v j)

/-- Restriction of zero extension recovers each finite coordinate. -/
@[simp] theorem initialL2Vector_apply {N : ℕ} (v : Fin N → 𝕜) (i : Fin N) :
    initialL2Vector v i = v i := by
  classical
  change (lp.evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i) (∑ j : Fin N, lp.single 2 (j : ℕ) (v j)) = _
  rw [map_sum]
  change (∑ j : Fin N, (lp.single 2 (j : ℕ) (v j) : lp (fun _ : ℕ ↦ 𝕜) 2) i) = v i
  simp [Pi.single_apply, Fin.val_inj]

/-- Embedding the first coordinates is exactly the initial orthogonal projection. -/
theorem initialL2Vector_restrict (N : ℕ) (c : lp (fun _ : ℕ ↦ 𝕜) 2) :
    initialL2Vector (fun i : Fin N ↦ c i) = initialL2Projection N c := by
  rw [initialL2Vector, initialL2Projection_apply]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ lp.single 2 j (c j)) N

/-- Initial projection fixes every embedded finite vector. -/
@[simp] theorem initialL2Projection_vector {N : ℕ} (v : Fin N → 𝕜) :
    initialL2Projection N (initialL2Vector v) = initialL2Vector v := by
  rw [← initialL2Vector_restrict]
  simp only [initialL2Vector_apply]

/-- Matrix entries in the standard orthonormal coordinates. -/
def initialL2Matrix (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (N : ℕ) : Matrix (Fin N) (Fin N) 𝕜 :=
  fun i j ↦ T (lp.single 2 (j : ℕ) 1) i

/-- Matrix multiplication is the coordinate restriction of the bounded operator. -/
theorem initialL2Matrix_mulVec
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    {N : ℕ} (v : Fin N → 𝕜) (i : Fin N) :
    (initialL2Matrix T N *ᵥ v) i = T (initialL2Vector v) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, initialL2Matrix, initialL2Vector, map_sum,
    lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  change T (lp.single 2 (j : ℕ) 1) i * v j = T (lp.single 2 (j : ℕ) (v j)) i
  have he : (lp.single 2 (j : ℕ) (v j) : lp (fun _ : ℕ ↦ 𝕜) 2) =
      v j • lp.single 2 (j : ℕ) 1 := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ℕ ↦ 𝕜) 2 (j : ℕ) (v j) (1 : 𝕜)
  rw [he, map_smul]
  change _ = v j * _
  exact mul_comm _ _

/-- The finite second-kind matrix equation is equivalent to the projected equation. -/
theorem initialL2Matrix_equation_iff
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    {N : ℕ} (v : Fin N → 𝕜) (f : lp (fun _ : ℕ ↦ 𝕜) 2) :
    (1 - initialL2Matrix T N) *ᵥ v = (fun i : Fin N ↦ f i) ↔
      initialL2Projection N (initialL2Vector v - T (initialL2Vector v)) =
        initialL2Projection N f := by
  rw [← initialL2Vector_restrict, ← initialL2Vector_restrict]
  constructor
  · intro h
    congr 1
    funext i
    have hi := congrFun h i
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      initialL2Matrix_mulVec, lp.coeFn_sub, initialL2Vector_apply] using hi
  · intro h
    funext i
    have hi := congrArg (fun c : lp (fun _ : ℕ ↦ 𝕜) 2 ↦ c i) h
    simpa only [initialL2Vector_apply, lp.coeFn_sub, Pi.sub_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, initialL2Matrix_mulVec] using hi

/-- A unique projected solution gives a unique solution of the actual finite matrix. -/
theorem existsUnique_initialL2Matrix_solution
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (N : ℕ) (f : lp (fun _ : ℕ ↦ 𝕜) 2)
    (h : ∃! u, initialL2Projection N u = u ∧
      initialL2Projection N (u - T u) = initialL2Projection N f) :
    ∃! v : Fin N → 𝕜, (1 - initialL2Matrix T N) *ᵥ v = (fun i : Fin N ↦ f i) := by
  obtain ⟨u, hu, huniq⟩ := h
  refine ⟨fun i ↦ u i, ?_, ?_⟩
  · apply (initialL2Matrix_equation_iff T (fun i : Fin N ↦ u i) f).mpr
    simpa only [initialL2Vector_restrict, hu.1] using hu.2
  · intro v hv
    have he := huniq (initialL2Vector v)
      ⟨initialL2Projection_vector v, (initialL2Matrix_equation_iff T v f).mp hv⟩
    funext i
    simpa only [initialL2Vector_apply] using
      congrArg (fun c : lp (fun _ : ℕ ↦ 𝕜) 2 ↦ c i) he

end lp
