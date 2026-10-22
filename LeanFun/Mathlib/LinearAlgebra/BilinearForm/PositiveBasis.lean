/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive bilinear forms from orthogonal bases

A finite orthogonal basis with positive diagonal pairing makes the entire form
positive definite. Reference: Dunkl–Xu, Chapter 3, orthogonal polynomial spaces.
-/

public section
open Module
namespace LinearMap.BilinForm
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Expansion of an orthogonal-basis quadratic pairing as a weighted sum of squares. -/
theorem apply_self_eq_sum_of_orthogonal_basis (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V)
    (ho : ∀ i j, i ≠ j → B (b i) (b j) = 0) (v : V) :
    B v v = ∑ i, (b.repr v i) ^ 2 * B (b i) (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  simp only [sum_left, sum_right, smul_left, smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [ho j i hji]
    simp
  · simp

/-- Positive diagonal entries in an orthogonal basis imply positive definiteness. -/
theorem apply_self_pos_of_orthogonal_basis (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V)
    (ho : ∀ i j, i ≠ j → B (b i) (b j) = 0) (hp : ∀ i, 0 < B (b i) (b i))
    {v : V} (hv : v ≠ 0) : 0 < B v v := by
  classical
  rw [apply_self_eq_sum_of_orthogonal_basis B b ho]
  have hex : ∃ i, b.repr v i ≠ 0 := by
    by_contra! h
    apply hv
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sq_nonneg _) (hp j).le
  · exact ⟨i, Finset.mem_univ _, mul_pos (sq_pos_of_ne_zero hi) (hp i)⟩

end LinearMap.BilinForm
