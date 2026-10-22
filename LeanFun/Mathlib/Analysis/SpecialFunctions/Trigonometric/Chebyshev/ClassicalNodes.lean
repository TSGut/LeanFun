/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
/-! # Classical positive-order Chebyshev nodes
Reference: ATAP Chapter 4. The angular denominator is positive in the input type.
-/
@[expose] public section
namespace Polynomial.Chebyshev
/-- Classical cosine nodes for positive order, with arbitrary natural angular index. -/
noncomputable def classicalNode (N : {n : ℕ // 0 < n}) (j : ℕ) : ℝ := node N.val j
/-- Cosine formula on the positive-order domain. -/
theorem classicalNode_apply (N : {n : ℕ // 0 < n}) (j : ℕ) :
    classicalNode N j = Real.cos (j * Real.pi / N.val) := rfl
/-- The extrema are strictly decreasing through the order. -/
theorem strictAntiOn_classicalNode (N : {n : ℕ // 0 < n}) :
    StrictAntiOn (classicalNode N) (Finset.range (N.val + 1)) := strictAntiOn_node N.val
/-- Every classical node lies in the closed interval. -/
theorem classicalNode_mem_Icc (N : {n : ℕ // 0 < n}) (j : ℕ) :
    classicalNode N j ∈ Set.Icc (-1 : ℝ) 1 := node_mem_Icc
/-- The two endpoint nodes. -/
theorem classicalNode_endpoints (N : {n : ℕ // 0 < n}) :
    classicalNode N 0 = 1 ∧ classicalNode N N.val = -1 :=
  ⟨node_eq_one, node_eq_neg_one (Nat.ne_of_gt N.property)⟩
/-- Finite extrema grid, with the separate singleton at `1` for order zero. -/
noncomputable def extremaGridNode (N : ℕ) (j : Fin (N + 1)) : ℝ :=
  if h : N = 0 then 1 else classicalNode ⟨N, Nat.pos_of_ne_zero h⟩ j


/-- The order-zero grid is the singleton `1`. -/
theorem extremaGridNode_zero (j : Fin 1) : extremaGridNode 0 j = 1 := by
  simp [extremaGridNode]

/-- Positive-order grid points use the classical cosine formula. -/
theorem extremaGridNode_positive (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    extremaGridNode N.val j = classicalNode N j := by
  simp [extremaGridNode, Nat.ne_of_gt N.property]

/-- Every finite-grid point lies in the interpolation interval. -/
theorem extremaGridNode_mem_Icc (N : ℕ) (j : Fin (N + 1)) :
    extremaGridNode N j ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases h : N = 0
  · subst N
    rw [extremaGridNode_zero]
    norm_num
  · rw [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero h⟩]
    exact classicalNode_mem_Icc _ _

/-- Finite-grid points are pairwise distinct, including the singleton grid. -/
theorem extremaGridNode_injective (N : ℕ) : Function.Injective (extremaGridNode N) := by
  by_cases h : N = 0
  · subst N
    intro i j _
    exact Fin.ext (by omega)
  · intro i j hij
    simp only [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero h⟩] at hij
    apply Fin.ext
    exact (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero h⟩).injOn
      (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) hij

end Polynomial.Chebyshev
