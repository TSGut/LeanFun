/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.UltrasphericalLadder
/-! # Ultraspherical coordinates of polynomial derivatives
Reference: Olver--Townsend (2013), Section 3.
-/
@[expose] public noncomputable section
namespace Polynomial
open Module

/-- A positive-order derivative has one nonzero entry per input column. -/
theorem ultraspherical_derivative_coordinate (k i : ℕ) (p : ℝ[X]) :
    (ultrasphericalBasis (k + 1)).repr ((derivative ^ (k + 1)) p) i =
      (2 : ℝ)^k * k.factorial * (i + k + 1) * chebyshevBasis.repr p (i + k + 1) := by
  let b := ultrasphericalBasis (k + 1)
  have hb (j : ℕ) : b j = gegenbauer ((k : ℝ) + 1) j := by simp [b]
  have h : (b.coord i).comp (derivative ^ (k + 1)) =
      ((2 : ℝ)^k * k.factorial * (i + k + 1)) • chebyshevBasis.coord (i + k + 1) := by
    apply chebyshevBasis.ext
    intro j
    change b.repr ((derivative ^ (k + 1)) (chebyshevBasis j)) i =
      ((2 : ℝ)^k * k.factorial * (i + k + 1)) * chebyshevBasis.repr (chebyshevBasis j) (i + k + 1)
    rw [chebyshevBasis.repr_self]
    simp only [Finsupp.single_apply, Module.End.pow_apply, chebyshevBasis_apply]
    change b.toMatrix (fun j : ℕ ↦ derivative^[k + 1] (Chebyshev.T ℝ j)) i j = _
    by_cases hj : j < k + 1
    · rw [chebyshev_iterate_derivative_matrix_zero b k.succ i j hj]
      rw [ite_eq_right (by omega), mul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + k + 1 := ⟨j - (k + 1), by omega⟩
      rw [chebyshev_iterate_derivative_matrix b k hb]
      by_cases hi : i = n
      · subst n
        simp
      · rw [ite_eq_right hi, ite_eq_right (by omega), mul_zero]
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ ↦ L p) h
end Polynomial
