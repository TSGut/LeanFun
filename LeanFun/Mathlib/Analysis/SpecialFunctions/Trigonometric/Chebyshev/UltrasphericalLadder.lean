/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Operators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.MultiplicationOperator

/-! # The ultraspherical basis ladder
Level zero is Chebyshev T, not the degenerate Gegenbauer parameter zero.
Positive levels reuse the existing Gegenbauer polynomial bases.
Reference: Olver--Townsend (2013), Section 3.
-/

@[expose] public section
namespace Polynomial
open Module

/-- Coordinate bases for the ultraspherical method: T at zero, C^(k) at k>0. -/
noncomputable def ultrasphericalBasis : ℕ → Basis ℕ ℝ ℝ[X]
  | 0 => chebyshevBasis
  | k + 1 => gegenbauerBasis
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : -(1 / 2 : ℝ) < (k : ℝ) + 1)
      (by positivity : (k : ℝ) + 1 ≠ 0)

@[simp] theorem ultrasphericalBasis_zero : ultrasphericalBasis 0 = chebyshevBasis := rfl

@[simp] theorem ultrasphericalBasis_succ_apply (k j : ℕ) :
    ultrasphericalBasis (k + 1) j = gegenbauer (k + 1 : ℝ) j := by
  simp [ultrasphericalBasis]

/-- One step of the basis ladder has bandwidths (0,2), including the T entry. -/
theorem ultrasphericalBasis_step_isBanded (k : ℕ) :
    ((ultrasphericalBasis (k + 1)).toMatrix (ultrasphericalBasis k)).IsBanded 0 2 := by
  cases k with
  | zero =>
    simpa only [ultrasphericalBasis, Nat.cast_zero, zero_add] using
      chebyshevBasis_conversion_isBanded
  | succ k =>
    have he : (ultrasphericalBasis (k + 1) : ℕ → ℝ[X]) = gegenbauer (k + 1 : ℝ) := by
      funext j
      exact ultrasphericalBasis_succ_apply k j
    rw [he]
    apply gegenbauer_conversion_matrix_isBanded (k + 1 : ℝ)
    · intro j
      simp [ultrasphericalBasis, Nat.cast_add, Nat.cast_one]
    · intro n
      exact ne_of_gt (by positivity)

/-- Conversion through r successive levels has upper bandwidth 2*r. -/
theorem ultrasphericalBasis_raise_isBanded (k r : ℕ) :
    ((ultrasphericalBasis (k + r)).toMatrix (ultrasphericalBasis k)).IsBanded 0 (2 * r) := by
  induction r with
  | zero =>
    intro i j hij
    simp only [Nat.add_zero, Basis.toMatrix_apply, Basis.repr_self, Finsupp.single_apply]
    exact ite_eq_right (by omega)
  | succ r ih =>
    have h := (ultrasphericalBasis k).toMatrix_comp_isBanded
      (ultrasphericalBasis (k + r)) (ultrasphericalBasis (k + r + 1))
      LinearMap.id LinearMap.id ih (ultrasphericalBasis_step_isBanded (k + r))
    convert h using 1

/-- Conversion to any later level has upper bandwidth twice the level difference. -/
theorem ultrasphericalBasis_conversion_isBanded {k N : ℕ} (hk : k ≤ N) :
    ((ultrasphericalBasis N).toMatrix (ultrasphericalBasis k)).IsBanded 0 (2 * (N - k)) := by
  simpa only [Nat.add_sub_of_le hk] using ultrasphericalBasis_raise_isBanded k (N - k)

/-- Order-k differentiation reaches its natural level with upper bandwidth k. -/
theorem ultrasphericalBasis_derivative_isBanded (k : ℕ) :
    ((ultrasphericalBasis k).toMatrix
      (fun j ↦ derivative^[k] (chebyshevBasis j))).IsBanded 0 k := by
  cases k with
  | zero =>
    intro i j hij
    simp only [Function.iterate_zero_apply, ultrasphericalBasis_zero,
      Basis.toMatrix_apply, Basis.repr_self, Finsupp.single_apply]
    exact ite_eq_right (by omega)
  | succ k => exact chebyshevBasis_iterate_derivative_isBanded k

/-- Every derivative can be represented in a common later level N, with the
conversion cost made explicit (Olver--Townsend, Section 3). -/
theorem ultrasphericalBasis_derivative_to_level_isBanded {k N : ℕ} (hk : k ≤ N) :
    ((ultrasphericalBasis N).toMatrix
      (fun j ↦ derivative^[k] (chebyshevBasis j))).IsBanded 0 (2 * N - k) := by
  have h := chebyshevBasis.toMatrix_comp_isBanded (ultrasphericalBasis k)
    (ultrasphericalBasis N) (derivative ^ k) LinearMap.id
    (by simpa only [Module.End.pow_apply] using ultrasphericalBasis_derivative_isBanded k)
    (ultrasphericalBasis_conversion_isBanded hk)
  have he : k + 2 * (N - k) = 2 * N - k := by omega
  simpa only [LinearMap.id_apply, Module.End.pow_apply, Nat.zero_add, he] using h

/-- Polynomial multiplication has symmetric degree bandwidth at every positive level. -/
theorem ultrasphericalBasis_mul_isBanded {N : ℕ} (hN : 1 ≤ N) (p : ℝ[X]) :
    ((ultrasphericalBasis N).toMatrix (fun j ↦ p * ultrasphericalBasis N j)).IsBanded
      p.natDegree p.natDegree := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  exact gegenbauerBasis_polynomial_mul_isBanded _ _ p

end Polynomial
