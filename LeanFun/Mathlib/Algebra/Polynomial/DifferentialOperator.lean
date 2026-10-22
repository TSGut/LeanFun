/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.FiniteSection
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Exact polynomial differential operators
Finite sums of polynomial multiplication followed by differentiation act on
polynomials and their finitely supported coordinates. No ODE solvability or
infinite-dimensional convergence is asserted.
Reference: Olver--Townsend (2013), Section 3.
-/

@[expose] public section
namespace Polynomial
variable {R : Type*} [CommRing R]

/-- Assemble `∑ k ≤ N, a_k D^k` on the polynomial module (Olver--Townsend, Section 3). -/
noncomputable def differentialOperator (a : ℕ → R[X]) (N : ℕ) : Module.End R R[X] :=
  ∑ k ∈ Finset.range (N + 1), (LinearMap.mulLeft R (a k)).comp (derivative ^ k)

/-- Polynomial operator assembly has exactly the expected differential action. -/
theorem differentialOperator_apply (a : ℕ → R[X]) (N : ℕ) (p : R[X]) :
    differentialOperator a N p = ∑ k ∈ Finset.range (N + 1), a k * derivative^[k] p := by
  simp [differentialOperator, LinearMap.mulLeft_apply, Module.End.pow_apply]

/-- The first-order case is multiplication plus multiplication after one derivative. -/
theorem differentialOperator_one_apply (a : ℕ → R[X]) (p : R[X]) :
    differentialOperator a 1 p = a 0 * p + a 1 * derivative p := by
  simp [differentialOperator_apply, Finset.sum_range_succ]

/-- Coefficient assembly reconstructs the exact polynomial residual. -/
theorem repr_symm_differentialOperator (b c : Module.Basis ℕ R R[X])
    (a : ℕ → R[X]) (N : ℕ) (v : ℕ →₀ R) :
    c.repr.symm (b.coefficientMap c (differentialOperator a N) v) =
      ∑ k ∈ Finset.range (N + 1), a k * derivative^[k] (b.repr.symm v) := by
  rw [b.repr_symm_coefficientMap, differentialOperator_apply]

/-- Uniform bandwidth bounds on the assembled terms bound their sum. In the
ultraspherical method these term bounds come from derivative, conversion, and
multiplication bandwidths, not from an arbitrary square truncation. -/
theorem differentialOperator_isBanded (b c : Module.Basis ℕ R R[X])
    (a : ℕ → R[X]) (N l u : ℕ)
    (h : ∀ k ≤ N, (c.toMatrix (fun j ↦ a k * derivative^[k] (b j))).IsBanded l u) :
    (c.toMatrix (fun j ↦ differentialOperator a N (b j))).IsBanded l u := by
  intro i j hij
  simp only [Module.Basis.toMatrix_apply, differentialOperator_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) i j hij

/-- Polynomial differential assembly commutes with changing the coefficient ring. -/
theorem differentialOperator_map {S : Type*} [CommRing S] (σ : R →+* S)
    (A : ℕ → R[X]) (m : ℕ) (p : R[X]) :
    (differentialOperator A m p).map σ =
      differentialOperator (fun k ↦ (A k).map σ) m (p.map σ) := by
  simp only [differentialOperator_apply, Polynomial.map_sum, Polynomial.map_mul,
    iterate_derivative_map]

end Polynomial
