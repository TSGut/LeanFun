/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.UltrasphericalLadder
public import LeanFun.Mathlib.Algebra.Polynomial.DifferentialOperator

/-! # All-order ultraspherical residual bandwidth
Differentiate into the natural level, convert to the common target level, then
multiply there. All operators act exactly on polynomials and finite coefficient
vectors. Reference: Olver--Townsend (2013), Section 3.
-/

public section
namespace Polynomial
open Module

/-- A term `p D^k` represented at level N has the derivative/conversion bandwidth
plus the polynomial multiplication bandwidth. -/
theorem ultrasphericalBasis_differential_term_isBanded {k N : ℕ} (hN : 1 ≤ N) (hk : k ≤ N)
    (p : ℝ[X]) :
    ((ultrasphericalBasis N).toMatrix
      (fun j ↦ p * derivative^[k] (chebyshevBasis j))).IsBanded
        p.natDegree (p.natDegree + 2 * N - k) := by
  have h := chebyshevBasis.toMatrix_comp_isBanded (ultrasphericalBasis N)
    (ultrasphericalBasis N) (derivative ^ k) (LinearMap.mulLeft ℝ p)
    (by simpa only [Module.End.pow_apply] using ultrasphericalBasis_derivative_to_level_isBanded hk)
    (ultrasphericalBasis_mul_isBanded hN p)
  have he : (2 * N - k) + p.natDegree = p.natDegree + 2 * N - k := by omega
  simpa only [LinearMap.mulLeft_apply, Module.End.pow_apply, Nat.zero_add, he] using h

/-- Full all-order assembly, with separate bounds for each coefficient degree.
The analytic existence or uniqueness of an ODE solution is not assumed or asserted. -/
theorem ultraspherical_differentialOperator_isBanded
    (a : ℕ → ℝ[X]) {N l u : ℕ} (hN : 1 ≤ N)
    (hl : ∀ k ≤ N, (a k).natDegree ≤ l)
    (hu : ∀ k ≤ N, (a k).natDegree + 2 * N - k ≤ u) :
    ((ultrasphericalBasis N).toMatrix
      (fun j ↦ differentialOperator a N (chebyshevBasis j))).IsBanded l u := by
  apply differentialOperator_isBanded
  intro k hk
  exact (ultrasphericalBasis_differential_term_isBanded hN hk (a k)).mono (hl k hk) (hu k hk)

/-- A common coefficient-degree bound d gives residual bandwidths (d,d+2N). -/
theorem ultraspherical_differentialOperator_isBanded_of_degree_le
    (a : ℕ → ℝ[X]) {N d : ℕ} (hN : 1 ≤ N)
    (hd : ∀ k ≤ N, (a k).natDegree ≤ d) :
    ((ultrasphericalBasis N).toMatrix
      (fun j ↦ differentialOperator a N (chebyshevBasis j))).IsBanded d (d + 2 * N) := by
  apply ultraspherical_differentialOperator_isBanded a hN hd
  intro k hk
  have := hd k hk
  omega

/-- With m input coefficients and coefficient degrees at most d, m+d residual
rows capture the whole polynomial result. This justifies rectangular padding. -/
theorem ultraspherical_differentialOperator_coeff_eq_zero
    (a : ℕ → ℝ[X]) {N d m : ℕ} (hN : 1 ≤ N)
    (hd : ∀ k ≤ N, (a k).natDegree ≤ d) (v : ℕ →₀ ℝ)
    (hv : ∀ j ∈ v.support, j < m) {i : ℕ} (hi : m + d ≤ i) :
    chebyshevBasis.coefficientMap (ultrasphericalBasis N) (differentialOperator a N) v i = 0 :=
  chebyshevBasis.coefficientMap_eq_zero_of_bandwidth (ultrasphericalBasis N)
    (differentialOperator a N) (ultraspherical_differentialOperator_isBanded_of_degree_le a hN hd)
    v hv hi

end Polynomial
