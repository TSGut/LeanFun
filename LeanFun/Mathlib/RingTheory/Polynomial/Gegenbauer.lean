/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Rat.Cast.Defs

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

/-!
# Gegenbauer (ultraspherical) polynomials

These are also called ultraspherical polynomials (DLMF 18.1(ii)).
The explicit sum is defined over any commutative rational algebra, including
parameters for which the degree drops.
References: DLMF 18.5.10, https://dlmf.nist.gov/18.5#E10, and Table 18.3.1.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Gegenbauer polynomials in DLMF normalisation (DLMF 18.5.10). -/
noncomputable def gegenbauer (lam : R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((-1) ^ k * algebraMap ℚ R (((k.factorial : ℚ) * (n - 2 * k).factorial)⁻¹) *
      (ascPochhammer R (n - k)).eval lam) * (C 2 * X) ^ (n - 2 * k)

/-- The constant member is one (DLMF 18.5.10). -/
@[simp] theorem gegenbauer_zero (lam : R) : gegenbauer lam 0 = 1 := by
  simp [gegenbauer]

/-- The degree-one member is `2 lam X` (DLMF 18.5.10). -/
@[simp] theorem gegenbauer_one (lam : R) : gegenbauer lam 1 = C (2 * lam) * X := by
  simp [gegenbauer, map_mul]
  ring

/-- The degree is bounded by the index at every parameter (DLMF Table 18.3.1). -/
theorem natDegree_gegenbauer_le (lam : R) (n : ℕ) : (gegenbauer lam n).natDegree ≤ n := by
  unfold gegenbauer
  apply natDegree_sum_le_of_forall_le
  intro k _
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_pow_le_of_le _ ((natDegree_C_mul_le _ _).trans natDegree_X_le)).trans
  simp

/-- The degree bound includes vanishing specialisations (DLMF Table 18.3.1). -/
theorem degree_gegenbauer_le (lam : R) (n : ℕ) : (gegenbauer lam n).degree ≤ n :=
  degree_le_of_natDegree_le (natDegree_gegenbauer_le lam n)

/-- The coefficient of `X^n` before imposing nondegeneracy (DLMF Table 18.3.1). -/
theorem coeff_gegenbauer_self (lam : R) (n : ℕ) :
    (gegenbauer lam n).coeff n =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) * (ascPochhammer R n).eval lam * 2 ^ n := by
  unfold gegenbauer
  rw [finsetSum_coeff, Finset.sum_eq_single 0]
  · simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, ite_true]
  · intro k hk hk0
    rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, ite_eq_right]
    have := Finset.mem_range.mp hk
    omega
  · simp

/-- The nonzero top coefficient is the exact-degree condition
(DLMF Table 18.3.1). -/
theorem degree_gegenbauer_eq (lam : R) (n : ℕ)
    (h : algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval lam * 2 ^ n ≠ 0) : (gegenbauer lam n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_gegenbauer_le lam n)
    (by rwa [coeff_gegenbauer_self])

/-- Exact degree is equivalent to the top coefficient being nonzero
(DLMF Table 18.3.1). -/
theorem degree_gegenbauer_eq_iff (lam : R) (n : ℕ) :
    (gegenbauer lam n).degree = n ↔ algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval lam * 2 ^ n ≠ 0 := by
  constructor
  · intro h
    rw [← coeff_gegenbauer_self]
    exact coeff_ne_zero_of_eq_degree h
  · exact degree_gegenbauer_eq lam n

/-- The leading coefficient at nondegenerate parameters (DLMF Table 18.3.1). -/
theorem leadingCoeff_gegenbauer (lam : R) (n : ℕ)
    (h : algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval lam * 2 ^ n ≠ 0) :
    (gegenbauer lam n).leadingCoeff = algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval lam * 2 ^ n := by
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some (degree_gegenbauer_eq lam n h),
    coeff_gegenbauer_self]

/-- Positive-index Gegenbauer polynomials vanish at parameter zero, so this
specialisation is not a polynomial sequence (DLMF 18.5.10). -/
@[simp] theorem gegenbauer_zero_parameter {n : ℕ} (hn : n ≠ 0) :
    gegenbauer (0 : R) n = 0 := by
  unfold gegenbauer
  apply Finset.sum_eq_zero
  intro k hk
  have hnk : n - k ≠ 0 := by
    have := Finset.mem_range.mp hk
    omega
  simp [ascPochhammer_ne_zero_eval_zero R hnk]

end Polynomial
