/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Rat.Cast.Defs

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Nontriviality

/-!
# Jacobi polynomials over a rational algebra

The explicit expansion only divides by rational constants. It therefore includes
exceptional parameters at which the degree drops.
Reference: DLMF 18.5.7, https://dlmf.nist.gov/18.5#E7.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Jacobi polynomials in DLMF normalisation (DLMF 18.5.7). -/
noncomputable def jacobi (α β : R) (n : ℕ) : R[X] :=
  ∑ l ∈ Finset.range (n + 1),
    C (algebraMap ℚ R (((l.factorial : ℚ) * (n - l).factorial * 2 ^ l)⁻¹) *
      (ascPochhammer R l).eval ((n : R) + α + β + 1) *
      (ascPochhammer R (n - l)).eval (α + l + 1)) * (X - 1) ^ l

/-- The constant member is one (DLMF 18.5.7). -/
@[simp] theorem jacobi_zero (α β : R) : jacobi α β 0 = 1 := by
  simp [jacobi]

/-- The first member, valid even when its leading coefficient vanishes
(DLMF 18.5.7). -/
theorem jacobi_one (α β : R) :
    jacobi α β 1 = C (α + 1) +
      C (algebraMap ℚ R (1 / 2) * (α + β + 2)) * (X - 1) := by
  simp only [one_div, jacobi, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.sub_zero, Nat.sub_self,
    Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, one_mul, mul_one,
    inv_one, map_one, ascPochhammer_zero, ascPochhammer_one, eval_one, eval_X,
    add_zero]
  congr 2
  ring_nf

/-- The natural degree never exceeds the index (DLMF Table 18.3.1). -/
theorem natDegree_jacobi_le (α β : R) (n : ℕ) : (jacobi α β n).natDegree ≤ n := by
  nontriviality R
  unfold jacobi
  apply natDegree_sum_le_of_forall_le
  intro l hl
  apply (natDegree_C_mul_le _ _).trans
  have hpow : ((X - 1 : R[X]) ^ l).natDegree = l := by
    rw [← C_1, (monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [hpow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hl)

/-- The degree bound also handles the zero polynomial (DLMF Table 18.3.1). -/
theorem degree_jacobi_le (α β : R) (n : ℕ) : (jacobi α β n).degree ≤ n :=
  degree_le_of_natDegree_le (natDegree_jacobi_le α β n)

/-- The coefficient of the potentially leading term (DLMF Table 18.3.1). -/
theorem coeff_jacobi_self (α β : R) (n : ℕ) :
    (jacobi α β n).coeff n =
      algebraMap ℚ R (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
        (ascPochhammer R n).eval ((n : R) + α + β + 1) := by
  nontriviality R
  unfold jacobi
  rw [finsetSum_coeff, Finset.sum_eq_single n]
  · have hpow : ((X - 1 : R[X]) ^ n).coeff n = 1 := by
      have hd : ((X - 1 : R[X]) ^ n).natDegree = n := by
        rw [← C_1, (monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
      simpa [hd] using ((monic_X_sub_C (1 : R)).pow n).coeff_natDegree
    simp only [coeff_C_mul, hpow, Nat.sub_self, ascPochhammer_zero, eval_one,
      mul_one, Nat.factorial_zero, Nat.cast_one]
  · intro l hl hln
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    have hd : ((X - 1 : R[X]) ^ l).natDegree = l := by
      rw [← C_1, (monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [hd]
    have := Finset.mem_range.mp hl
    omega
  · simp

/-- Nonvanishing of the top coefficient gives exact degree, including over rings
with zero divisors (DLMF Table 18.3.1). -/
theorem degree_jacobi_eq (α β : R) (n : ℕ)
    (h : algebraMap ℚ R (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
      (ascPochhammer R n).eval ((n : R) + α + β + 1) ≠ 0) :
    (jacobi α β n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_jacobi_le α β n)
    (by rwa [coeff_jacobi_self])

/-- Exact degree is equivalent to the explicit nondegeneracy condition
(DLMF Table 18.3.1). -/
theorem degree_jacobi_eq_iff (α β : R) (n : ℕ) :
    (jacobi α β n).degree = n ↔
      algebraMap ℚ R (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
        (ascPochhammer R n).eval ((n : R) + α + β + 1) ≠ 0 := by
  constructor
  · intro h
    rw [← coeff_jacobi_self]
    exact coeff_ne_zero_of_eq_degree h
  · exact degree_jacobi_eq α β n

/-- The leading coefficient in the nondegenerate case (DLMF Table 18.3.1). -/
theorem leadingCoeff_jacobi (α β : R) (n : ℕ)
    (h : algebraMap ℚ R (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
      (ascPochhammer R n).eval ((n : R) + α + β + 1) ≠ 0) :
    (jacobi α β n).leadingCoeff = algebraMap ℚ R (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
      (ascPochhammer R n).eval ((n : R) + α + β + 1) := by
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some (degree_jacobi_eq α β n h),
    coeff_jacobi_self]

/-- The endpoint normalisation (DLMF Table 18.6.1). -/
@[simp] theorem eval_jacobi_one (α β : R) (n : ℕ) :
    (jacobi α β n).eval 1 = algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval (α + 1) := by
  unfold jacobi
  rw [eval_finsetSum, Finset.sum_eq_single 0]
  · simp
  · intro l hl hl0
    simp [hl0]
  · simp

end Polynomial
