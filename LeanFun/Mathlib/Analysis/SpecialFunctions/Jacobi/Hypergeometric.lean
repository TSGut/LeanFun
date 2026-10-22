/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.TerminatingDomain

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The terminating hypergeometric representation of Jacobi polynomials

The denominator condition is finite: only the rising factorial through the
polynomial degree must be nonzero. Reference: DLMF 18.5.7.
-/

public section
namespace Polynomial

private theorem jacobi_hypergeometric_term {R : Type*} [Field R] [CharZero R] [Algebra ℚ R]
    (α β x : R) (n k : ℕ) (hk : k ≤ n)
    (hc : (ascPochhammer R n).eval (α + 1) ≠ 0) :
    algebraMap ℚ R (((k.factorial : ℚ) * (n - k).factorial * 2 ^ k)⁻¹) *
      (ascPochhammer R k).eval ((n : R) + α + β + 1) *
      (ascPochhammer R (n - k)).eval (α + k + 1) * (x - 1) ^ k =
    (ascPochhammer R n).eval (α + 1) / n.factorial *
      ordinaryHypergeometricCoefficient (-(n : R)) (n + α + β + 1) (α + 1) k *
      ((1 - x) / 2) ^ k := by
  have hp := congrArg (fun p : R[X] ↦ p.eval (α + 1))
    (ascPochhammer_mul R k (n - k))
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, Nat.add_sub_of_le hk] at hp
  have hs : α + 1 + (k : R) = α + k + 1 := by ring
  rw [hs] at hp
  have hck : (ascPochhammer R k).eval (α + 1) ≠ 0 := by
    intro hz
    apply hc
    rw [← hp, hz, zero_mul]
  have hf : ((n - k).factorial : R) * n.descFactorial k = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hn : (n.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hnk : ((n - k).factorial : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hkk : (k.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have ht : (2 : R) ≠ 0 := by norm_num
  have he : (ascPochhammer R k).eval (-(n : R)) * ((1 - x) / 2) ^ k =
      (n.descFactorial k : R) * ((x - 1) / 2) ^ k := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
    calc
      _ = (n.descFactorial k : R) * ((-1) * ((1 - x) / 2)) ^ k := by
        rw [mul_pow]; ring
      _ = _ := by congr 2; ring
  unfold ordinaryHypergeometricCoefficient
  simp only [map_inv₀, map_mul, map_natCast, map_pow, map_ofNat]
  calc
    _ = (ascPochhammer R n).eval (α + 1) / n.factorial *
        ((k.factorial : R)⁻¹ * (ascPochhammer R k).eval ((n : R) + α + β + 1) *
          ((ascPochhammer R k).eval (α + 1))⁻¹) *
          ((n.descFactorial k : R) * ((x - 1) / 2) ^ k) := by
      rw [← hp, div_pow]
      field_simp
      linear_combination -(ascPochhammer R k).eval ((n : R) + α + β + 1) *
        (ascPochhammer R (n - k)).eval (α + k + 1) * (x - 1) ^ k * hf
    _ = _ := by rw [← he]; ring



/-- The finite Jacobi representation with only certified classical coefficients. -/
theorem eval_jacobi_eq_hypergeometric_sum {R : Type*} [Field R] [CharZero R]
    [Algebra ℚ R] (α β x : R) (n : ℕ)
    (hc : (ascPochhammer R n).eval (α + 1) ≠ 0) :
    (jacobi α β n).eval x = (ascPochhammer R n).eval (α + 1) / n.factorial *
      ∑ k ∈ Finset.range (n + 1),
        ordinaryHypergeometricCoefficientOn
          (GaussParameters.ofTerminating (-(n : R)) (n + α + β + 1) (α + 1) n (Or.inl rfl) hc) k *
          ((1 - x) / 2) ^ k := by
  rw [jacobi, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hck := GaussParameters.pochhammer_ne_zero_of_le (α + 1) hc hkn
  rw [ordinaryHypergeometricCoefficientOn_eq_div _ k hck]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one,
    GaussParameters.ofTerminating]
  simpa only [ordinaryHypergeometricCoefficient, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_left_comm, mul_comm] using
    jacobi_hypergeometric_term α β x n k hkn hc


/-- Jacobi's terminating classical Gauss representation with its original finite admissibility. -/
theorem eval_jacobi_eq_ordinaryHypergeometric {𝕂 : Type*} [RCLike 𝕂]
    (α β x : 𝕂) (n : ℕ) (hc : (ascPochhammer 𝕂 n).eval (α + 1) ≠ 0) :
    (jacobi α β n).eval x = (ascPochhammer 𝕂 n).eval (α + 1) / n.factorial *
      ordinaryHypergeometricOn (GaussParameters.ofTerminating (-(n : 𝕂)) (n + α + β + 1) (α + 1) n (Or.inl rfl) hc)
        (.ofTerminating _ n (Or.inl rfl) ((1 - x) / 2)) := by
  rw [ordinaryHypergeometricOn_terminating]
  exact eval_jacobi_eq_hypergeometric_sum α β x n hc


end Polynomial
