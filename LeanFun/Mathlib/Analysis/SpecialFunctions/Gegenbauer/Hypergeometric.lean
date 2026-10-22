/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.TerminatingDomain

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Hypergeometric
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Jacobi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Hypergeometric representations of Gegenbauer polynomials

The representation in the variable `(1 - x)/2` follows from the Jacobi one
(DLMF 18.5.9). The representation in `1/x²` is a reindexing of the defining
sum (DLMF 18.5.10). Both are terminating-series identities with explicit
finite conditions on the denominator rising factorials.
-/

public section

namespace Polynomial

/-- Legendre duplication for rising factorials, with denominators cleared:
`4^k (a)_k (a + 1/2)_k = (2a)_{2k}` (DLMF 5.2.8). -/
theorem four_pow_mul_ascPochhammer_eval_mul_eval_add_half {K : Type*} [Field K]
    [CharZero K] (a : K) (k : ℕ) :
    4 ^ k * ((ascPochhammer K k).eval a * (ascPochhammer K k).eval (a + 1 / 2)) =
      (ascPochhammer K (2 * k)).eval (2 * a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, ascPochhammer_succ_eval,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← ih]
    push_cast
    ring




/-- Gegenbauer's classical terminating Gauss representation. -/
theorem eval_gegenbauer_eq_ordinaryHypergeometric {𝕂 : Type*} [RCLike 𝕂]
    (lam x : 𝕂) (n : ℕ) (hc : (ascPochhammer 𝕂 n).eval (lam + 1 / 2) ≠ 0) :
    (gegenbauer lam n).eval x = (ascPochhammer 𝕂 n).eval (2 * lam) / n.factorial *
      ordinaryHypergeometricOn (GaussParameters.ofTerminating (-(n : 𝕂)) (n + 2 * lam) (lam + 1 / 2) n (Or.inl rfl) hc)
        (.ofTerminating _ n (Or.inl rfl) ((1 - x) / 2)) := by
  have e1 : lam - 1 / 2 + 1 = lam + 1 / 2 := by ring
  have e2 : (n : 𝕂) + (lam - 1 / 2) + (lam - 1 / 2) + 1 = n + 2 * lam := by ring
  have hb := congrArg (eval x) (gegenbauer_jacobi lam n)
  have hj := eval_jacobi_eq_ordinaryHypergeometric (lam - 1 / 2) (lam - 1 / 2) x n
    (by rwa [e1])
  rw [ordinaryHypergeometricOn_terminating] at hj ⊢
  simp only [ordinaryHypergeometricCoefficientOn, GaussParameters.ofTerminating] at hj ⊢
  have h12 : algebraMap ℚ 𝕂 (1 / 2) = 1 / 2 := by simp
  simp only [eval_mul, eval_C, h12] at hb
  simp only [e1, e2] at hj
  rw [hj] at hb
  apply mul_left_cancel₀ hc
  rw [hb]
  ring_nf


/-- The quadratic reindexing uses only nonzero arguments and finite admissible denominators. -/
theorem two_mul_pow_mul_ordinaryHypergeometric_inv_sq {𝕂 : Type*} [RCLike 𝕂]
    (n : ℕ) (c : {c : 𝕂 // (ascPochhammer 𝕂 (n / 2)).eval c ≠ 0}) (x : 𝕂ˣ) :
    (2 * x.val) ^ n * ordinaryHypergeometricOn (GaussParameters.quadratic n c.val c.property)
      (.ofTerminating _ (n / 2) (GaussParameters.quadratic_has_termination n _ _) (x.val ^ 2)⁻¹) =
      ∑ k : Fin (n / 2 + 1),
        (n.factorial : 𝕂) / (k.val.factorial * (n - 2 * k.val).factorial) *
          ((ascPochhammer 𝕂 k.val).eval c.val)⁻¹ * (2 * x.val) ^ (n - 2 * k.val) := by
  rw [ordinaryHypergeometricOn_terminating]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
    (n.factorial : 𝕂) / (k.factorial * (n - 2 * k).factorial) *
      ((ascPochhammer 𝕂 k).eval c.val)⁻¹ * (2 * x.val) ^ (n - 2 * k)) (n / 2 + 1)]
  have hd (k : ℕ) : 4 ^ k * ((ascPochhammer 𝕂 k).eval (-(n : 𝕂) / 2) *
      (ascPochhammer 𝕂 k).eval ((1 - (n : 𝕂)) / 2)) = (n.descFactorial (2 * k) : 𝕂) := by
    rw [show ((1 : 𝕂) - n) / 2 = -(n : 𝕂) / 2 + 1 / 2 by ring,
      four_pow_mul_ascPochhammer_eval_mul_eval_add_half,
      show 2 * (-(n : 𝕂) / 2) = -(n : 𝕂) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial, pow_mul]
    norm_num
  have h4 (k : ℕ) : (4 : 𝕂) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hck := GaussParameters.pochhammer_ne_zero_of_le c.val c.property
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  rw [ordinaryHypergeometricCoefficientOn_eq_div _ k hck]
  simp only [GaussParameters.quadratic, GaussParameters.ofTerminating]
  have hk : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have hf : ((n - 2 * k).factorial : 𝕂) * n.descFactorial (2 * k) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hpow : (2 * x.val) ^ n = (2 * x.val) ^ (n - 2 * k) * (4 ^ k * (x.val ^ 2) ^ k) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_add, pow_mul]
    ring
  have hkf : (k.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnf : ((n - 2 * k).factorial : 𝕂) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hx2 : (x.val ^ 2) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Units.ne_zero x))
  rw [hpow, ← hf, ← hd k, inv_pow]
  field_simp


/-- Gegenbauer's classical inverse-square representation on its exact stated domain. -/
theorem eval_gegenbauer_eq_ordinaryHypergeometric_inv_sq {𝕂 : Type*} [RCLike 𝕂]
    (lam : 𝕂) (x : 𝕂ˣ) (n : ℕ)
    (hc : (ascPochhammer 𝕂 (n / 2)).eval (1 - lam - n) ≠ 0) :
    (gegenbauer lam n).eval x.val =
      (2 * x.val) ^ n * ((ascPochhammer 𝕂 n).eval lam / n.factorial) *
        ordinaryHypergeometricOn (GaussParameters.quadratic n (1 - lam - n) hc)
          (.ofTerminating _ (n / 2) (GaussParameters.quadratic_has_termination n _ _) (x.val ^ 2)⁻¹) := by
  have hq := two_mul_pow_mul_ordinaryHypergeometric_inv_sq n ⟨1 - lam - n, hc⟩ x
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
    (n.factorial : 𝕂) / (k.factorial * (n - 2 * k).factorial) *
      ((ascPochhammer 𝕂 k).eval (1 - lam - n))⁻¹ * (2 * x.val) ^ (n - 2 * k))
      (n / 2 + 1)] at hq

  rw [mul_comm ((2 * x.val) ^ n), mul_assoc, hq,
    Finset.mul_sum, gegenbauer, eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  -- `(λ)_n = (λ)_{n-k} (λ+n-k)_k` and `(1-λ-n)_k = (-1)^k (λ+n-k)_k`.
  have hsplit := congrArg (eval lam) (ascPochhammer_mul 𝕂 (n - k) k)
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast,
    Nat.sub_add_cancel (by omega : k ≤ n)] at hsplit
  have hrefl : (ascPochhammer 𝕂 k).eval (1 - lam - n) =
      (-1) ^ k * (ascPochhammer 𝕂 k).eval (lam + (n - k : ℕ)) := by
    rw [show (1 : 𝕂) - lam - n = -(lam + n - 1) by ring,
      ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
    congr 2
    push_cast [show k ≤ n by omega]
    ring
  have hck : (ascPochhammer 𝕂 k).eval (1 - lam - n) ≠ 0 := by
    intro hz
    apply hc
    have hm := congrArg (eval (1 - lam - n)) (ascPochhammer_mul 𝕂 k (n / 2 - k))
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, hz, zero_mul,
      Nat.add_sub_cancel' (by omega : k ≤ n / 2)] at hm
    exact hm.symm
  have hkf : (k.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnf : ((n - 2 * k).factorial : 𝕂) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnn : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hrefl] at hck ⊢
  simp only [eval_mul, eval_C, eval_pow, eval_X, map_inv₀, map_mul, map_natCast,
    ← hsplit]
  have hck' : (ascPochhammer 𝕂 k).eval (lam + (n - k : ℕ)) ≠ 0 := by
    intro hz; apply hck; rw [hz, mul_zero]
  have hs : ((-1 : 𝕂) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg, inv_one]
  rw [mul_inv ((-1 : 𝕂) ^ k), hs]
  field_simp


end Polynomial
