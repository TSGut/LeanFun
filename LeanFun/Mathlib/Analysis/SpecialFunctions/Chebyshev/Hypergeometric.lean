/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.TerminatingDomain

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Hypergeometric
public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Jacobi
public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Gegenbauer
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Reduced
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Hypergeometric representations of Chebyshev polynomials

The representations in `(1 - x)/2` follow from the Jacobi one (DLMF 18.5.11_2,
18.5.11_4). The representations in `1/x²` follow from the Gegenbauer one at
parameter one (DLMF 18.5.11_3) and from the reduced Gegenbauer polynomials at
parameter zero (DLMF 18.5.11_1). No hypothesis is needed beyond `x ≠ 0`, and `n ≥ 1`
for `T` in `1/x²`.
-/

public section

namespace Polynomial

variable {𝕂 : Type*} [RCLike 𝕂]

private theorem ascPochhammer_eval_ofReal_ne_zero (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (ascPochhammer 𝕂 n).eval (r : 𝕂) ≠ 0 := by
  rw [← RCLike.algebraMap_eq_ofReal, ← ascPochhammer_map (algebraMap ℝ 𝕂), eval_map,
    eval₂_at_apply, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_ne_zero]
  exact (ascPochhammer_pos n r hr).ne'





/-- Chebyshev's classical terminating Gauss representation, at every argument. -/
theorem eval_chebyshev_T_eq_ordinaryHypergeometric (x : 𝕂) (n : ℕ) :
    (Chebyshev.T 𝕂 n).eval x = ordinaryHypergeometricOn (GaussParameters.ofTerminating (-(n : 𝕂)) n (1 / 2) n (Or.inl rfl)
        (by have h := ascPochhammer_eval_ofReal_ne_zero (𝕂 := 𝕂) n (r := 1 / 2) (by norm_num); push_cast at h; exact h))
      (.ofTerminating _ n (Or.inl rfl) ((1 - x) / 2)) := by
  have hh : (ascPochhammer 𝕂 n).eval (1 / 2) ≠ 0 := by
    have h := ascPochhammer_eval_ofReal_ne_zero (𝕂 := 𝕂) n (r := 1 / 2) (by norm_num)
    push_cast at h
    exact h
  have hj := eval_jacobi_eq_ordinaryHypergeometric (-1 / 2 : 𝕂) (-1 / 2) x n
    (by rwa [show (-1 / 2 : 𝕂) + 1 = 1 / 2 by norm_num])
  rw [ordinaryHypergeometricOn_terminating] at hj ⊢
  simp only [ordinaryHypergeometricCoefficientOn, GaussParameters.ofTerminating] at hj ⊢
  have hb := congrArg (eval x) (jacobi_eq_chebyshev_T 𝕂 n)
  simp only [eval_mul, eval_C, map_div₀, map_neg, map_one, map_ofNat, map_inv₀,
    map_natCast] at hb
  simp only [show (-1 / 2 : 𝕂) + 1 = 1 / 2 by norm_num,
    show (n : 𝕂) + -1 / 2 + -1 / 2 + 1 = n by ring] at hj
  rw [hb] at hj
  have hnf : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hnf) hh)
  rw [hj]
  field_simp
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) * (ascPochhammer 𝕂 k).eval (n : 𝕂) = 0
  · simp only [h, ite_true]
  · simp only [h, ite_false]


/-- Chebyshev's classical terminating Gauss representation, at every argument. -/
theorem eval_chebyshev_U_eq_ordinaryHypergeometric (x : 𝕂) (n : ℕ) :
    (Chebyshev.U 𝕂 n).eval x = (n + 1) * ordinaryHypergeometricOn (GaussParameters.ofTerminating (-(n : 𝕂)) (n + 2) (3 / 2) n (Or.inl rfl)
        (by have h := ascPochhammer_eval_ofReal_ne_zero (𝕂 := 𝕂) n (r := 3 / 2) (by norm_num); push_cast at h; exact h))
      (.ofTerminating _ n (Or.inl rfl) ((1 - x) / 2)) := by
  have hh : (ascPochhammer 𝕂 n).eval (3 / 2) ≠ 0 := by
    have h := ascPochhammer_eval_ofReal_ne_zero (𝕂 := 𝕂) n (r := 3 / 2) (by norm_num)
    push_cast at h
    exact h
  have hj := eval_jacobi_eq_ordinaryHypergeometric (1 / 2 : 𝕂) (1 / 2) x n
    (by rwa [show (1 / 2 : 𝕂) + 1 = 3 / 2 by norm_num])
  rw [ordinaryHypergeometricOn_terminating] at hj ⊢
  simp only [ordinaryHypergeometricCoefficientOn, GaussParameters.ofTerminating] at hj ⊢
  have hb := congrArg (eval x) (jacobi_eq_chebyshev_U 𝕂 n)
  simp only [eval_mul, eval_C, map_div₀, map_one, map_ofNat, map_inv₀, map_natCast] at hb
  simp only [show (1 / 2 : 𝕂) + 1 = 3 / 2 by norm_num,
    show (n : 𝕂) + 1 / 2 + 1 / 2 + 1 = n + 2 by ring] at hj
  rw [hj] at hb
  have hnf : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hnf) hh)
  rw [← hb]
  field_simp
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) * (ascPochhammer 𝕂 k).eval ((n : 𝕂) + 2) = 0
  · simp only [h, ite_true]
  · simp only [h, ite_false]


/-- Chebyshev U's classical inverse-square representation, including degree zero. -/
theorem eval_chebyshev_U_eq_ordinaryHypergeometric_inv_sq (x : 𝕂ˣ) (n : ℕ) :
    (Chebyshev.U 𝕂 n).eval x.val =
      (2 * x.val) ^ n * ordinaryHypergeometricOn
        (GaussParameters.quadratic n (-(n : 𝕂))
          (GaussParameters.pochhammer_neg_nat_ne_zero n (n / 2) (Nat.div_le_self _ _)))
        (.ofTerminating _ (n / 2) (GaussParameters.quadratic_has_termination n _ _) (x.val ^ 2)⁻¹) := by
  have hc : (ascPochhammer 𝕂 (n / 2)).eval (1 - 1 - (n : 𝕂)) ≠ 0 := by
    rw [sub_self, zero_sub, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr ?_)
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have hnf : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← gegenbauer_one_eq_chebyshev_U, eval_gegenbauer_eq_ordinaryHypergeometric_inv_sq 1 x n hc,
    ascPochhammer_eval_one, div_self hnf, mul_one]
  rw [ordinaryHypergeometricOn_terminating, ordinaryHypergeometricOn_terminating]
  simp only [ordinaryHypergeometricCoefficientOn,
    GaussParameters.quadratic, GaussParameters.ofTerminating, sub_self, zero_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : (ascPochhammer 𝕂 k).eval (-(n : 𝕂) / 2) *
      (ascPochhammer 𝕂 k).eval ((1 - (n : 𝕂)) / 2) = 0
  · simp only [h, ite_true]
  · simp only [h, ite_false]


private theorem chebyshev_T_hypergeometric_inv_sq (x : 𝕂ˣ) (n : ℕ) (hn : n ≠ 0)
    (hc : (ascPochhammer 𝕂 (n / 2)).eval (1 - (n : 𝕂)) ≠ 0) :
    (Chebyshev.T 𝕂 n).eval x.val =
      2 ^ (n - 1) * x.val ^ n * ordinaryHypergeometricOn
        (GaussParameters.quadratic n (1 - (n : 𝕂)) hc)
        (.ofTerminating _ (n / 2) (GaussParameters.quadratic_has_termination n _ _)
          (x.val ^ 2)⁻¹) := by
  have hq := two_mul_pow_mul_ordinaryHypergeometric_inv_sq n ⟨1 - (n : 𝕂), hc⟩ x
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
    (n.factorial : 𝕂) / (k.factorial * (n - 2 * k).factorial) *
      ((ascPochhammer 𝕂 k).eval (1 - (n : 𝕂)))⁻¹ * (2 * x.val) ^ (n - 2 * k))
      (n / 2 + 1)] at hq

  have hT := congrArg (eval x.val) (natCast_mul_gegenbauerReduced_zero (R := 𝕂) hn)
  simp only [eval_mul, eval_natCast, eval_ofNat] at hT
  have h2 : (2 : 𝕂) ^ (n - 1) * x.val ^ n = (2 * x.val) ^ n / 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_sub_one, mul_pow, pow_succ (2 : 𝕂) m]
    ring
  have hTR : (Chebyshev.T 𝕂 n).eval x.val = n * (gegenbauerReduced (0 : 𝕂) n).eval x.val / 2 := by
    rw [hT]
    ring
  rw [h2, div_mul_eq_mul_div, hq, hTR,
    gegenbauerReduced, eval_finsetSum, Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have hrefl : (ascPochhammer 𝕂 k).eval (1 - (n : 𝕂)) = (-1) ^ k * ((n - 1).descFactorial k : 𝕂) := by
    rw [show (1 : 𝕂) - n = -((n - 1 : ℕ) : 𝕂) by
        push_cast [Nat.one_le_iff_ne_zero.mpr hn]
        ring,
      ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have hf : ((n - 1 - k).factorial : 𝕂) * (n - 1).descFactorial k = (n - 1).factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial (by omega : k ≤ n - 1)
  have hnn : (n.factorial : 𝕂) = n * (n - 1).factorial := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_sub_one, Nat.factorial_succ]
    push_cast
    ring
  have hone : (ascPochhammer 𝕂 (n - k - 1)).eval (0 + 1) = ((n - 1 - k).factorial : 𝕂) := by
    rw [zero_add, ascPochhammer_eval_one, show n - k - 1 = n - 1 - k by omega]
  have hd : ((n - 1).descFactorial k : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega)
  have hkf : (k.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnf : ((n - 2 * k).factorial : 𝕂) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : ((-1 : 𝕂) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg, inv_one]
  simp only [eval_mul, eval_C, eval_pow, eval_X, map_inv₀, map_mul, map_natCast, eval_natCast, hone, hrefl]
  rw [mul_inv ((-1 : 𝕂) ^ k), hs, hnn, ← hf]
  field_simp




/-- Chebyshev T's classical inverse-square representation at positive degree. -/
theorem eval_chebyshev_T_eq_ordinaryHypergeometric_inv_sq (x : 𝕂ˣ) (n : ℕ+) :
    (Chebyshev.T 𝕂 (n : ℕ)).eval x.val =
      2 ^ ((n : ℕ) - 1) * x.val ^ (n : ℕ) * ordinaryHypergeometricOn
        (GaussParameters.quadratic (n : ℕ) (1 - ((n : ℕ) : 𝕂)) (by
          have hn : 1 ≤ (n : ℕ) := n.pos
          rw [show (1 : 𝕂) - (n : ℕ) = -(((n : ℕ) - 1 : ℕ) : 𝕂) by
            push_cast [hn]; ring]
          exact GaussParameters.pochhammer_neg_nat_ne_zero ((n : ℕ) - 1) ((n : ℕ) / 2)
            (by omega)))
        (.ofTerminating _ ((n : ℕ) / 2) (GaussParameters.quadratic_has_termination (n : ℕ) _ _)
          (x.val ^ 2)⁻¹) := by
  exact chebyshev_T_hypergeometric_inv_sq x n n.ne_zero (by
    have hn : 1 ≤ (n : ℕ) := n.pos
    rw [show (1 : 𝕂) - (n : ℕ) = -(((n : ℕ) - 1 : ℕ) : 𝕂) by
      push_cast [hn]; ring]
    exact GaussParameters.pochhammer_neg_nat_ne_zero ((n : ℕ) - 1) ((n : ℕ) / 2)
      (by omega))


end Polynomial
