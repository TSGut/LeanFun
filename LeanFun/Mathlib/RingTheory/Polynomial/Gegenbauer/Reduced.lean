/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Recurrence
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Map
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.LinearCombination

/-!
# Reduced Gegenbauer polynomials and Chebyshev T at parameter zero

Every positive-degree Gegenbauer polynomial vanishes at `λ = 0`. Removing one
factor `λ` from each rising factorial, `(λ)_{n-k} = λ (λ + 1)_{n-k-1}`, gives
polynomials `R_n^{(λ)}` with `C_n^{(λ)} = λ R_n^{(λ)}` for `n ≥ 1`, and
`n R_n^{(0)} = 2 T_n`. This is the renormalisation behind the convention
`C_n^{(0)} = (2/n) T_n` of DLMF 18.1.1 and the limit in DLMF 18.7(iii).
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Gegenbauer sum (DLMF 18.5.10) with one factor `λ` removed from each rising
factorial, `(λ)_{n-k} = λ (λ + 1)_{n-k-1}` (DLMF 18.7(iii)). The value at `n = 0` is
the normalization `R₀ = 1`. The identity `Cₙ = λ Rₙ` applies only in positive degree. -/
noncomputable def gegenbauerReduced (lam : R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((-1) ^ k * algebraMap ℚ R (((k.factorial : ℚ) * (n - 2 * k).factorial)⁻¹) *
      (ascPochhammer R (n - k - 1)).eval (lam + 1)) * (C 2 * X) ^ (n - 2 * k)

/-- The degree-zero normalization of the reduced family is one. -/
@[simp] theorem gegenbauerReduced_zero (lam : R) : gegenbauerReduced lam 0 = 1 := by
  simp only [gegenbauerReduced, Nat.zero_div, zero_add, Finset.sum_range_one,
    pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, Nat.zero_sub,
    inv_one, map_one, ascPochhammer_zero, eval_one]

/-- Positive-degree Gegenbauer polynomials are `λ` times the reduced polynomials
(DLMF 18.5.10, 18.7(iii)). -/
theorem gegenbauer_eq_C_mul_gegenbauerReduced (lam : R) {n : ℕ} (hn : n ≠ 0) :
    gegenbauer lam n = C lam * gegenbauerReduced lam n := by
  unfold gegenbauer gegenbauerReduced
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hnk : n - k = n - k - 1 + 1 := by
    have := Finset.mem_range.mp hk
    omega
  conv_lhs => rw [hnk]
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]
  simp only [C_mul]
  ring

/-- Reduced Gegenbauer polynomials commute with rational algebra maps (DLMF 18.5.10). -/
theorem map_gegenbauerReduced {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →ₐ[ℚ] S)
    (lam : R) (n : ℕ) :
    (gegenbauerReduced lam n).map f.toRingHom = gegenbauerReduced (f lam) n := by
  have hp (k : ℕ) (x : R) : f ((ascPochhammer R k).eval x) =
      (ascPochhammer S k).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  simp only [gegenbauerReduced, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_ofNat, map_X,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, map_pow, map_neg, map_one,
    map_ofNat, map_add, hp,
    AlgHom.commutes]

private theorem gegenbauerReduced_recurrence_generic {n : ℕ} (hn : n ≠ 0) :
    C (n + 2 : ℚ[X]) * gegenbauerReduced (X : ℚ[X]) (n + 2) -
      C (2 * ((n : ℚ[X]) + X + 1)) * X * gegenbauerReduced (X : ℚ[X]) (n + 1) +
      C ((n : ℚ[X]) + 2 * X) * gegenbauerReduced (X : ℚ[X]) n = 0 := by
  have hr := gegenbauer_recurrence (X : ℚ[X]) n
  rw [gegenbauer_eq_C_mul_gegenbauerReduced _ hn,
    gegenbauer_eq_C_mul_gegenbauerReduced _ n.succ_ne_zero,
    gegenbauer_eq_C_mul_gegenbauerReduced _ (by omega : n + 2 ≠ 0)] at hr
  apply mul_left_cancel₀ (C_ne_zero.mpr (X_ne_zero : (X : ℚ[X]) ≠ 0))
  linear_combination hr

/-- The Gegenbauer recurrence divided by `λ`, valid from degree one
(DLMF Table 18.9.1, 18.7(iii)). -/
theorem gegenbauerReduced_recurrence (lam : R) {n : ℕ} (hn : n ≠ 0) :
    C (n + 2 : R) * gegenbauerReduced lam (n + 2) -
      C (2 * ((n : R) + lam + 1)) * X * gegenbauerReduced lam (n + 1) +
      C ((n : R) + 2 * lam) * gegenbauerReduced lam n = 0 := by
  have h := congrArg (Polynomial.map (aeval lam).toRingHom)
    (gegenbauerReduced_recurrence_generic hn)
  have hm (m : ℕ) := map_gegenbauerReduced (aeval lam) (X : ℚ[X]) m
  simp only [AlgHom.toRingHom_eq_coe, aeval_X] at hm h
  simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    map_X, Polynomial.map_zero, Polynomial.map_natCast, Polynomial.map_ofNat,
    Polynomial.map_one, hm, AlgHom.coe_toRingHom, map_add, map_mul, map_natCast, map_ofNat,
    map_one, aeval_X] using h

private theorem natCast_mul_gegenbauerReduced_zero_rat (m : ℕ) :
    ((m + 1 : ℕ) : ℚ[X]) * gegenbauerReduced (0 : ℚ) (m + 1) =
      2 * Chebyshev.T ℚ (m + 1 : ℕ) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    simp [gegenbauerReduced, map_ofNat]
  | one =>
    simp [gegenbauerReduced, Finset.sum_range_succ, Chebyshev.T_two]
    have h : (C (2 : ℚ)⁻¹ : ℚ[X]) * 2 = 1 := by
      rw [← map_ofNat C 2, ← C_mul]
      norm_num
    rw [map_ofNat C 2]
    linear_combination (2 * X ^ 2 : ℚ[X]) * h
  | more m h₀ h₁ =>
    have hr := gegenbauerReduced_recurrence (0 : ℚ) (n := m + 1) (by omega)
    rw [show m + 1 + 2 = m + 2 + 1 by omega] at hr
    have e3 : ((m + 2 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    have e2 : ((m + 1 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e3, Chebyshev.T_add_two, ← e2]
    push_cast at h₀ h₁ hr ⊢
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, mul_zero,
      add_zero] at hr
    linear_combination hr + 2 * X * h₁ - h₀

/-- At parameter zero, `n R_n^{(0)} = 2 T_n` for `n ≥ 1`. This is the Chebyshev T
normalisation `C_n^{(0)} = (2/n) T_n` of DLMF 18.1.1 (see DLMF 18.7(iii)). -/
theorem natCast_mul_gegenbauerReduced_zero {n : ℕ} (hn : n ≠ 0) :
    (n : R[X]) * gegenbauerReduced (0 : R) n = 2 * Chebyshev.T R n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let f : ℚ →ₐ[ℚ] R := Algebra.ofId ℚ R
  have h := congrArg (Polynomial.map f.toRingHom) (natCast_mul_gegenbauerReduced_zero_rat m)
  simpa only [Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_ofNat,
    map_gegenbauerReduced, map_zero, Chebyshev.map_T] using h

end Polynomial
