/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Reduced
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The parameter-zero limit of Gegenbauer polynomials

For `n ≥ 1` and real `x`, `C_n^{(λ)}(x) / λ → (2/n) T_n(x)` as `λ → 0` with `λ ≠ 0`.
This is the limit behind the convention `C_n^{(0)} = (2/n) T_n` (DLMF 18.1.1,
18.7(iii)); `gegenbauer 0 n` itself is zero for `n ≥ 1`.
-/

public section

open Filter Topology

namespace Polynomial

/-- Reduced Gegenbauer polynomials depend continuously on a real parameter
(DLMF 18.5.10). -/
theorem continuous_eval_gegenbauerReduced (n : ℕ) (x : ℝ) :
    Continuous fun lam : ℝ ↦ (gegenbauerReduced lam n).eval x := by
  simp only [gegenbauerReduced, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

/-- Divided by `λ`, real Gegenbauer polynomials tend to `(2/n) T_n` as `λ → 0`,
`λ ≠ 0`, for `n ≥ 1` (DLMF 18.1.1, 18.7(iii)). -/
theorem tendsto_eval_gegenbauer_div_nhdsNE_zero {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    Tendsto (fun lam : ℝ ↦ (gegenbauer lam n).eval x / lam) (𝓝[≠] 0)
      (𝓝 (2 / n * (Chebyshev.T ℝ n).eval x)) := by
  have h0 : (gegenbauerReduced (0 : ℝ) n).eval x = 2 / n * (Chebyshev.T ℝ n).eval x := by
    have h := congrArg (eval x) (natCast_mul_gegenbauerReduced_zero (R := ℝ) hn)
    simp only [eval_mul, eval_natCast, eval_ofNat] at h
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    linarith
  rw [← h0]
  refine ((continuous_eval_gegenbauerReduced n x).tendsto 0).mono_left nhdsWithin_le_nhds
    |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [gegenbauer_eq_C_mul_gegenbauerReduced lam hn, eval_mul, eval_C,
    mul_div_cancel_left₀ _ hlam]

end Polynomial
