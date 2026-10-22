/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.FiniteClenshaw
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Recurrence

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Clenshaw evaluation of Jacobi expansions

The denominator for the recurrence from degrees `k, k + 1` to `k + 2` is
`2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2)`.
Nonvanishing is explicit over a field and automatic for real `α, β > -1`.
The degree-one value is supplied directly, including when `α + β = -1`.
References: Clenshaw (1955); DLMF 18.9.1--2 and §18.40(i).
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Classical denominators needed by the first `n` Jacobi coefficients. -/
structure JacobiClenshawInput (α β : K) (n : ℕ) : Prop where
  two_ne_zero : 2 ≤ n → (2 : K) ≠ 0
  denominator_ne_zero : ∀ i : Fin (n - 2),
    2 * (i.val + 2 : K) * (i.val + α + β + 2) * (2 * i.val + α + β + 2) ≠ 0

/-- Global recurrence nonvanishing supplies every finite input. -/
theorem JacobiClenshawInput.ofDenominators (α β : K)
    (hd : ∀ k : ℕ, 2 * (k + 2 : K) * (k + α + β + 2) * (2 * k + α + β + 2) ≠ 0)
    (n : ℕ) : JacobiClenshawInput α β n := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  exact ⟨fun _ ↦ by norm_num, fun i ↦ hd i.val⟩

/-- Finite Jacobi evaluation; empty and constant expansions need no division.
References: Clenshaw (1955), DLMF 18.9.1--2. -/
def clenshawJacobi (α β x : K) (c : ℕ → K) (n : ℕ)
    (_d : JacobiClenshawInput α β n) : K :=
  match n with
  | 0 => 0
  | 1 => c 0
  | m + 2 => finiteClenshaw (m + 2)
    (fun k ↦ (2 * k.val + α + β + 3) *
      ((2 * k.val + α + β + 2) * (2 * k.val + α + β + 4) * x + (α ^ 2 - β ^ 2)) /
        (2 * (k.val + 2) * (k.val + α + β + 2) * (2 * k.val + α + β + 2)))
    (fun k ↦ -(2 * (k.val + α + 1) * (k.val + β + 1) * (2 * k.val + α + β + 4)) /
      (2 * (k.val + 2) * (k.val + α + β + 2) * (2 * k.val + α + β + 2)))
    (fun i ↦ c i.val) 1 ((α + 1) + (α + β + 2) / 2 * (x - 1))

omit [Algebra ℚ K] in
private theorem clenshawJacobi_eq_clenshaw (α β x : K) (c : ℕ → K) (n : ℕ)
    (d : JacobiClenshawInput α β n) :
    clenshawJacobi α β x c n d = clenshaw
    (fun k ↦ (2 * k + α + β + 3) *
      ((2 * k + α + β + 2) * (2 * k + α + β + 4) * x + (α ^ 2 - β ^ 2)) /
        (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2)))
    (fun k ↦ -(2 * (k + α + 1) * (k + β + 1) * (2 * k + α + β + 4)) /
      (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2)))
    c 1 ((α + 1) + (α + β + 2) / 2 * (x - 1)) n := by
  match n with
  | 0 => simp [clenshawJacobi]
  | 1 => simp [clenshawJacobi]
  | m + 2 =>
    exact finiteClenshaw_eq
      (fun k ↦ (2 * k + α + β + 3) *
        ((2 * k + α + β + 2) * (2 * k + α + β + 4) * x + (α ^ 2 - β ^ 2)) /
          (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2)))
      (fun k ↦ -(2 * (k + α + 1) * (k + β + 1) * (2 * k + α + β + 4)) /
        (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2)))
      c 1 ((α + 1) + (α + β + 2) / 2 * (x - 1)) (m + 2)

/-- Exact Jacobi evaluation wherever the forward recurrence denominators are nonzero. -/
theorem clenshawJacobi_eq_sum (α β x : K) (c : ℕ → K)
    (hd : ∀ k : ℕ,
      2 * (k + 2 : K) * (k + α + β + 2) * (2 * k + α + β + 2) ≠ 0) (n : ℕ) :
    clenshawJacobi α β x c n (JacobiClenshawInput.ofDenominators α β hd n) =
      ∑ i ∈ Finset.range n, c i * (jacobi α β i).eval x := by
  have hp (k : ℕ) : (jacobi α β (k + 2)).eval x =
      ((2 * k + α + β + 3) *
        ((2 * k + α + β + 2) * (2 * k + α + β + 4) * x + (α ^ 2 - β ^ 2)) /
          (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2))) *
        (jacobi α β (k + 1)).eval x +
      (-(2 * (k + α + 1) * (k + β + 1) * (2 * k + α + β + 4)) /
          (2 * (k + 2) * (k + α + β + 2) * (2 * k + α + β + 2))) *
        (jacobi α β k).eval x := by
    have h := congrArg (fun p : K[X] ↦ p.eval x) (jacobi_recurrence α β k)
    simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X] at h
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff (hd k)]
    linear_combination h
  have he := clenshaw_eq_sum _ _ c (fun k ↦ (jacobi α β k).eval x) hp n
  rw [clenshawJacobi_eq_clenshaw]
  simpa [jacobi_one, map_div, mul_comm, div_eq_mul_inv] using he

end Polynomial
