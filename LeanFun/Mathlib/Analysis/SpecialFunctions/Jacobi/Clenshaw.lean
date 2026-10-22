/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Clenshaw
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Jacobi Clenshaw evaluation in the orthogonality range

All recurrence denominators are strictly positive for real `α, β > -1`.
References: Clenshaw (1955); DLMF 18.9.1--2 and §18.40(i).
-/

public section

namespace Polynomial

/-- Positivity in the real orthogonality range certifies every finite input. -/
theorem JacobiClenshawInput.of_neg_one_lt {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) : JacobiClenshawInput α β n := by
  apply JacobiClenshawInput.ofDenominators
  intro k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h₁ : (0 : ℝ) < k + α + β + 2 := by linarith
  have h₂ : (0 : ℝ) < 2 * k + α + β + 2 := by linarith
  positivity

/-- Throughout the real orthogonality range, no extra division conditions are needed. -/
theorem clenshawJacobi_eq_sum_of_neg_one_lt {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    clenshawJacobi α β x c n (JacobiClenshawInput.of_neg_one_lt hα hβ n) =
      ∑ i ∈ Finset.range n, c i * (jacobi α β i).eval x := by
  have hd (k : ℕ) :
      2 * (k + 2 : ℝ) * (k + α + β + 2) * (2 * k + α + β + 2) ≠ 0 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h₁ : (0 : ℝ) < k + α + β + 2 := by linarith
    have h₂ : (0 : ℝ) < 2 * k + α + β + 2 := by linarith
    positivity
  exact clenshawJacobi_eq_sum α β x c hd n


end Polynomial
