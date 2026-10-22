/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Order.IntermediateValue

/-! # Polynomial alternation and degree
Strict sign alternation produces distinct intervening roots. This is the
algebraic obstruction behind ATAP, Theorem 10.1 and Exercise 10.3.
-/

public section
namespace Polynomial
open Set

/-- A strict sign change produces a root in the open interval. -/
theorem exists_eval_eq_zero_between_of_mul_neg {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hp : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hp with h | h
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨h.1, h.2⟩

/-- A polynomial changing sign in each of `n` consecutive intervals has degree
at least `n` (ATAP, proof of Theorem 10.1). -/
theorem le_natDegree_of_alternating_eval {n : ℕ} {p : ℝ[X]}
    {x : Fin (n + 1) → ℝ} (hx : StrictMono x)
    (hp : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    n ≤ p.natDegree := by
  by_cases hn : n = 0
  · omega
  have hex (i : Fin n) := exists_eval_eq_zero_between_of_mul_neg
    (hx (Fin.castSucc_lt_succ (i := i))) (hp i)
  choose z hz he using hex
  have hzmono : StrictMono z := by
    intro i j hij
    have hmid : x i.succ ≤ x j.castSucc := hx.monotone (by simpa using hij)
    exact hz i |>.2.trans_le hmid |>.trans (hz j).1
  by_contra hdeg
  have hpzero := p.eq_zero_of_natDegree_lt_card_of_eval_eq_zero hzmono.injective he
    (by simpa using Nat.lt_of_not_ge hdeg)
  have ht := hp ⟨0, by omega⟩
  simp [hpzero] at ht

end Polynomial
