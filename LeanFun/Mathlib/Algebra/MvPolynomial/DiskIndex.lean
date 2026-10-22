/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases

/-! # Indexing bivariate total-degree blocks
Exponent pairs correspond to total degree and inner degree.
-/

public section
namespace MvPolynomial

/-- The sum of exponents in two variables. -/
theorem sum_exponents_fin_two (d : Fin 2 →₀ ℕ) :
    d.sum (fun _ e => e) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype]
  · simp
  · simp

/-- Exponent pairs identify distinct degree/inner-index pairs. -/
theorem diskIndex_injective : Function.Injective
    (fun d : Fin 2 →₀ ℕ => (⟨d 0 + d 1, ⟨d 1, by omega⟩⟩ : Σ n : ℕ, Fin (n + 1))) := by
  intro d e h
  have hn := congrArg Sigma.fst h
  have hk := congrArg (fun i : Σ n : ℕ, Fin (n + 1) => (i.2 : ℕ)) h
  ext i
  fin_cases i <;> dsimp at hn hk ⊢ <;> omega

end MvPolynomial
