/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex
import Mathlib.Tactic.FinCases

/-! # Finite separated labels and exponent pairs
Reference: Dunkl–Xu, §2.6.1. This is an index equivalence, not a degree assertion.
-/

public section
namespace MvPolynomial

/-- Separated labels and exponent pairs have the same finite cardinality. -/
noncomputable def separatedIndexEquiv (N : ℕ) :
    ((n : Fin (N+1)) × Fin (n.val+1)) ≃
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} where
  toFun i := ⟨Finsupp.single 0 (i.1.val-i.2.val)+Finsupp.single 1 i.2.val, by
    rw [sum_exponents_fin_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
      (by decide : (0 : Fin 2) ≠ 1), Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      zero_add, add_zero]
    omega⟩
  invFun d := ⟨⟨d.1 0+d.1 1, by have := d.2; rw [sum_exponents_fin_two] at this; omega⟩,
    ⟨d.1 1, by change d.1 1 < d.1 0+d.1 1+1; omega⟩⟩
  left_inv i := by
    apply Sigma.ext
    · apply Fin.ext
      simp
      omega
    · apply (Fin.heq_ext_iff (by simp; omega)).mpr
      simp
  right_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

end MvPolynomial
