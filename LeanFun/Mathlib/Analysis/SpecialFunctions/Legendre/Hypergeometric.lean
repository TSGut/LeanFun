/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.TerminatingDomain

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Hypergeometric
public import LeanFun.Mathlib.RingTheory.Polynomial.Legendre.Jacobi

/-!
# Hypergeometric representation of Legendre polynomials

The Jacobi representation at `α = β = 0` (DLMF 18.5.7, Table 18.3.1).
-/

public section

namespace Polynomial


/-- Legendre's classical terminating Gauss representation, at every argument. -/
theorem eval_legendre_eq_ordinaryHypergeometric {𝕂 : Type*} [RCLike 𝕂] (x : 𝕂) (n : ℕ) :
    (legendre 𝕂 n).eval x = ordinaryHypergeometricOn (GaussParameters.ofTerminating (-(n : 𝕂)) (n + 1) 1 n (Or.inl rfl)
        (by simpa only [ascPochhammer_eval_one] using (Nat.cast_ne_zero.mpr n.factorial_ne_zero : (n.factorial : 𝕂) ≠ 0)))
      (.ofTerminating _ n (Or.inl rfl) ((1 - x) / 2)) := by
  have hnf : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h := eval_jacobi_eq_ordinaryHypergeometric (0 : 𝕂) 0 x n
    (by rwa [zero_add, ascPochhammer_eval_one])
  rw [ordinaryHypergeometricOn_terminating] at h ⊢
  simp only [ordinaryHypergeometricCoefficientOn, GaussParameters.ofTerminating] at h ⊢
  rw [legendre_eq_jacobi]
  simpa only [zero_add, ascPochhammer_eval_one, div_self hnf, one_mul,
    add_zero] using h


end Polynomial
