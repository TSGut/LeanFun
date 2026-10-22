/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Rational polynomial identities from real specializations

A polynomial identity in formal rational parameters can be checked on a real
box with infinite sides. This supports transferring analytically proved classical
identities to arbitrary rational algebras. Reference: polynomial identity principle.
-/

public section
namespace Polynomial

/-- Equality on an infinite-sided real box determines a polynomial with formal
rational parameters. -/
theorem eq_of_map_eval₂_eq_on {σ : Type*} {p q : Polynomial (MvPolynomial σ ℚ)}
    (s : σ → Set ℝ) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi Set.univ s,
      p.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x) =
        q.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x)) : p = q := by
  ext n : 1
  apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
  apply MvPolynomial.funext_set s hs
  intro x hx
  have hc := congrArg (fun p : ℝ[X] ↦ p.coeff n) (h x hx)
  simpa only [coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map] using hc

end Polynomial
