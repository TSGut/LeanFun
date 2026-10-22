/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.Basic

/-! # Polynomial composition and partial derivatives -/

public section
namespace MvPolynomial

/-- The chain rule for a univariate polynomial evaluated at a multivariate polynomial. -/
theorem pderiv_polynomial_eval₂_C {R σ : Type*} [CommRing R] (i : σ)
    (p : Polynomial R) (q : MvPolynomial σ R) :
    pderiv i (p.eval₂ C q) = p.derivative.eval₂ C q * pderiv i q := by
  simpa only [Polynomial.aeval_def, algebraMap_eq, smul_eq_mul] using
    (pderiv i).map_aeval p q

end MvPolynomial
