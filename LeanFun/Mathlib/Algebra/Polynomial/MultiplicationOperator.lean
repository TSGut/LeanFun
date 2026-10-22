/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial multiplication as a polynomial in the coordinate operator
The identities hold on polynomials and finitely supported basis coordinates;
no finite matrix truncation or infinite matrix product is implicit.
Reference: Olver--Townsend (2013), Sections 2--3.
-/

public section
namespace Polynomial
variable {R : Type*} [CommSemiring R]

/-- Multiplication by `p` is `p(J)`, where `J` multiplies by `X`.
This is an identity of endomorphisms of the full polynomial module. -/
theorem aeval_mulLeft_X (p : R[X]) :
    aeval (LinearMap.mulLeft R (X : R[X])) p = LinearMap.mulLeft R p := by
  have he (q : R[X]) : Algebra.lmul R R[X] q = LinearMap.mulLeft R q := by
    ext r
    rfl
  simpa only [he, aeval_X_left_apply] using
    (aeval_algHom_apply (Algebra.lmul R R[X]) (X : R[X]) p)

/-- The existing same-basis coefficient map is conjugation by the basis equivalence. -/
theorem coefficientMap_eq_conj {ι : Type*} (b : Module.Basis ι R R[X])
    (L : Module.End R R[X]) : b.coefficientMap b L = b.repr.conjAlgEquiv R L := by
  rfl

/-- In any polynomial basis, multiplication coefficients satisfy `M[p]=p(J)`.
The operator acts on finitely supported coefficients, even for an infinite basis. -/
theorem coefficientMap_mulLeft_eq_aeval {ι : Type*} (b : Module.Basis ι R R[X]) (p : R[X]) :
    b.coefficientMap b (LinearMap.mulLeft R p) =
      aeval (b.coefficientMap b (LinearMap.mulLeft R (X : R[X]))) p := by
  rw [coefficientMap_eq_conj, coefficientMap_eq_conj,
    aeval_algHom_apply, aeval_mulLeft_X]

/-- Polynomial functional calculus reconstructs exact multiplication of every
finite coefficient vector (Olver--Townsend, Sections 2--3). -/
theorem repr_symm_aeval_mulLeft {ι : Type*} (b : Module.Basis ι R R[X])
    (p : R[X]) (v : ι →₀ R) :
    b.repr.symm ((aeval (b.coefficientMap b (LinearMap.mulLeft R (X : R[X]))) p) v) =
      p * b.repr.symm v := by
  rw [← coefficientMap_mulLeft_eq_aeval, b.repr_symm_coefficientMap]
  rfl

end Polynomial
