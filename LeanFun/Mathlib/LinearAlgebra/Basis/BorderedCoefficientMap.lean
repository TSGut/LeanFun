/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap

/-! # Exact boundary bordering on finite coefficients
A boundary map and a residual map are assembled without asserting existence or
uniqueness of solutions. Reference: Olver--Townsend (2013), §2.
-/

@[expose] public section
namespace Module.Basis
variable {R M N ι κ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Attach finitely many boundary rows to a residual coefficient map
(Olver--Townsend 2013, §2). -/
noncomputable def borderedCoefficientMap (b : Basis ι R M) (c : Basis κ R N)
    {q : ℕ} (B : M →ₗ[R] (Fin q → R)) (L : M →ₗ[R] N) :
    (ι →₀ R) →ₗ[R] ((Fin q → R) × (κ →₀ R)) :=
  (B.comp b.repr.symm.toLinearMap).prod (b.coefficientMap c L)

/-- Bordering computes precisely the boundary data and residual of the
reconstructed finite expansion. -/
theorem borderedCoefficientMap_apply (b : Basis ι R M) (c : Basis κ R N)
    {q : ℕ} (B : M →ₗ[R] (Fin q → R)) (L : M →ₗ[R] N) (v : ι →₀ R) :
    b.borderedCoefficientMap c B L v =
      (B (b.repr.symm v), c.repr (L (b.repr.symm v))) := rfl

/-- A bordered coefficient equation is equivalent to the original boundary
and residual equations; it makes no invertibility assumption. -/
theorem borderedCoefficientMap_eq_iff (b : Basis ι R M) (c : Basis κ R N)
    {q : ℕ} (B : M →ₗ[R] (Fin q → R)) (L : M →ₗ[R] N)
    (v : ι →₀ R) (β : Fin q → R) (f : N) :
    b.borderedCoefficientMap c B L v = (β, c.repr f) ↔
      B (b.repr.symm v) = β ∧ L (b.repr.symm v) = f := by
  rw [borderedCoefficientMap_apply, Prod.mk.injEq, c.repr.injective.eq_iff]

end Module.Basis
