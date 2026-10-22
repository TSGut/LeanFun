/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Change of coefficient algebra for Jacobi polynomials
The finite formula is natural in commutative rational algebras (DLMF 18.5.7).
-/
public section
namespace Polynomial
variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

/-- Jacobi polynomials commute with rational algebra maps (DLMF 18.5.7). -/
theorem map_jacobi (f : R →ₐ[ℚ] S) (α β : R) (n : ℕ) :
    (jacobi α β n).map f.toRingHom = jacobi (f α) (f β) n := by
  have hp (k : ℕ) (x : R) : f ((ascPochhammer R k).eval x) =
      (ascPochhammer S k).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  simp only [jacobi, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, hp, map_add, map_natCast, map_one, AlgHom.commutes]

end Polynomial
