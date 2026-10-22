/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Change of coefficient algebra for Gegenbauer polynomials
Naturality of the finite formula (DLMF 18.5.10).
-/
public section
namespace Polynomial

/-- Gegenbauer polynomials commute with rational algebra maps (DLMF 18.5.10). -/
theorem map_gegenbauer {R S : Type*} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (lam : R) (n : ℕ) :
    (gegenbauer lam n).map f.toRingHom = gegenbauer (f lam) n := by
  have hp (k : ℕ) (x : R) : f ((ascPochhammer R k).eval x) =
      (ascPochhammer S k).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  simp only [gegenbauer, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_ofNat, map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_mul, map_pow, map_neg, map_one, map_ofNat, hp, AlgHom.commutes]

end Polynomial
