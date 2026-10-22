/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Clenshaw
public import LeanFun.Mathlib.Algebra.Polynomial.MultiplicationOperator
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-! # Clenshaw evaluation at a single operator
A polynomial recurrence maps through `aeval` to any algebra, including the
noncommutative algebra of endomorphisms. Only polynomials in the single chosen
operator occur. Reference: Clenshaw (1955); Olver--Townsend (2013), Sections 2--3.
-/

public section
namespace Polynomial.Chebyshev
variable {R : Type*} [CommRing R]

/-- Polynomial-valued Clenshaw reconstructs the full Chebyshev expansion. -/
theorem clenshaw_polynomial_T (c : ℕ → R) (n : ℕ) :
    clenshaw (fun _ ↦ 2 * (X : R[X])) (fun _ ↦ -1) (fun k ↦ Polynomial.C (c k)) 1 X n =
      ∑ k ∈ Finset.range n, Polynomial.C (c k) * T R k := by
  have hp (k : ℕ) : T R (k + 2 : ℕ) =
      (2 * X) * T R (k + 1 : ℕ) + (-1) * T R k := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, T_add_two, neg_one_mul,
      sub_eq_add_neg]
  simpa only [Nat.cast_zero, Nat.cast_one, T_zero, T_one] using
    clenshaw_eq_sum (fun _ ↦ 2 * (X : R[X])) (fun _ ↦ -1)
      (fun k ↦ Polynomial.C (c k)) (fun k ↦ T R k) hp n

/-- The same backward recurrence evaluates a Chebyshev expansion at one element
of an arbitrary algebra. This includes linear operators without assuming that
the whole endomorphism algebra is commutative. -/
theorem clenshaw_aeval_T {A : Type*} [Ring A] [Algebra R A] (J : A)
    (c : ℕ → R) (n : ℕ) :
    clenshaw (fun _ ↦ 2 * J) (fun _ ↦ -1) (fun k ↦ algebraMap R A (c k)) 1 J n =
      aeval J (∑ k ∈ Finset.range n, Polynomial.C (c k) * T R k) := by
  have h := clenshaw_map (aeval J).toRingHom (fun _ ↦ 2 * (X : R[X])) (fun _ ↦ -1)
    (fun k ↦ Polynomial.C (c k)) 1 X n
  rw [clenshaw_polynomial_T] at h
  simpa only [Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_mul, map_ofNat, map_neg, map_one, aeval_X, Polynomial.aeval_C] using h

/-- Operator Clenshaw computes multiplication by the Chebyshev expansion exactly
on the polynomial module (Olver--Townsend, Sections 2--3). -/
theorem clenshaw_mulLeft_T (c : ℕ → R) (n : ℕ) :
    clenshaw (fun _ ↦ 2 * LinearMap.mulLeft R (X : R[X])) (fun _ ↦ -1)
      (fun k ↦ algebraMap R (Module.End R R[X]) (c k)) 1
      (LinearMap.mulLeft R (X : R[X])) n =
      LinearMap.mulLeft R (∑ k ∈ Finset.range n, Polynomial.C (c k) * T R k) := by
  rw [clenshaw_aeval_T, aeval_mulLeft_X]

/-- In any polynomial basis, operator Clenshaw produces the multiplication
coefficient map on finitely supported vectors, with no finite-section claim. -/
theorem clenshaw_coefficientMap_T {ι : Type*} (b : Module.Basis ι R R[X])
    (c : ℕ → R) (n : ℕ) :
    clenshaw (fun _ ↦ 2 * b.coefficientMap b (LinearMap.mulLeft R (X : R[X])))
      (fun _ ↦ -1) (fun k ↦ algebraMap R (Module.End R (ι →₀ R)) (c k)) 1
      (b.coefficientMap b (LinearMap.mulLeft R (X : R[X]))) n =
      b.coefficientMap b
        (LinearMap.mulLeft R (∑ k ∈ Finset.range n, Polynomial.C (c k) * T R k)) := by
  rw [clenshaw_aeval_T, ← coefficientMap_mulLeft_eq_aeval]

end Polynomial.Chebyshev
