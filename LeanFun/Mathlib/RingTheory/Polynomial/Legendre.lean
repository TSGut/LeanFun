/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Legendre polynomials

The standard family is defined by Rodrigues' formula, independently of Jacobi.
Mathlib's shifted family has orientation `1 - 2X`, rather than `2X - 1`.
References: DLMF 18.5.5 and Table 18.3.1.
-/

@[expose] public section

namespace Polynomial

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Legendre polynomials in the normalisation `Pₙ(1) = 1`, defined by
Rodrigues' formula (DLMF 18.5.5, Table 18.5.1 and Table 18.3.1). -/
noncomputable def legendre (n : ℕ) : R[X] :=
  C (algebraMap ℚ R (((2 : ℚ) ^ n * n.factorial)⁻¹)) *
    derivative^[n] ((X ^ 2 - 1) ^ n)

/-- Legendre polynomials commute with coefficient maps (DLMF 18.5.5). -/
theorem map_legendre {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (n : ℕ) :
    (legendre R n).map f.toRingHom = legendre S n := by
  simp only [legendre, Polynomial.map_mul, Polynomial.map_C,
    ← iterate_derivative_map, Polynomial.map_pow, Polynomial.map_sub, map_X,
    Polynomial.map_one]
  congr 2
  exact f.commutes _

omit [Algebra ℚ R] in
private theorem iterate_derivative_comp_affine (p : R[X]) (a b : R) (n : ℕ) :
    derivative^[n] (p.comp (C a * X + C b)) =
      C (a ^ n) * (derivative^[n] p).comp (C a * X + C b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp]
    simp only [derivative_add, derivative_C_mul, derivative_X, mul_one, derivative_C,
      add_zero, Function.iterate_succ_apply', pow_succ, map_mul]
    ring

private theorem legendre_comp_one_sub_two_mul_X_rat (n : ℕ) :
    (legendre ℚ n).comp (1 - 2 * X) = (shiftedLegendre n).map (Int.castRingHom ℚ) := by
  have hd := iterate_derivative_comp_affine ℚ ((X ^ 2 - 1) ^ n) (-2) 1 n
  have harg : (C (-2 : ℚ) * X + C 1 : ℚ[X]) = 1 - 2 * X := by simp only [map_neg, map_ofNat, map_one]; ring
  rw [harg] at hd
  have hp : ((X ^ 2 - 1 : ℚ[X]) ^ n).comp (1 - 2 * X) =
      C ((-4 : ℚ) ^ n) * (X ^ n * (1 - X) ^ n) := by
    simp only [pow_comp, sub_comp, X_comp, one_comp]
    rw [← mul_pow, C_pow, ← mul_pow]
    congr 1
    simp only [map_neg, map_ofNat]
    ring
  rw [hp, iterate_derivative_C_mul] at hd
  have hs := congrArg (fun p : ℤ[X] ↦ p.map (Int.castRingHom ℚ))
    (factorial_mul_shiftedLegendre_eq n)
  simp only [Polynomial.map_mul, Polynomial.map_natCast, ← iterate_derivative_map,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, map_X] at hs
  rw [← hs] at hd
  simp only [legendre, mul_comp, C_comp, Algebra.algebraMap_self, RingHom.id_apply]
  have hc : (C (((2 : ℚ) ^ n * n.factorial)⁻¹) : ℚ[X]) =
      C (((-4 : ℚ) ^ n * n.factorial)⁻¹) * C ((-2 : ℚ) ^ n) := by
    rw [← C_mul]
    congr 1
    have he : (-4 : ℚ) ^ n = (-2 : ℚ) ^ n * 2 ^ n := by rw [← mul_pow]; congr 1; norm_num
    rw [he]
    field_simp
  rw [hc, mul_assoc, ← hd]
  rw [← C_eq_natCast n.factorial]
  simp only [← mul_assoc, ← C_mul]
  have hh : (((-4 : ℚ) ^ n * n.factorial)⁻¹ * (-4) ^ n * n.factorial) = 1 := by
    field_simp
  rw [hh, C_1, one_mul]

/-- The rational-coefficient construction specialises to every rational algebra
(DLMF 18.5.5). -/
theorem map_legendre_rat (n : ℕ) :
    (legendre ℚ n).map (algebraMap ℚ R) = legendre R n :=
  map_legendre ℚ (Algebra.ofId ℚ R) n

/-- Mathlib's shifted Legendre polynomial uses the orientation `1 - 2X`
(DLMF Table 18.3.1, with the shifted variable reversed). -/
theorem legendre_comp_one_sub_two_mul_X (n : ℕ) :
    (legendre R n).comp (1 - 2 * X) = (shiftedLegendre n).map (Int.castRingHom R) := by
  have h := congrArg (Polynomial.map (algebraMap ℚ R)) (legendre_comp_one_sub_two_mul_X_rat n)
  rw [Polynomial.map_comp, map_legendre_rat] at h
  have hm : (algebraMap ℚ R).comp (Int.castRingHom ℚ) = Int.castRingHom R := by
    ext z
    simp
  simpa only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_ofNat, map_X, map_map, hm] using h

/-- Recover standard Legendre polynomials by undoing Mathlib's shift
(DLMF Table 18.3.1). -/
theorem legendre_eq_shiftedLegendre_comp (n : ℕ) :
    legendre R n = ((shiftedLegendre n).map (Int.castRingHom R)).comp
      (C (algebraMap ℚ R (1 / 2)) * (1 - X)) := by
  have h := congrArg (fun p : R[X] ↦ p.comp (C (algebraMap ℚ R (1 / 2)) * (1 - X)))
    (legendre_comp_one_sub_two_mul_X R n)
  have hh : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    have hh := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  have ha : (1 - 2 * X : R[X]).comp (C (algebraMap ℚ R (1 / 2)) * (1 - X)) = X := by
    simp only [sub_comp, one_comp, mul_comp, ofNat_comp, X_comp]
    have hh' := congrArg (C : R →+* R[X]) hh
    simp only [map_mul, map_ofNat, map_one] at hh'
    linear_combination -(1 - X) * hh'
  simpa only [comp_assoc, ha, comp_X] using h

/-- Legendre parity as a polynomial identity (DLMF Table 18.6.1). -/
theorem legendre_comp_neg_X (n : ℕ) :
    (legendre R n).comp (-X) = C ((-1 : R) ^ n) * legendre R n := by
  have hd := iterate_derivative_comp_affine R ((X ^ 2 - 1) ^ n) (-1) 0 n
  simp only [map_neg, map_one, map_zero, neg_one_mul, add_zero] at hd
  have hp : ((X ^ 2 - 1 : R[X]) ^ n).comp (-X) = (X ^ 2 - 1) ^ n := by
    simp only [pow_comp, sub_comp, X_comp, one_comp, neg_sq]
  rw [hp] at hd
  have hs : C ((-1 : R) ^ n) * C ((-1 : R) ^ n) = (1 : R[X]) := by
    rw [← C_mul, ← mul_pow]
    simp
  have he := congrArg (fun p : R[X] ↦ C ((-1 : R) ^ n) * p) hd
  rw [← mul_assoc, hs, one_mul] at he
  simp only [legendre, mul_comp, C_comp]
  rw [← he]
  ring

/-- With the conventional shift `2X - 1`, Mathlib's family carries a parity
factor (DLMF Table 18.6.1). -/
theorem legendre_comp_two_mul_X_sub_one (n : ℕ) :
    (legendre R n).comp (2 * X - 1) =
      C ((-1 : R) ^ n) * (shiftedLegendre n).map (Int.castRingHom R) := by
  have h := congrArg (fun p : R[X] ↦ p.comp (1 - 2 * X)) (legendre_comp_neg_X R n)
  have ha : (-X : R[X]).comp (1 - 2 * X) = 2 * X - 1 := by simp
  simpa only [comp_assoc, ha, mul_comp, C_comp, legendre_comp_one_sub_two_mul_X] using h

end Polynomial
