/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Harmonics
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-! # Cartesian derivatives of the solid angular harmonics
These polynomial identities avoid singular polar differentiation at the origin.
Reference: real and imaginary parts of (x+iy)^m in DLMF 18.37.1.
-/

public section
namespace MvPolynomial

/-- All four first derivatives, including the initial angular frequency. -/
theorem pderiv_diskHarmonics_succ (m : ℕ) :
    pderiv 0 (diskHarmonics (m+1)).1 = (m+1)*(diskHarmonics m).1 ∧
    pderiv 1 (diskHarmonics (m+1)).1 = -(m+1)*(diskHarmonics m).2 ∧
    pderiv 0 (diskHarmonics (m+1)).2 = (m+1)*(diskHarmonics m).2 ∧
    pderiv 1 (diskHarmonics (m+1)).2 = (m+1)*(diskHarmonics m).1 := by
  induction m with
  | zero => norm_num [diskHarmonics, pderiv_mul]
  | succ m ih =>
    have he : diskHarmonics (m+1+1) =
        (X 0*(diskHarmonics (m+1)).1-X 1*(diskHarmonics (m+1)).2,
          X 1*(diskHarmonics (m+1)).1+X 0*(diskHarmonics (m+1)).2) := rfl
    rw [he]
    simp only [map_sub, map_add, pderiv_mul, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
    norm_num [pderiv_X, Pi.single_apply]
    simp only [diskHarmonics]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

/-- Both solid harmonics are harmonic polynomials, at every degree. -/
theorem laplacian_diskHarmonics (m : ℕ) :
    pderiv 0 (pderiv 0 (diskHarmonics m).1)+pderiv 1 (pderiv 1 (diskHarmonics m).1)=0 ∧
    pderiv 0 (pderiv 0 (diskHarmonics m).2)+pderiv 1 (pderiv 1 (diskHarmonics m).2)=0 := by
  cases m with
  | zero => simp [diskHarmonics]
  | succ m =>
    rw [(pderiv_diskHarmonics_succ m).1, (pderiv_diskHarmonics_succ m).2.1,
      (pderiv_diskHarmonics_succ m).2.2.1, (pderiv_diskHarmonics_succ m).2.2.2]
    cases m with
    | zero => simp [diskHarmonics]
    | succ m =>
      simp only [pderiv_mul, map_neg, map_add, Derivation.map_natCast, pderiv_one, zero_add,
        neg_zero, zero_mul, (pderiv_diskHarmonics_succ m).1,
        (pderiv_diskHarmonics_succ m).2.1, (pderiv_diskHarmonics_succ m).2.2.1,
        (pderiv_diskHarmonics_succ m).2.2.2]
      constructor <;> ring

/-- Euler's homogeneous-polynomial identity for the two real angular harmonics. -/
theorem euler_diskHarmonics (m : ℕ) :
    X 0*pderiv 0 (diskHarmonics m).1+X 1*pderiv 1 (diskHarmonics m).1 = (m : MvPolynomial (Fin 2) ℝ)*(diskHarmonics m).1 ∧
    X 0*pderiv 0 (diskHarmonics m).2+X 1*pderiv 1 (diskHarmonics m).2 = (m : MvPolynomial (Fin 2) ℝ)*(diskHarmonics m).2 := by
  cases m with
  | zero => simp [diskHarmonics]
  | succ m =>
    rw [(pderiv_diskHarmonics_succ m).1, (pderiv_diskHarmonics_succ m).2.1,
      (pderiv_diskHarmonics_succ m).2.2.1, (pderiv_diskHarmonics_succ m).2.2.2]
    simp only [diskHarmonics, Nat.cast_add, Nat.cast_one]
    constructor <;> ring

end MvPolynomial
