/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-! # Real polynomial angular harmonics
These are the real and imaginary parts of (x+iy)^m, defined without polar
coordinates or division. Reference: DLMF 18.37.1 and real Zernike angular factors.
-/

@[expose] public section
namespace MvPolynomial

/-- The cosine and sine solid harmonics, as a polynomial pair. -/
noncomputable def diskHarmonics : ℕ → MvPolynomial (Fin 2) ℝ × MvPolynomial (Fin 2) ℝ
  | 0 => (1,0)
  | m+1 => (X 0*(diskHarmonics m).1-X 1*(diskHarmonics m).2,
      X 1*(diskHarmonics m).1+X 0*(diskHarmonics m).2)

/-- Solid harmonics have degree at most their angular index. -/
theorem totalDegree_diskHarmonics_le (m : ℕ) :
    (diskHarmonics m).1.totalDegree ≤ m ∧ (diskHarmonics m).2.totalDegree ≤ m := by
  induction m with
  | zero => simp [diskHarmonics]
  | succ m ih =>
    have h00 := (totalDegree_mul (X 0) (diskHarmonics m).1).trans
      (Nat.add_le_add (le_of_eq (totalDegree_X _)) ih.1)
    have h11 := (totalDegree_mul (X 1) (diskHarmonics m).2).trans
      (Nat.add_le_add (le_of_eq (totalDegree_X _)) ih.2)
    have h10 := (totalDegree_mul (X 1) (diskHarmonics m).1).trans
      (Nat.add_le_add (le_of_eq (totalDegree_X _)) ih.1)
    have h01 := (totalDegree_mul (X 0) (diskHarmonics m).2).trans
      (Nat.add_le_add (le_of_eq (totalDegree_X _)) ih.2)
    constructor
    · exact (totalDegree_sub _ _).trans (max_le (by omega) (by omega))
    · exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))

/-- Polar evaluation recovers r^m cos(m theta) and r^m sin(m theta), including r=0. -/
theorem eval_diskHarmonics_polar (m : ℕ) (r θ : ℝ) :
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (diskHarmonics m).1 =
      r^m*Real.cos (m*θ) ∧
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (diskHarmonics m).2 =
      r^m*Real.sin (m*θ) := by
  induction m with
  | zero => simp [diskHarmonics]
  | succ m ih =>
    simp only [diskHarmonics, map_add, map_sub, map_mul, eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ih.1, ih.2, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Real.cos_add, Real.sin_add, pow_succ]
    constructor <;> ring

end MvPolynomial
