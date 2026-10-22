/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Orthogonality
public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Laplacian

/-! # Polynomial radial lifting into real angular sectors
This common construction underlies disk and annular Zernike families.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public section
namespace MvPolynomial

/-- Multiply a polynomial in squared radius by a real solid harmonic. -/
noncomputable def diskRadialLift (s : Bool) (p : Polynomial ℝ) (m : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  p.eval₂ C (X 0^2+X 1^2) * if s then (diskHarmonics m).2 else (diskHarmonics m).1

/-- Polar evaluation, including the center, separates radius and angle. -/
theorem eval_diskRadialLift_polar (s : Bool) (p : Polynomial ℝ) (m : ℕ) (r θ : ℝ) :
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (diskRadialLift s p m) =
      p.eval (r^2)*r^m*zernikeAngular s m θ := by
  have he : eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ)
      (p.eval₂ C (X 0^2+X 1^2)) = p.eval (r^2) := by
    rw [eval_polynomial_eval₂_C]
    congr 1
    simp only [map_add, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
    rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  cases s <;> simp only [diskRadialLift, Bool.false_eq_true, ↓reduceIte, map_mul, he,
    (eval_diskHarmonics_polar m r θ).1, (eval_diskHarmonics_polar m r θ).2,
    zernikeAngular] <;> ring

/-- Radial degree contributes twice to Cartesian degree. -/
theorem totalDegree_diskRadialLift_le (s : Bool) (p : Polynomial ℝ) (m : ℕ) :
    (diskRadialLift s p m).totalDegree ≤ 2*p.natDegree+m := by
  have hr : (p.eval₂ C (X 0^2+X 1^2 : MvPolynomial (Fin 2) ℝ)).totalDegree ≤
      2*p.natDegree := by
    apply (totalDegree_polynomial_eval₂_C_le _ _).trans
    have hd : (X 0^2+X 1^2 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 :=
      (totalDegree_add _ _).trans (by simp)
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left p.natDegree hd
  cases s <;> simp only [diskRadialLift, Bool.false_eq_true, ↓reduceIte]
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add hr (totalDegree_diskHarmonics_le m).1)
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add hr (totalDegree_diskHarmonics_le m).2)

/-- The Cartesian Laplacian remains in the same angular sector. -/
theorem diskLaplacian_diskRadialLift (s : Bool) (p : Polynomial ℝ) (m : ℕ) :
    diskLaplacian (diskRadialLift s p m) =
      diskRadialLift s
        (4*(Polynomial.X*p.derivative.derivative+((m : Polynomial ℝ)+1)*p.derivative)) m := by
  cases s <;> simp only [diskRadialLift, Bool.false_eq_true, ↓reduceIte]
  · rw [diskLaplacian_radial_mul p _ m (laplacian_diskHarmonics m).1 (euler_diskHarmonics m).1]
    simp [Polynomial.eval₂_add, Polynomial.eval₂_mul]
  · rw [diskLaplacian_radial_mul p _ m (laplacian_diskHarmonics m).2 (euler_diskHarmonics m).2]
    simp [Polynomial.eval₂_add, Polynomial.eval₂_mul]

end MvPolynomial
