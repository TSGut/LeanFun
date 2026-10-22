/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Harmonics
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Shifted
public import LeanFun.Mathlib.Algebra.MvPolynomial.PolynomialComposition

/-! # Real Zernike polynomials from radial Jacobi factors
The raw real modes are r^m P_k^(b,a+m)(2r²-1) times cos(m theta) or sin(m theta).
Their positive L2 normalization is separate. Reference: DLMF 18.37.1 (complex
boundary normalization) and MultivariateOrthogonalPolynomials.jl, disk.jl (real modes).
-/

@[expose] public section
namespace MvPolynomial

/-- The radial Jacobi polynomial composed with squared radius. -/
noncomputable def zernikeRadialPolynomial (a b : ℝ) (k m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (Polynomial.shiftedJacobi b (a+m) k).eval₂ C (X 0^2+X 1^2)

/-- The raw cosine Zernike polynomial, including the angular constant mode. -/
noncomputable def zernikeCos (a b : ℝ) (k m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  zernikeRadialPolynomial a b k m * (diskHarmonics m).1

/-- The raw sine Zernike polynomial; m=0 is identically zero and is omitted from bases. -/
noncomputable def zernikeSin (a b : ℝ) (k m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  zernikeRadialPolynomial a b k m * (diskHarmonics m).2

/-- The radial factor evaluates at squared radius in polar coordinates. -/
theorem eval_zernikeRadialPolynomial_polar (a b : ℝ) (k m : ℕ) (r θ : ℝ) :
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (zernikeRadialPolynomial a b k m) =
      (Polynomial.shiftedJacobi b (a+m) k).eval (r^2) := by
  rw [zernikeRadialPolynomial, eval_polynomial_eval₂_C]
  congr 1
  simp only [map_add, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
  rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- The actual Cartesian polynomial has the conventional real Zernike polar expression. -/
theorem eval_zernikeCos_polar (a b : ℝ) (k m : ℕ) (r θ : ℝ) :
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (zernikeCos a b k m) =
      (Polynomial.jacobi b (a+m) k).eval (2*r^2-1)*r^m*Real.cos (m*θ) := by
  rw [zernikeCos, map_mul, eval_zernikeRadialPolynomial_polar,
    (eval_diskHarmonics_polar m r θ).1, Polynomial.eval_shiftedJacobi, mul_assoc]

/-- The sine mode has the analogous polar expression, including r=0. -/
theorem eval_zernikeSin_polar (a b : ℝ) (k m : ℕ) (r θ : ℝ) :
    eval (![r*Real.cos θ,r*Real.sin θ] : Fin 2 → ℝ) (zernikeSin a b k m) =
      (Polynomial.jacobi b (a+m) k).eval (2*r^2-1)*r^m*Real.sin (m*θ) := by
  rw [zernikeSin, map_mul, eval_zernikeRadialPolynomial_polar,
    (eval_diskHarmonics_polar m r θ).2, Polynomial.eval_shiftedJacobi, mul_assoc]

/-- Radial degree k contributes at most 2k in Cartesian coordinates. -/
theorem totalDegree_zernikeRadialPolynomial_le (a b : ℝ) (k m : ℕ) :
    (zernikeRadialPolynomial a b k m).totalDegree ≤ 2*k := by
  have hd : (X 0^2+X 1^2 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (by simp)
  exact (totalDegree_polynomial_eval₂_C_le _ _).trans
    ((Nat.mul_le_mul (Polynomial.natDegree_shiftedJacobi_le _ _ _) hd).trans (by omega))

/-- Both real modes belong to total degree 2k+m. -/
theorem totalDegree_zernike_le (a b : ℝ) (k m : ℕ) :
    (zernikeCos a b k m).totalDegree ≤ 2*k+m ∧
      (zernikeSin a b k m).totalDegree ≤ 2*k+m := by
  exact ⟨(totalDegree_mul _ _).trans (Nat.add_le_add
    (totalDegree_zernikeRadialPolynomial_le a b k m) (totalDegree_diskHarmonics_le m).1),
    (totalDegree_mul _ _).trans (Nat.add_le_add
      (totalDegree_zernikeRadialPolynomial_le a b k m) (totalDegree_diskHarmonics_le m).2)⟩

end MvPolynomial
