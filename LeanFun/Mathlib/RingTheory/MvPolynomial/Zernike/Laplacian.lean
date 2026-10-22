/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Basic
public import LeanFun.Mathlib.RingTheory.MvPolynomial.Zernike.Derivatives
public import LeanFun.Mathlib.Algebra.MvPolynomial.PolynomialDerivative
import Mathlib.Tactic.LinearCombination

/-! # Polynomial radial form of the disk Laplacian
For a homogeneous harmonic h of degree m, the Cartesian Laplacian sends
p(r²)h to 4(r² p''(r²)+(m+1)p'(r²))h. This proves angular-sector preservation
as an identity of polynomials, including at the origin.
Reference: the radial differential operators in Papadopoulos–Gutleb–Slevinsky–Olver,
Building hierarchies of semiclassical Jacobi polynomials for spectral methods in annuli.
-/

@[expose] public section
namespace MvPolynomial

/-- The Cartesian polynomial Laplacian in two dimensions. -/
noncomputable def diskLaplacian (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  pderiv 0 (pderiv 0 p)+pderiv 1 (pderiv 1 p)

/-- First Cartesian derivative of a radial polynomial. -/
theorem pderiv_zero_radial (p : Polynomial ℝ) :
    pderiv 0 (p.eval₂ C (X 0^2+X 1^2 : MvPolynomial (Fin 2) ℝ)) =
      p.derivative.eval₂ C (X 0^2+X 1^2) * (2*X 0) := by
  rw [pderiv_polynomial_eval₂_C]
  congr 1
  norm_num [pderiv_pow, pderiv_X, Pi.single_apply]

/-- Second-coordinate derivative of a radial polynomial. -/
theorem pderiv_one_radial (p : Polynomial ℝ) :
    pderiv 1 (p.eval₂ C (X 0^2+X 1^2 : MvPolynomial (Fin 2) ℝ)) =
      p.derivative.eval₂ C (X 0^2+X 1^2) * (2*X 1) := by
  rw [pderiv_polynomial_eval₂_C]
  congr 1
  norm_num [pderiv_pow, pderiv_X, Pi.single_apply]

/-- The radial Laplacian identity for any homogeneous harmonic polynomial. -/
theorem diskLaplacian_radial_mul (p : Polynomial ℝ) (h : MvPolynomial (Fin 2) ℝ) (m : ℕ)
    (hh : diskLaplacian h=0)
    (he : X 0*pderiv 0 h+X 1*pderiv 1 h = (m : MvPolynomial (Fin 2) ℝ)*h) :
    diskLaplacian (p.eval₂ C (X 0^2+X 1^2)*h) =
      4*((X 0^2+X 1^2)*p.derivative.derivative.eval₂ C (X 0^2+X 1^2)+
        ((m : MvPolynomial (Fin 2) ℝ)+1)*p.derivative.eval₂ C (X 0^2+X 1^2))*h := by
  have htwo (i : Fin 2) : pderiv i (2 : MvPolynomial (Fin 2) ℝ)=0 := by
    rw [show (2 : MvPolynomial (Fin 2) ℝ)=1+1 by ring, map_add, pderiv_one, add_zero]
  unfold diskLaplacian at hh ⊢
  simp only [pderiv_mul, map_add, pderiv_zero_radial, pderiv_one_radial]
  norm_num [pderiv_X, Pi.single_apply, htwo]
  linear_combination 4*p.derivative.eval₂ C (X 0^2+X 1^2)*he +
    p.eval₂ C (X 0^2+X 1^2)*hh

/-- The cosine Zernike Laplacian is a radial Jacobi differential expression in the same mode. -/
theorem diskLaplacian_zernikeCos (a b : ℝ) (k m : ℕ) :
    diskLaplacian (zernikeCos a b k m) =
      4*((X 0^2+X 1^2)*(Polynomial.shiftedJacobi b (a+m) k).derivative.derivative.eval₂ C
        (X 0^2+X 1^2)+((m : MvPolynomial (Fin 2) ℝ)+1)*(Polynomial.shiftedJacobi b (a+m) k).derivative.eval₂ C
          (X 0^2+X 1^2))*(diskHarmonics m).1 :=
  diskLaplacian_radial_mul _ _ m (laplacian_diskHarmonics m).1 (euler_diskHarmonics m).1

/-- The sine Zernike Laplacian preserves the sine angular sector. -/
theorem diskLaplacian_zernikeSin (a b : ℝ) (k m : ℕ) :
    diskLaplacian (zernikeSin a b k m) =
      4*((X 0^2+X 1^2)*(Polynomial.shiftedJacobi b (a+m) k).derivative.derivative.eval₂ C
        (X 0^2+X 1^2)+((m : MvPolynomial (Fin 2) ℝ)+1)*(Polynomial.shiftedJacobi b (a+m) k).derivative.eval₂ C
          (X 0^2+X 1^2))*(diskHarmonics m).2 :=
  diskLaplacian_radial_mul _ _ m (laplacian_diskHarmonics m).2 (euler_diskHarmonics m).2

end MvPolynomial
