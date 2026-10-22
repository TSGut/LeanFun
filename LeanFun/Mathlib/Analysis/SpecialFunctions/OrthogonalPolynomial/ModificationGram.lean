/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionGram
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ModificationOperators
public import LeanFun.Mathlib.LinearAlgebra.Matrix.CholeskyLU

/-!
# Cholesky and LU for one-dimensional polynomial measure modification

The leading section is taken after full polynomial multiplication. No unpadded
matrix functional calculus is involved. Reference: Gutleb–Olver–Slevinsky,
Lemma 2.8 and the polynomial modification theorem attributed to Gautschi.
-/

public section
open MeasureTheory Module Matrix
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) (u : ℝ[X]) (hu0 : u ≠ 0)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) {P Q : Sequence ℝ}
    (hP : P.IsOrthogonal μ)
    (hQ : Q.IsOrthogonal (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    (hPu : ∀ i, IsUnit (P i).leadingCoeff) (hQu : ∀ i, IsUnit (Q i).leadingCoeff)
    (hPn : ∀ n, integralInner μ (IntegrablePair.of μ (P n) (P n)) = 1)
    (hQn : ∀ n, integralInner (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (IntegrablePair.of (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (Q n) (Q n)) = 1)
include hμ hpos hu0 hu hP hQ hPn hQn

/-- The normalized multiplication section equals the connection transpose product. -/
theorem IsOrthogonal.modification_gram (N : ℕ) :
    Matrix.of (fun i j : Fin N => (P.basis hPu).repr (u * P j) i) =
      (Matrix.of (fun i j : Fin N => (Q.basis hQu).repr (P j) i)).transpose *
        Matrix.of (fun i j : Fin N => (Q.basis hQu).repr (P j) i) := by
  rw [← hQ.connection_gram (hμ.polynomialDensityMeasure u hu)
    (hpos.polynomialDensityMeasure hμ u hu0 hu) hQu P hQn N]
  ext i j
  dsimp only [Matrix.of_apply]
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hPu, hPn, div_one,
    integralInner_comm _ (P i), integralInner_polynomialDensityMeasure_comap u (P j) (P i) hu]

/-- Any exact unit-lower/upper LU of the normalized multiplication section has
exactly the connection support; the upper factor differs by row scaling. -/
theorem IsOrthogonal.modification_lu_support
    (hPl : ∀ n, 0 < (P n).leadingCoeff) (hQl : ∀ n, 0 < (Q n).leadingCoeff)
    (N : ℕ) (L U : Matrix (Fin N) (Fin N) ℝ)
    (hL : L.transpose.IsUpperTriangular) (hd : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular)
    (hLU : Matrix.of (fun i j : Fin N => (P.basis hPu).repr (u * P j) i) = L * U) :
    ∀ i j, U i j = 0 ↔ (Q.basis hQu).repr (P j) i = 0 := by
  have hm := hμ.polynomialDensityMeasure u hu
  have hp := hpos.polynomialDensityMeasure hμ u hu0 hu
  have hg := hP.modification_gram hμ hpos u hu0 hu hQ hPu hQu hPn hQn N
  have hr := Matrix.upper_eq_of_diagonal_gram_factor _ _ L U (fun _ => 1)
    (fun _ => one_ne_zero) (hQ.connection_upperTriangular hm hp hQu P N)
    (fun i => (hQ.connection_diag_pos hm hp hQu P hPl hQl i).ne')
    (by simpa using hg.symm) hL hd hU hLU
  exact hr.2

end Polynomial.Sequence
