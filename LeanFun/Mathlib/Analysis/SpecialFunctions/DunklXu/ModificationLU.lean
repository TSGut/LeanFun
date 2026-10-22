/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.ModificationGram

/-!
# Exact raw-basis LU and sparse disk Cholesky factors

Any enumeration increasing first in total degree and then in inner index gives
the same correspondence. The theorem concerns exact unpivoted LU; no floating
point threshold or pivot permutation is built into the statement.
Reference: Gutleb–Olver–Slevinsky, diagonal normalization and measure conversion.
-/

public section
open MeasureTheory Set Polynomial Matrix
namespace MvPolynomial

/-- Exact unpivoted LU of the raw multiplication section has precisely the
connection-factor zeros, after any degree/inner-index ordered enumeration. -/
theorem dunklXuModifiedConnection_lu_support {β : ℝ} (hβ : -1 < β)
    (h g : ℝ[X]) (l : ℕ)
    (hh : ∀ᵐ x ∂jacobiMeasure (β+1/2) (β+1/2), 0 ≤ h.eval x)
    (hg : ∀ᵐ z ∂jacobiMeasure β β, 0 ≤ g.eval z)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) (((jacobiMeasure β β)).comap Subtype.val)))
    (hh0 : h ≠ 0) (hhpar : ∀ x, h.eval (-x) = h.eval x)
    (hgpar : ∀ z, g.eval (-z) = g.eval z) (hgdeg : g.natDegree ≤ 2*l)
    (N M : ℕ) (e : Fin M ≃ {d : Fin 2 →₀ ℕ // d.sum (fun _ t => t) ≤ N})
    (he : ∀ i j : Fin M, j < i →
      (e j).1 0+(e j).1 1 < (e i).1 0+(e i).1 1 ∨
        ((e j).1 0+(e j).1 1=(e i).1 0+(e i).1 1 ∧ (e j).1 1 < (e i).1 1))
    (L U : Matrix (Fin M) (Fin M) ℝ)
    (hL : L.transpose.IsUpperTriangular) (hd : ∀ i, L i i=1)
    (hU : U.IsUpperTriangular)
    (hLU : (dunklXuMultiplicationSection hβ (cartesianDiskModification h g l) N).submatrix e e =
      L*U) :
    ∀ i j, U i j=0 ↔ dunklXuModifiedConnection hβ h g l hh hg T N (e i) (e j)=0 := by
  classical
  let := Fintype.ofEquiv (Fin M) e
  let C := dunklXuModifiedConnection hβ h g l hh hg T N
  let W := dunklXuMultiplicationSection hβ (cartesianDiskModification h g l) N
  let D := fun i : Fin M => dunklXuNorm β ⟨(((e i).1 0+(e i).1 1), ((e i).1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩
  have hC : (C.submatrix e e).IsUpperTriangular := by
    intro i j hij
    exact dunklXuModifiedConnection_eq_zero_of_order hβ h g l hh hg T hh0 hhpar hgpar hgdeg
      N (e i) (e j) (he i j hij)
  have hdiag : ∀ i, C.submatrix e e i i ≠ 0 := fun i =>
    (dunklXuModifiedConnection_diag_pos hβ h g l hh hg T N (e i)).ne'
  have hD : ∀ i, D i ≠ 0 := fun i => (dunklXuNorm_pos hβ _ _).ne'
  have hgram : (C.submatrix e e).transpose*(C.submatrix e e) =
      diagonal D*(W.submatrix e e)*diagonal (fun i => (D i)⁻¹) := by
    have ht := congrArg (fun A => A.submatrix e e)
      (dunklXuModifiedConnection_transpose_mul hβ h g l hh hg T hgpar hgdeg N)
    rw [← submatrix_mul_equiv _ _ e e e,
      ← submatrix_mul_equiv _ _ e e e,← submatrix_mul_equiv _ _ e e e] at ht
    simp only [submatrix_diagonal_equiv,Function.comp_def] at ht
    simpa only [C,W,D,Matrix.submatrix,Matrix.transpose,Matrix.of_apply] using ht
  exact (upper_eq_of_diagonal_gram_factor (W.submatrix e e) (C.submatrix e e) L U D
    hD hC hdiag hgram hL hd hU hLU).2

end MvPolynomial
