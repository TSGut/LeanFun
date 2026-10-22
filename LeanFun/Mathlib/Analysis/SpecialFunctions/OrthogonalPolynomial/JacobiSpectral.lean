/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Matrix.HessenbergEigenvector
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.JacobiMatrix
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.GaussEigenvector

/-! # Symmetric Jacobi matrices and Golub--Welsch
Squared norms explicitly transport arbitrary polynomial normalization to
orthonormal coordinates. Reference: DLMF §3.5(vi).
-/

@[expose] public section
open MeasureTheory Matrix
namespace Polynomial.Sequence

/-- Local existence data for a normalized Jacobi section. -/
structure NormalizedJacobiMatrixInput (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) where
  mixed : ∀ i j : Fin n, Integrable (fun t => (X * P j).eval t * (P i).eval t) μ
  square : ∀ i : Fin n, IntegrableSquare μ (P i)
  positive : ∀ i : Fin n, 0 < P.squaredNorm μ i (square i)

/-- Finite moments and positive polynomial pairing supply every finite section. -/
abbrev NormalizedJacobiMatrixInput.ofMoments (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (hμ : HasFiniteMoments μ := by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hpos : HasPositiveDefiniteIntegral μ := by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    NormalizedJacobiMatrixInput P μ n :=
  ⟨fun _ _ => hμ.integrable_mul _ _, fun _ => ⟨hμ.integrable_mul _ _⟩,
    fun i => squaredNorm_pos hpos P i⟩

/-- Multiplication by X compressed in classically normalized polynomial coordinates. -/
noncomputable def normalizedJacobiMatrix (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : NormalizedJacobiMatrixInput P μ n := by exact Polynomial.Sequence.NormalizedJacobiMatrixInput.ofMoments _ _ _) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ integralInner μ (IntegrablePair.of μ (X * P j) (P i) (d.mixed i j)) /
    (Real.sqrt (P.squaredNorm μ i (d.square i)) * Real.sqrt (P.squaredNorm μ j (d.square j)))

/-- All normalization denominators are strictly positive. -/
theorem NormalizedJacobiMatrixInput.denominator_pos {P : Sequence ℝ} {μ : Measure ℝ} {n : ℕ}
    (d : NormalizedJacobiMatrixInput P μ n) (i j : Fin n) :
    0 < Real.sqrt (P.squaredNorm μ i (d.square i)) * Real.sqrt (P.squaredNorm μ j (d.square j)) :=
  mul_pos (Real.sqrt_pos.mpr (d.positive i)) (Real.sqrt_pos.mpr (d.positive j))

/-- Multiplication by the classical normalizing factor recovers the mixed pairing. -/
theorem normalizedJacobiMatrix_mul_norm (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : NormalizedJacobiMatrixInput P μ n) (i j : Fin n) :
    P.normalizedJacobiMatrix μ n d i j *
      (Real.sqrt (P.squaredNorm μ i (d.square i)) * Real.sqrt (P.squaredNorm μ j (d.square j))) =
    integralInner μ (IntegrablePair.of μ (X * P j) (P i) (d.mixed i j)) :=
  div_mul_cancel₀ _ (d.denominator_pos i j).ne'

/-- The normalized multiplication section is symmetric on its classical domain. -/
theorem normalizedJacobiMatrix_isSymm (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : NormalizedJacobiMatrixInput P μ n := by exact Polynomial.Sequence.NormalizedJacobiMatrixInput.ofMoments _ _ _) :
    (P.normalizedJacobiMatrix μ n d).IsSymm := by
  ext i j
  simp only [normalizedJacobiMatrix, transpose_apply]
  rw [integralInner_X_mul, integralInner_comm]
  ring

variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
include hμ hP

/-- Orthogonality makes the symmetric section tridiagonal. -/
theorem IsOrthogonal.normalizedJacobiMatrix_eq_zero {n : ℕ}
    (d : NormalizedJacobiMatrixInput P μ n) (i j : Fin n)
    (hij : (j : ℕ) + 1 < i ∨ (i : ℕ) + 1 < j) :
    P.normalizedJacobiMatrix μ n d  i j = 0 := by
  simp only [normalizedJacobiMatrix, hP.integralInner_X_mul_eq_zero hμ hij, zero_div]

include hpos

/-- Diagonal norm scaling converts the original recurrence matrix to the
symmetric Jacobi matrix. -/
theorem IsOrthogonal.normalizedJacobiMatrix_entry (n : ℕ) (i j : Fin n) :
    P.normalizedJacobiMatrix μ n (d := NormalizedJacobiMatrixInput.ofMoments _ _ _) i j =
      Real.sqrt (P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) * P.jacobiMatrix n i j /
        Real.sqrt (P.squaredNorm μ j (Polynomial.Sequence.IntegrableSquare.of _ _)) := by
  rw [jacobiMatrix, hP.basis_repr_eq_integralInner_div hμ hpos]
  change integralInner μ (IntegrablePair.of μ (X * P j) (P i)) / _ =
    Real.sqrt (P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) * (integralInner μ (IntegrablePair.of μ (X * P j) (P i)) /
      P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) / _
  have hi := Real.sqrt_pos.mpr (squaredNorm_pos hpos P i)
  have hj := Real.sqrt_pos.mpr (squaredNorm_pos hpos P j)
  have hs := Real.sq_sqrt (squaredNorm_pos hpos P i).le
  field_simp [hi.ne', hj.ne', (squaredNorm_pos hpos P i).ne']
  rw [hs]

/-- The characteristic polynomial is unchanged by normalization. -/
theorem IsOrthogonal.charpoly_normalizedJacobiMatrix (n : ℕ) :
    (P.normalizedJacobiMatrix μ n).charpoly = P n * C (P n).leadingCoeff⁻¹ := by
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i ↦ Real.sqrt (P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)))
  let E : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i ↦ (Real.sqrt (P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹)
  have hED : E * D = 1 := by
    ext i j
    dsimp only [E, D]
    rw [diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst j
      simp [Real.sqrt_ne_zero'.mpr (squaredNorm_pos hpos P i)]
    · simp [hij]
  have he : P.normalizedJacobiMatrix μ n = D * P.jacobiMatrix n * E := by
    ext i j
    rw [hP.normalizedJacobiMatrix_entry hμ hpos]
    simp [D, E, mul_diagonal, diagonal_mul, div_eq_mul_inv]
  rw [he, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hED, Matrix.one_mul,
    P.charpoly_jacobiMatrix]

/-- Gaussian nodes are precisely the eigenvalues (matrix spectrum) of the
symmetric finite Jacobi matrix. -/
theorem IsOrthogonal.mem_spectrum_normalizedJacobiMatrix_iff (n : ℕ) (x : ℝ) :
    x ∈ spectrum ℝ (P.normalizedJacobiMatrix μ n) ↔ (P n).IsRoot x := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hP.charpoly_normalizedJacobiMatrix hμ hpos]
  simp [IsRoot, eval_mul, leadingCoeff_ne_zero.mpr (P.ne_zero n)]

/-- The Gaussian evaluation vector is an eigenvector in normalized coordinates. -/
theorem IsOrthogonal.normalizedJacobiMatrix_mulVec_gaussEigenvector {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) :
    P.normalizedJacobiMatrix μ n *ᵥ P.gaussEigenvector μ n x (hP.gaussEigenvectorInput hμ hpos hx) =
      x • P.gaussEigenvector μ n x (hP.gaussEigenvectorInput hμ hpos hx) := by
  have hx0 : (P n).eval x = 0 :=
    (mem_roots (P.ne_zero n)).mp (Multiset.mem_toFinset.mp hx)
  have hs := P.normalizedJacobiMatrix_isSymm μ n
  ext i
  change (∑ j : Fin n, P.normalizedJacobiMatrix μ n (d := NormalizedJacobiMatrixInput.ofMoments _ _ _) i j * P.gaussEigenvector μ n x (hP.gaussEigenvectorInput hμ hpos hx) j) = _
  have he (j : Fin n) :
      P.normalizedJacobiMatrix μ n (d := NormalizedJacobiMatrixInput.ofMoments _ _ _) i j * P.gaussEigenvector μ n x (hP.gaussEigenvectorInput hμ hpos hx) j =
      (Real.sqrt (P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _))) / Real.sqrt (P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) *
        (P.jacobiMatrix n j i * (P j).eval x) := by
    rw [← hs.apply i j, hP.normalizedJacobiMatrix_entry hμ hpos]
    dsimp only [gaussEigenvector, IsOrthogonal.gaussEigenvectorInput]
    have hi := (Real.sqrt_pos.mpr (squaredNorm_pos hpos P i)).ne'
    have hj := (Real.sqrt_pos.mpr (squaredNorm_pos hpos P j)).ne'
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum, P.sum_jacobiMatrix_mul_eval hx0]
  simp only [Pi.smul_apply, smul_eq_mul, gaussEigenvector]
  ring

/-- Golub--Welsch: a unit eigenvector at each node recovers its quadrature weight
from the first component. No eigensolver or floating-point claim is made. -/
theorem IsOrthogonal.golubWelsch {n : ℕ} {x : ℝ}
    (hx : x ∈ (P (n + 1)).roots.toFinset) :
    ∃ v : Fin (n + 1) → ℝ,
      (∑ i, v i ^ 2 = 1) ∧ P.normalizedJacobiMatrix μ (n + 1) *ᵥ v = x • v ∧
      P.gaussWeight μ (n + 1) x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) = μ.real Set.univ * v 0 ^ 2 :=
  ⟨P.gaussEigenvector μ (n + 1) x (hP.gaussEigenvectorInput hμ hpos hx), hP.sum_sq_gaussEigenvector hμ hpos hx,
    hP.normalizedJacobiMatrix_mulVec_gaussEigenvector hμ hpos hx,
    hP.gaussWeight_eq_mass_mul_first_sq hμ hpos hx⟩

/-- Adjacent entries are nonzero, independently of signs of leading coefficients. -/
theorem IsOrthogonal.normalizedJacobiMatrix_superdiag_ne_zero {n : ℕ} (i : Fin n) :
    P.normalizedJacobiMatrix μ (n + 1) (d := NormalizedJacobiMatrixInput.ofMoments _ _ _) i.castSucc i.succ ≠ 0 := by
  have ha : P.jacobiMatrix (n + 1) i.castSucc i.succ = P.recurrenceC μ i (Sequence.RecurrenceCInput.of _ _ _) := by
    rw [jacobiMatrix, hP.basis_repr_eq_integralInner_div hμ hpos]
    change integralInner μ (IntegrablePair.of μ (X * P ((i : ℕ) + 1)) (P i)) / _ = _
    rw [hP.integralInner_X_mul_pred hμ]
    rfl
  rw [hP.normalizedJacobiMatrix_entry hμ hpos, ha]
  exact div_ne_zero (mul_ne_zero
    (Real.sqrt_pos.mpr (squaredNorm_pos hpos P i)).ne'
    (recurrenceC_ne_zero hpos P i))
    (Real.sqrt_pos.mpr (squaredNorm_pos hpos P ((i : ℕ) + 1))).ne'

/-- Every unit eigenvector at a Gaussian node gives the same Golub--Welsch
weight; the result is independent of the eigenvector's sign. -/
theorem IsOrthogonal.gaussWeight_eq_of_unit_eigenvector {n : ℕ} {x : ℝ}
    (hx : x ∈ (P (n + 1)).roots.toFinset) (v : Fin (n + 1) → ℝ)
    (hv : P.normalizedJacobiMatrix μ (n + 1) *ᵥ v = x • v)
    (hvN : ∑ i, v i ^ 2 = 1) :
    P.gaussWeight μ (n + 1) x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) = μ.real Set.univ * v 0 ^ 2 := by
  have hw := hP.gaussWeight_eq_mass_mul_first_sq hμ hpos hx
  have hu0 : P.gaussEigenvector μ (n + 1) x (hP.gaussEigenvectorInput hμ hpos hx) 0 ≠ 0 := by
    intro hz
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] at hw
    exact (hP.gaussWeight_pos hμ hpos hx).ne' hw
  have hs := Matrix.hessenberg_eigenvector_first_sq_eq
    (fun i j hij ↦ hP.normalizedJacobiMatrix_eq_zero hμ (NormalizedJacobiMatrixInput.ofMoments P μ _) i j (Or.inr hij))
    (hP.normalizedJacobiMatrix_superdiag_ne_zero hμ hpos)
    (hP.normalizedJacobiMatrix_mulVec_gaussEigenvector hμ hpos hx) hv hu0
    (hP.sum_sq_gaussEigenvector hμ hpos hx) hvN
  rw [hw, hs]

end Polynomial.Sequence
