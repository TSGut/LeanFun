/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Conversion
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Operators

/-! # Semiclassical Jacobi hierarchy factorizations

Exact parameter-shift factorizations in positive orthonormal coordinates.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, §§3.1–3.2 and 3.5.
-/

@[expose] public section
open MeasureTheory Module
namespace Polynomial

/-- Multiplication by the coordinate in the positive orthonormal semiclassical basis. -/
noncomputable def semiclassicalJacobiMatrix {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα hβ γ).toMatrix
    (fun j ↦ X * semiclassicalJacobiSequence ht hα hβ γ j)

/-- The orthonormal Jacobi matrix is tridiagonal. -/
theorem semiclassicalJacobiMatrix_isBanded {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) :
    (semiclassicalJacobiMatrix ht hα hβ γ).IsBanded 1 1 :=
  (semiclassicalJacobiSequence_spec ht hα hβ γ).1.mul_matrix_isBanded
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ) _

/-- Positive orthonormal coordinates make multiplication symmetric. -/
theorem semiclassicalJacobiMatrix_symmetric {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (i j : ℕ) :
    semiclassicalJacobiMatrix ht hα hβ γ i j =
      semiclassicalJacobiMatrix ht hα hβ γ j i := by
  simp only [semiclassicalJacobiMatrix, Basis.toMatrix_apply,
    semiclassicalJacobiBasis_repr, integralInner]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [eval_mul]
  ring

/-- A leading section of the connection raising the third parameter by an integer. -/
noncomputable def semiclassicalJacobiRaisingSection {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (c N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ semiclassicalJacobiConnection ht hα hβ γ hα hβ (γ+c) i j

/-- Polynomial multiplication for an integer shift is factored by its connection. -/
theorem semiclassicalJacobiRaisingSection_gram {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (c N : ℕ) :
    (Matrix.of (fun i j : Fin N ↦ (semiclassicalJacobiBasis ht hα hβ γ).repr
      ((C t-X)^c * semiclassicalJacobiSequence ht hα hβ γ j) i)) =
    (semiclassicalJacobiRaisingSection ht hα hβ γ c N).transpose *
      semiclassicalJacobiRaisingSection ht hα hβ γ c N := by
  refine Eq.trans ?_ (semiclassicalJacobiConnection_gram ht hα hβ γ hα hβ (γ+c) N)
  ext i j
  simp only [Matrix.of_apply]
  rw [semiclassicalJacobiBasis_repr]
  simp only [integralInner]
  have hi := (hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ+c) ht hα hβ).integrable_mul
    (semiclassicalJacobiSequence ht hα hβ γ i) (semiclassicalJacobiSequence ht hα hβ γ j)
  have he := (integral_semiclassicalJacobi_shift_integrable ht α β γ 0 0 c
    ⟨_, by simpa only [Nat.cast_zero, add_zero] using hi⟩).2
  simp only [Nat.cast_zero, add_zero, semiclassicalJacobiShiftDensity, pow_zero, one_mul] at he
  erw [he]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [eval_mul]
  ring

/-- A unit parameter shift is the Cholesky factorization of `t I - X`. -/
theorem semiclassicalJacobiRaisingSection_cholesky {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (N : ℕ) :
    t • (1 : Matrix (Fin N) (Fin N) ℝ) -
        (Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ γ i j)) =
      (semiclassicalJacobiRaisingSection ht hα hβ γ 1 N).transpose *
        semiclassicalJacobiRaisingSection ht hα hβ γ 1 N := by
  rw [← semiclassicalJacobiRaisingSection_gram]
  ext i j
  simp only [Matrix.of_apply, pow_one, sub_mul, C_mul', map_sub, map_smul, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply,
    semiclassicalJacobiMatrix, Basis.toMatrix_apply]
  rw [← semiclassicalJacobiBasis_apply ht hα hβ γ j, Basis.repr_self]
  simp [Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- Every raising section has positive diagonal and is upper triangular. -/
theorem semiclassicalJacobiRaisingSection_triangular {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (c N : ℕ) :
    (semiclassicalJacobiRaisingSection ht hα hβ γ c N).IsUpperTriangular ∧
      ∀ i, 0 < semiclassicalJacobiRaisingSection ht hα hβ γ c N i i :=
  ⟨semiclassicalJacobiConnection_upperTriangular ht hα hβ γ hα hβ (γ+c) N,
    fun i ↦ semiclassicalJacobiConnection_diag_pos ht hα hβ γ hα hβ (γ+c) i⟩

/-- Finite raising sections are invertible, including the empty section. -/
theorem semiclassicalJacobiRaisingSection_isUnit {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (c N : ℕ) :
    IsUnit (semiclassicalJacobiRaisingSection ht hα hβ γ c N) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact (semiclassicalJacobiRaisingSection_triangular ht hα hβ γ c N).1.det_ne_zero_iff.mpr
    (fun i ↦ (semiclassicalJacobiRaisingSection_triangular ht hα hβ γ c N).2 i |>.ne')


/-- The unit-shift connection is the unique positive upper triangular Cholesky factor. -/
theorem semiclassicalJacobiRaisingSection_cholesky_unique {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (N : ℕ)
    (R : Matrix (Fin N) (Fin N) ℝ) (hR : R.IsUpperTriangular)
    (hdiag : ∀ i, 0 < R i i)
    (hgram : R.transpose * R = t • (1 : Matrix (Fin N) (Fin N) ℝ) -
      Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ γ i j)) :
    R = semiclassicalJacobiRaisingSection ht hα hβ γ 1 N :=
  Matrix.eq_of_pos_upperTriangular_gram_eq hR
    (semiclassicalJacobiRaisingSection_triangular ht hα hβ γ 1 N).1 hdiag
    (semiclassicalJacobiRaisingSection_triangular ht hα hβ γ 1 N).2
    (hgram.trans (semiclassicalJacobiRaisingSection_cholesky ht hα hβ γ N))

end Polynomial
