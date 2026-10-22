/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.FiniteHierarchy
import Mathlib.Tactic.ComputeDegree

/-! # Rectangular QR for two-step semiclassical raising

Reference: Papadopoulos–Gutleb–Slevinsky–Olver, §3.1.
The first N columns of multiplication by t-x need N+1 rows. Their QR factor
is the connection for raising the third parameter by two.
-/

@[expose] public section
open MeasureTheory Module
namespace Polynomial
variable {t α β : ℝ} (ht : 1 < t) (hα : -1 < α) (hβ : -1 < β)

/-- The orthogonal factor's columns are `(t-X)` times the twice-raised basis. -/
noncomputable def semiclassicalJacobiQRSection (γ : ℝ) (N : ℕ) :
    Matrix (Fin (N+1)) (Fin N) ℝ := fun i j ↦
  (semiclassicalJacobiBasis ht hα hβ γ).repr
    ((C t-X) * semiclassicalJacobiSequence ht hα hβ (γ+2) j) i

/-- Multiplication by `t-X`, with one extra output mode. -/
noncomputable def semiclassicalJacobiShiftSection (γ : ℝ) (N : ℕ) :
    Matrix (Fin (N+1)) (Fin N) ℝ := fun i j ↦
  (semiclassicalJacobiBasis ht hα hβ γ).repr
    ((C t-X) * semiclassicalJacobiSequence ht hα hβ γ j) i

/-- The rectangular multiplication section is exactly Q times the two-step connection. -/
theorem semiclassicalJacobiShiftSection_eq_QR (γ : ℝ) (N : ℕ) :
    semiclassicalJacobiShiftSection ht hα hβ γ N =
      semiclassicalJacobiQRSection ht hα hβ γ N *
        semiclassicalJacobiRaisingSection ht hα hβ γ 2 N := by
  ext i j
  simpa only [semiclassicalJacobiShiftSection, semiclassicalJacobiQRSection,
    semiclassicalJacobiRaisingSection, semiclassicalJacobiConnection,
    Matrix.mul_apply, Basis.toMatrix_apply, semiclassicalJacobiBasis_apply,
    Nat.cast_ofNat, LinearMap.mulLeft_apply] using
    semiclassicalJacobi_repr_map_sum ht hα hβ (γ+2)
      (semiclassicalJacobiBasis ht hα hβ γ) (LinearMap.mulLeft ℝ (C t-X))
      (semiclassicalJacobiSequence ht hα hβ γ j) N (by simp) i

/-- Multiplication by `t-X` is an isometry from the twice-raised polynomial inner product. -/
theorem semiclassicalJacobi_integralInner_shift_two (γ : ℝ) (p q : ℝ[X]) :
    integralInner (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ)
      (IntegrablePair.of _ ((C t-X)*p) ((C t-X)*q)) =
    integralInner (semiclassicalJacobiMeasure ⟨t, ht⟩ α β (γ+2))
      (IntegrablePair.of _ p q) := by
  have hi := (hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ+2) ht hα hβ).integrable_mul p q
  have he := (integral_semiclassicalJacobi_shift_integrable ht α β γ 0 0 2
    ⟨_, by simpa only [Nat.cast_zero, add_zero, Nat.cast_ofNat] using hi⟩).2
  simp only [Nat.cast_zero, add_zero, Nat.cast_ofNat, semiclassicalJacobiShiftDensity,
    pow_zero, one_mul] at he
  simp only [integralInner]
  erw [he]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [eval_mul, eval_pow]
  ring

/-- The rectangular Q has orthonormal columns. -/
theorem semiclassicalJacobiQRSection_orthogonal (γ : ℝ) (N : ℕ) :
    (semiclassicalJacobiQRSection ht hα hβ γ N).transpose *
      semiclassicalJacobiQRSection ht hα hβ γ N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, semiclassicalJacobiQRSection]
  rw [← semiclassicalJacobi_integralInner_eq_sum ht hα hβ γ _ _ (N+1)
    (by have hd := natDegree_mul_le (p := C t-X) (q := semiclassicalJacobiSequence ht hα hβ (γ+2) i)
        have htdeg : (C t-X).natDegree ≤ 1 := by compute_degree
        simp only [Sequence.natDegree_eq] at hd
        omega), semiclassicalJacobi_integralInner_shift_two ht hα hβ]
  rw [← semiclassicalJacobiBasis_repr ht hα hβ, ← semiclassicalJacobiBasis_apply ht hα hβ (γ+2) i,
    Basis.repr_self]
  simp [Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff]

/-- The twice-raised Jacobi section is the compression by the rectangular Q.
All entries are exact; the old Jacobi section has one extra row and column. -/
theorem semiclassicalJacobiQRSection_update (γ : ℝ) (N : ℕ) :
    (semiclassicalJacobiQRSection ht hα hβ γ N).transpose *
      (Matrix.of (fun i j : Fin (N+1) ↦ semiclassicalJacobiMatrix ht hα hβ γ i j)) *
      semiclassicalJacobiQRSection ht hα hβ γ N =
    Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ (γ+2) i j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    semiclassicalJacobiQRSection, semiclassicalJacobiMatrix, Basis.toMatrix_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi : ((C t-X)*semiclassicalJacobiSequence ht hα hβ (γ+2) i).natDegree < N+1 := by
    have hd := natDegree_mul_le (p := C t-X) (q := semiclassicalJacobiSequence ht hα hβ (γ+2) i)
    have htdeg : (C t-X).natDegree ≤ 1 := by compute_degree
    simp only [Sequence.natDegree_eq] at hd
    omega
  have hj : ((C t-X)*semiclassicalJacobiSequence ht hα hβ (γ+2) j).natDegree < N+1 := by
    have hd := natDegree_mul_le (p := C t-X) (q := semiclassicalJacobiSequence ht hα hβ (γ+2) j)
    have htdeg : (C t-X).natDegree ≤ 1 := by compute_degree
    simp only [Sequence.natDegree_eq] at hd
    omega
  rw [← semiclassicalJacobi_integralInner_mul_eq_sum ht hα hβ γ _ _ X (N+1) hi hj]
  have he : X * ((C t-X)*semiclassicalJacobiSequence ht hα hβ (γ+2) j) =
      (C t-X)*(X*semiclassicalJacobiSequence ht hα hβ (γ+2) j) := by ring
  have htransfer := semiclassicalJacobi_integralInner_shift_two ht hα hβ γ
    (semiclassicalJacobiSequence ht hα hβ (γ+2) i)
    (X*semiclassicalJacobiSequence ht hα hβ (γ+2) j)
  rw [semiclassicalJacobiBasis_repr ht hα hβ]
  simp only [integralInner] at htransfer ⊢
  rw [he, htransfer]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _


end Polynomial
