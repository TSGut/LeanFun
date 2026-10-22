/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletSection

/-! # Exact finite polynomial Galerkin equations for annular Dirichlet blocks
The square section tests the residual against the finite trial space; it does
not assert that the full polynomial residual vanishes.
Reference: the conforming Galerkin formulation of the annular energy identity.
-/

@[expose] public section
open Module Matrix
namespace Polynomial

/-- Radial synthesis of the first N orthonormal (1,1,gamma) polynomials. -/
noncomputable def semiclassicalJacobiDirichletTrial {t : ℝ} (ht : 1<t) (γ : ℝ)
    (N : ℕ) (v : Fin N → ℝ) : ℝ[X] :=
  ∑ i, v i • semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
    (by norm_num : (-1 : ℝ)<1) γ i

/-- The polynomial forcing is projected onto the same test family. -/
noncomputable def semiclassicalJacobiDirichletLoad {t : ℝ} (ht : 1<t) (γ : ℝ)
    (N : ℕ) (f : ℝ[X]) : Fin N → ℝ :=
  fun i ↦ integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) f (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
      (by norm_num : (-1 : ℝ)<1) γ i))

/-- A coordinate unit vector reconstructs its trial polynomial. -/
theorem semiclassicalJacobiDirichletTrial_single {t : ℝ} (ht : 1<t) (γ : ℝ)
    (N : ℕ) (i : Fin N) :
    semiclassicalJacobiDirichletTrial ht γ N (Pi.single i 1) =
      semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
        (by norm_num : (-1 : ℝ)<1) γ i := by
  classical
  simp [semiclassicalJacobiDirichletTrial, Pi.single_apply]

/-- Each square-section row is exactly one tested differential residual. -/
theorem semiclassicalJacobiDirichletSection_mulVec {t : ℝ} (ht : 1<t) (γ : ℝ)
    (N : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    (semiclassicalJacobiDirichletSection ht γ N *ᵥ v) i =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (semiclassicalJacobiDirichletTrial ht γ N v)) (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
          (by norm_num : (-1 : ℝ)<1) γ i)) := by
  have hμ := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
    (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1)
  have hsmul (p q : ℝ[X]) (a : ℝ) := integralInner_smul_left _ p q a
    (h := hμ.integrable_mul _ _)
  simp only [semiclassicalJacobiDirichletSection, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, semiclassicalJacobiDirichletMatrix, Basis.toMatrix_apply,
    semiclassicalJacobiBasis_repr, semiclassicalJacobiDirichletTrial,
    semiclassicalJacobiBasis_apply, map_sum, map_smul, integralInner_sum_left hμ,
    hsmul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Solving the coefficient system is equivalent to orthogonality of the residual
against every polynomial in the finite trial space. -/
theorem semiclassicalJacobiDirichletSection_eq_iff_galerkin {t : ℝ} (ht : 1<t)
    (γ : ℝ) (N : ℕ) (f : ℝ[X]) (v : Fin N → ℝ) :
    semiclassicalJacobiDirichletSection ht γ N *ᵥ v =
        semiclassicalJacobiDirichletLoad ht γ N f ↔
      ∀ w : Fin N → ℝ, integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (semiclassicalJacobiDirichletTrial ht γ N v)-f) (semiclassicalJacobiDirichletTrial ht γ N w)) = 0 := by
  have hμ := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
    (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1)
  have hsmul (p q : ℝ[X]) (a : ℝ) := integralInner_smul_left _ p q a
    (h := hμ.integrable_mul _ _)
  constructor
  · intro h w
    rw [integralInner_comm]
    dsimp only [semiclassicalJacobiDirichletTrial]
    rw [integralInner_sum_left hμ]
    apply Finset.sum_eq_zero
    intro i hi
    have hrow := semiclassicalJacobiDirichletSection_mulVec ht γ N v i
    dsimp only [semiclassicalJacobiDirichletTrial] at hrow
    rw [hsmul, integralInner_comm, integralInner_sub_left hμ,
      ← hrow, congrFun h i]
    simp [semiclassicalJacobiDirichletLoad]
  · intro h
    funext i
    have hi := h (Pi.single i 1)
    simp only [semiclassicalJacobiDirichletTrial_single] at hi
    rw [integralInner_sub_left hμ, ← semiclassicalJacobiDirichletSection_mulVec] at hi
    exact sub_eq_zero.mp hi

/-- Polynomial forcing gives exactly one finite Galerkin coefficient vector. -/
theorem existsUnique_semiclassicalJacobiDirichletGalerkin {t : ℝ} (ht : 1<t)
    (γ : ℝ) (N : ℕ) (f : ℝ[X]) :
    ∃! v : Fin N → ℝ, ∀ w : Fin N → ℝ,
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (semiclassicalJacobiDirichletTrial ht γ N v)-f) (semiclassicalJacobiDirichletTrial ht γ N w)) = 0 := by
  simpa only [← semiclassicalJacobiDirichletSection_eq_iff_galerkin ht γ N f] using
    existsUnique_semiclassicalJacobiDirichletSection ht γ N
      (semiclassicalJacobiDirichletLoad ht γ N f)

/-- If the exact radial solution is already in the trial space, the finite solve recovers it. -/
theorem semiclassicalJacobiDirichletGalerkin_exact_on_trial {t : ℝ} (ht : 1<t)
    (γ : ℝ) (N : ℕ) (v w : Fin N → ℝ)
    (hv : semiclassicalJacobiDirichletSection ht γ N *ᵥ v =
      semiclassicalJacobiDirichletLoad ht γ N
        (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (semiclassicalJacobiDirichletTrial ht γ N w))) :
    v=w := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_semiclassicalJacobiDirichletSection ht γ N))
  rw [hv]
  funext i
  exact (semiclassicalJacobiDirichletSection_mulVec ht γ N w i).symm

end Polynomial
