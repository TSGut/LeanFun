/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletForm

/-! # Symmetric tridiagonal annular Dirichlet Laplacians
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 15.
-/

@[expose] public section
open Module
namespace Polynomial

/-- The physical weighted Laplacian in the orthonormal (1,1,gamma) basis. -/
noncomputable def semiclassicalJacobiDirichletMatrix {t : ℝ} (ht : 1<t) (γ : ℝ) :
    Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ).toMatrix
    (fun n ↦ semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ
      (semiclassicalJacobiSequence ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ n))

/-- The actual coefficient entries are symmetric. -/
theorem semiclassicalJacobiDirichletMatrix_symm {t : ℝ} (ht : 1<t) (γ : ℝ) (i j : ℕ) :
    semiclassicalJacobiDirichletMatrix ht γ i j =
      semiclassicalJacobiDirichletMatrix ht γ j i := by
  simp only [semiclassicalJacobiDirichletMatrix, Basis.toMatrix_apply,
    semiclassicalJacobiBasis_repr]
  exact integralInner_semiclassicalJacobi_dirichlet_symm ht γ _ _

/-- Only the main diagonal and its two neighbors can be nonzero. -/
theorem semiclassicalJacobiDirichletMatrix_eq_zero {t : ℝ} (ht : 1<t) (γ : ℝ)
    (i j : ℕ) (hgap : j+1 < i ∨ i+1 < j) :
    semiclassicalJacobiDirichletMatrix ht γ i j = 0 := by
  have hu (i j : ℕ) (h : j+1 < i) : semiclassicalJacobiDirichletMatrix ht γ i j = 0 := by
    rw [semiclassicalJacobiDirichletMatrix, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr]
    apply (semiclassicalJacobiSequence_spec ht (by norm_num : (-1 : ℝ)<1)
      (by norm_num : (-1 : ℝ) < 1) γ).1.integralInner_eq_zero_of_degree_lt
        (hasFiniteMoments_semiclassicalJacobiMeasure ht (by norm_num : (-1 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1))
    apply degree_le_natDegree.trans_lt
    have hd := natDegree_semiclassicalJacobiDirichletMap_le ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ
      (semiclassicalJacobiSequence ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ j)
    rw [Sequence.natDegree_eq] at hd
    exact_mod_cast hd.trans_lt h
  rcases hgap with h | h
  · exact hu i j h
  · rw [semiclassicalJacobiDirichletMatrix_symm]
    exact hu j i h

/-- Finite coefficient action reconstructs the physical weighted Laplacian exactly. -/
theorem semiclassicalJacobi_dirichlet_coefficientMap_exact {t : ℝ} (ht : 1<t)
    (γ : ℝ) (v : ℕ →₀ ℝ) :
    (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ).repr.symm
      ((semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ).coefficientMap
        (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ)
        (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ) v) =
      semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ
        ((semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ).repr.symm v) :=
  Basis.repr_symm_coefficientMap _ _ _ _

end Polynomial
