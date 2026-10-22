/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletMatrix

/-! # Pentadiagonal boundary-weight multiplication
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 5.
-/

@[expose] public section
open Module MeasureTheory
namespace Polynomial

/-- Multiplication by the physical boundary weight in the same (1,1,gamma) basis. -/
noncomputable def semiclassicalJacobiDirichletMass {t : ℝ} (ht : 1<t) (γ : ℝ) :
    Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ).toMatrix
    (fun n ↦ annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ *
      semiclassicalJacobiSequence ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ n)

/-- Boundary-weight multiplication is symmetric. -/
theorem semiclassicalJacobiDirichletMass_symm {t : ℝ} (ht : 1<t) (γ : ℝ) (i j : ℕ) :
    semiclassicalJacobiDirichletMass ht γ i j = semiclassicalJacobiDirichletMass ht γ j i := by
  simp only [semiclassicalJacobiDirichletMass, Basis.toMatrix_apply,
    semiclassicalJacobiBasis_repr, integralInner, eval_mul]
  congr 1
  funext x
  ring

/-- The mass matrix has only the main diagonal and its first two neighbors on each side. -/
theorem semiclassicalJacobiDirichletMass_eq_zero {t : ℝ} (ht : 1<t) (γ : ℝ)
    (i j : ℕ) (hgap : j+2 < i ∨ i+2 < j) :
    semiclassicalJacobiDirichletMass ht γ i j=0 := by
  have hu (i j : ℕ) (h : j+2 < i) : semiclassicalJacobiDirichletMass ht γ i j=0 := by
    rw [semiclassicalJacobiDirichletMass, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr]
    apply (semiclassicalJacobiSequence_spec ht (by norm_num : (-1 : ℝ)<1)
      (by norm_num : (-1 : ℝ) < 1) γ).1.integralInner_eq_zero_of_degree_lt
        (hasFiniteMoments_semiclassicalJacobiMeasure ht (by norm_num : (-1 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1))
    apply degree_le_natDegree.trans_lt
    have hd : (annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩).natDegree ≤ 2 := by
      unfold annularDirichletWeight
      compute_degree
    have hp := natDegree_mul_le (p := annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩)
      (q := semiclassicalJacobiSequence ht (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) γ j)
    rw [Sequence.natDegree_eq] at hp
    exact_mod_cast hp.trans_lt (by omega)
  rcases hgap with h | h
  · exact hu i j h
  · rw [semiclassicalJacobiDirichletMass_symm]
    exact hu j i h

/-- The mass form is strictly positive on every nonzero polynomial. -/
theorem integralInner_annularDirichletWeight_pos {t : ℝ} (ht : 1<t) (γ : ℝ)
    {p : ℝ[X]} (hp : p≠0) :
    0 < integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩*p) p) := by
  have he := integralInner_semiclassicalJacobi_ab_add_one
    (α := 1) (β := 1) (γ := γ) ht p p
      (hi := (hasFiniteMoments_semiclassicalJacobiMeasure ht (by norm_num) (by norm_num)).integrable_mul _ _)
      (hj := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one ht).integrable_mul _ _)
  have hw : annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩*p = t⁻¹^2 • (X*(1-X)*p) := by
    simp [annularDirichletWeight, smul_eq_C_mul, mul_assoc]
  simp only [hw]
  rw [integralInner_smul_left (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one ht).integrable_mul _ _), ← he, integralInner_self]
  have hp' := hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure
    (γ := γ) ht (by norm_num : (-1 : ℝ)<2) (by norm_num : (-1 : ℝ)<2) p hp
  have ht' : 0<t := by linarith
  convert (mul_pos (pow_pos (inv_pos.mpr ht') 2) hp') using 1
  norm_num

end Polynomial
