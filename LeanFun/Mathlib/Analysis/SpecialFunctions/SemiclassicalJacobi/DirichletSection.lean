/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergy
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletMass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.FiniteGalerkin

/-! # Definiteness and invertibility of finite annular Dirichlet sections
The energy identities survive every leading finite section, including the empty
section. Reference: the Galerkin energy argument applied to the operators in
Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 15.
-/

@[expose] public section
open Module Matrix
namespace Polynomial

/-- The leading square section of the physical weighted Laplacian. -/
noncomputable def semiclassicalJacobiDirichletSection {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (semiclassicalJacobiDirichletMatrix ht γ).submatrix Fin.val Fin.val

/-- The leading square section of boundary-weight multiplication. -/
noncomputable def semiclassicalJacobiDirichletMassSection {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (semiclassicalJacobiDirichletMass ht γ).submatrix Fin.val Fin.val

/-- Every negative Dirichlet section is positive definite. -/
theorem neg_semiclassicalJacobiDirichletSection_posDef {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    (-semiclassicalJacobiDirichletSection ht γ N).PosDef := by
  have hM := hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht
  have hsmul (p q : ℝ[X]) (a : ℝ) := integralInner_smul_left _ p q a
    (h := hM.integrable_mul _ _)
  let b := semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
    (by norm_num : (-1 : ℝ)<1) γ
  have hf := b.linearIndependent.comp (fun i : Fin N ↦ (i : ℕ)) Fin.val_injective
  have h := posDef_integralInner_operator
    (hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
      (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1))
    ((-1 : ℝ) • semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ) (fun i : Fin N ↦ b i) hf
    (by
      intro p q
      simp only [LinearMap.smul_apply, hsmul]
      rw [integralInner_semiclassicalJacobi_dirichlet_symm ht])
    (by
      intro p hp
      simpa only [LinearMap.smul_apply, hsmul, neg_one_mul] using
        neg_pos.mpr (integralInner_semiclassicalJacobi_dirichlet_neg ht γ hp))
  convert h using 1
  ext i j
  simp only [semiclassicalJacobiDirichletSection, Matrix.submatrix_apply,
    semiclassicalJacobiDirichletMatrix, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr,
    b, semiclassicalJacobiBasis_apply, LinearMap.smul_apply, hsmul,
    neg_one_mul, Matrix.neg_apply, Matrix.of_apply]

/-- Every mass section is positive definite. -/
theorem semiclassicalJacobiDirichletMassSection_posDef {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    (semiclassicalJacobiDirichletMassSection ht γ N).PosDef := by
  let b := semiclassicalJacobiBasis ht (by norm_num : (-1 : ℝ)<1)
    (by norm_num : (-1 : ℝ)<1) γ
  have hf := b.linearIndependent.comp (fun i : Fin N ↦ (i : ℕ)) Fin.val_injective
  have h := posDef_integralInner_operator
    (hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
      (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1))
    (LinearMap.mulLeft ℝ (annularDirichletWeight ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩)) (fun i : Fin N ↦ b i) hf
    (by
      intro p q
      simp only [LinearMap.mulLeft_apply, integralInner, eval_mul]
      congr 1
      funext x
      ring)
    (fun p hp ↦ integralInner_annularDirichletWeight_pos ht γ hp)
  convert h using 1
  ext i j
  simp only [semiclassicalJacobiDirichletMassSection, Matrix.submatrix_apply,
    semiclassicalJacobiDirichletMass, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr,
    b, semiclassicalJacobiBasis_apply, LinearMap.mulLeft_apply, Matrix.of_apply]

/-- No leading Dirichlet section is singular. -/
theorem isUnit_semiclassicalJacobiDirichletSection {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    IsUnit (semiclassicalJacobiDirichletSection ht γ N) := by
  simpa only [neg_neg] using (neg_semiclassicalJacobiDirichletSection_posDef ht γ N).isUnit.neg

/-- No leading mass section is singular. -/
theorem isUnit_semiclassicalJacobiDirichletMassSection {t : ℝ} (ht : 1<t) (γ : ℝ) (N : ℕ) :
    IsUnit (semiclassicalJacobiDirichletMassSection ht γ N) :=
  (semiclassicalJacobiDirichletMassSection_posDef ht γ N).isUnit

/-- Every finite right-hand side has exactly one coefficient solution. -/
theorem existsUnique_semiclassicalJacobiDirichletSection {t : ℝ} (ht : 1<t)
    (γ : ℝ) (N : ℕ) (f : Fin N → ℝ) :
    ∃! v : Fin N → ℝ, semiclassicalJacobiDirichletSection ht γ N *ᵥ v=f := by
  have hu := isUnit_semiclassicalJacobiDirichletSection ht γ N
  exact (Function.bijective_iff_existsUnique _).mp
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩ f

end Polynomial
