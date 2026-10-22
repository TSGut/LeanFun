/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletBestApproximation
public import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Completion in the annular Dirichlet energy norm
This is the energy completion of radial polynomial factors in one angular sector.
It is not yet identified with a Sobolev space on the planar annulus.
The type synonym keeps this norm separate from other polynomial norms.
-/

@[expose] public noncomputable section
namespace Polynomial.SemiclassicalJacobiEnergy

/-- The external singularity lies strictly beyond the integration interval. -/
theorem gt_one (t : Set.Ioi (1 : ℝ)) : 1 < (t : ℝ) := t.property

/-- Radial polynomials with the parameter-dependent Dirichlet energy norm. -/
def PolynomialSpace (_t : Set.Ioi (1 : ℝ)) (_γ : ℝ) := Polynomial ℝ

instance (t : Set.Ioi (1 : ℝ)) (γ : ℝ) : AddCommGroup (PolynomialSpace t γ) :=
  inferInstanceAs (AddCommGroup (Polynomial ℝ))

instance (t : Set.Ioi (1 : ℝ)) (γ : ℝ) : Module ℝ (PolynomialSpace t γ) :=
  inferInstanceAs (Module ℝ (Polynomial ℝ))

/-- Forget only the energy norm, retaining the polynomial algebra. -/
def polynomialEquiv (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    PolynomialSpace t γ ≃ₗ[ℝ] Polynomial ℝ := LinearEquiv.refl ℝ _

/-- The negative Dirichlet form supplies an inner product before completion. -/
@[instance_reducible]
def innerCore (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    InnerProductSpace.Core ℝ (PolynomialSpace t γ) where
  inner p q := -integralInner (semiclassicalJacobiMeasure t 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure t 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ q) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _))
  conj_inner_symm p q := by
    change -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ q)) (polynomialEquiv t γ p) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _)) =
      -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ q) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _))
    rw [integralInner_semiclassicalJacobi_dirichlet_symm (gt_one t)]
  re_inner_nonneg p := semiclassicalJacobiDirichletEnergy_nonneg (gt_one t) γ _
  add_left p q r := by
    simp only [map_add]
    rw [integralInner_add_left
      (hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) (gt_one t)
        (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1)), neg_add]
  smul_left p q a := by
    change -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ (a • p))) (polynomialEquiv t γ q) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _)) =
      a * -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ q) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _))
    simp only [map_smul]
    rw [integralInner_smul_left (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _)]
    ring
  definite p hp := by
    by_contra hne
    have h := integralInner_semiclassicalJacobi_dirichlet_neg (gt_one t) γ
      ((polynomialEquiv t γ).map_ne_zero_iff.mpr hne)
    change -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ p) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _))=0 at hp
    linarith

noncomputable instance (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    NormedAddCommGroup (PolynomialSpace t γ) := by
  letI := innerCore t γ
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    InnerProductSpace ℝ (PolynomialSpace t γ) := by
  letI := innerCore t γ
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (PolynomialSpace t γ))

/-- The norm squared is the proved polynomial Dirichlet energy. -/
theorem norm_sq_eq_energy (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (p : PolynomialSpace t γ) :
    ‖p‖^2 = semiclassicalJacobiDirichletEnergy t γ (polynomialEquiv t γ p) := by
  rw [← real_inner_self_eq_norm_sq]
  rfl

/-- The Hilbert space obtained by completing radial polynomials in Dirichlet energy. -/
abbrev Space (t : Set.Ioi (1 : ℝ)) (γ : ℝ) := UniformSpace.Completion (PolynomialSpace t γ)

/-- The canonical polynomial embedding preserves the energy norm. -/
noncomputable def embed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    PolynomialSpace t γ →ₗᵢ[ℝ] Space t γ := UniformSpace.Completion.toComplₗᵢ

/-- The completed inner product extends the polynomial Dirichlet form exactly. -/
theorem inner_embed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (p q : PolynomialSpace t γ) :
    inner ℝ (embed t γ p) (embed t γ q) =
      -integralInner (semiclassicalJacobiMeasure t 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure t 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ q) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) (gt_one t)).integrable_mul _ _)) := by
  change inner ℝ (p : Space t γ) (q : Space t γ) = _
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-- Radial polynomials are dense in the chosen energy completion. -/
theorem denseRange_embed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) : DenseRange (embed t γ) :=
  UniformSpace.Completion.denseRange_coe

end Polynomial.SemiclassicalJacobiEnergy
