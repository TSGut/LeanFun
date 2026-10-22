/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.AnnularLaplacian

/-! # The weighted annular Dirichlet form
The physical boundary factor is t⁻² x(1-x). Its Laplacian is symmetric in
parameters (1,1,gamma). Reference: Papadopoulos–Gutleb–Slevinsky–Olver,
Proposition 15, equation (43).
-/

@[expose] public section
open MeasureTheory
namespace Polynomial

/-- The physical boundary factor in semiclassical coordinates. -/
noncomputable def annularDirichletWeight (t : {t : ℝ // t ≠ 0}) : ℝ[X] := C ((t : ℝ)⁻¹^2)*(X*(1-X))

/-- Classical evaluation of the nondegenerate boundary factor. -/
theorem eval_annularDirichletWeight (t : {t : ℝ // t ≠ 0}) (x : ℝ) :
    (annularDirichletWeight t).eval x = (t : ℝ)⁻¹^2 * (x*(1-x)) := by
  simp only [annularDirichletWeight, eval_mul, eval_C, eval_sub, eval_one, eval_X]

/-- Differentiate after inserting both endpoint zeros. -/
noncomputable def semiclassicalJacobiABWeightedDerivativeMap : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  derivative.comp (LinearMap.mulLeft ℝ (X*(1-X)))

/-- Explicit action of endpoint-weighted differentiation. -/
theorem semiclassicalJacobiABWeightedDerivativeMap_apply (p : ℝ[X]) :
    semiclassicalJacobiABWeightedDerivativeMap p = X*(1-X)*p.derivative+(1-2*X)*p := by
  simp [semiclassicalJacobiABWeightedDerivativeMap, derivative_mul]
  ring

/-- The Laplacian of a boundary-weighted radial polynomial, in the same parameter family. -/
noncomputable def semiclassicalJacobiDirichletMap (t : {t : ℝ // t ≠ 0}) (γ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (4/(t : ℝ)) • (semiclassicalJacobiCWeightedDerivativeMap t γ).comp
    semiclassicalJacobiABWeightedDerivativeMap

/-- The geometric scalar agrees with the Cartesian radial Laplacian. -/
theorem semiclassicalJacobiDirichletMap_eq (t γ : ℝ) (ht : t≠0) (p : ℝ[X]) :
    semiclassicalJacobiDirichletMap ⟨t,ht⟩ γ p =
      semiclassicalJacobiAnnularLaplacianMap t γ (annularDirichletWeight ⟨t,ht⟩*p) := by
  simp only [semiclassicalJacobiDirichletMap, semiclassicalJacobiAnnularLaplacianMap,
    LinearMap.smul_apply, LinearMap.comp_apply]
  have he : annularDirichletWeight ⟨t,ht⟩*p = t⁻¹^2 • (X*(1-X)*p) := by
    simp [annularDirichletWeight, smul_eq_C_mul, mul_assoc]
  rw [he, map_smul, map_smul, smul_smul]
  congr 1
  field_simp

/-- The endpoint-vanishing Dirichlet weight has all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_semiclassicalJacobiMeasure_one_one {t γ : ℝ} (ht : 1<t) :
    HasFiniteMoments (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) :=
  hasFiniteMoments_semiclassicalJacobiMeasure ht (by norm_num) (by norm_num)

/-- The derivative Gram weight has all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_semiclassicalJacobiMeasure_zero_zero {t γ : ℝ} (ht : 1<t) :
    HasFiniteMoments (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 0 0 γ) :=
  hasFiniteMoments_semiclassicalJacobiMeasure ht (by norm_num) (by norm_num)

/-- Integration by parts expresses the weighted Laplacian as a negative derivative Gram form. -/
theorem integralInner_semiclassicalJacobi_dirichlet {t : ℝ} (ht : 1<t)
    (γ : ℝ) (p q : ℝ[X]) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ p) q) =
      -(4/t)*integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 0 0 (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 0 0 (γ+1)) (semiclassicalJacobiABWeightedDerivativeMap p) (semiclassicalJacobiABWeightedDerivativeMap q)) := by
  have he := integralInner_semiclassicalJacobi_cWeightedDerivative
    (α := 0) (β := 0) (γ := γ) ht (by norm_num) (by norm_num)
    (semiclassicalJacobiABWeightedDerivativeMap p) q
  simp only [integralInner, zero_add, C_1, one_mul] at he
  have hq : X*(1-X)*q.derivative+((1-X)-X)*q =
      semiclassicalJacobiABWeightedDerivativeMap q := by
    rw [semiclassicalJacobiABWeightedDerivativeMap_apply]
    ring
  rw [hq] at he
  change integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ)
    ((hasFiniteMoments_semiclassicalJacobiMeasure_one_one ht).pair
      ((4/t) • semiclassicalJacobiCWeightedDerivativeMap t γ (semiclassicalJacobiABWeightedDerivativeMap p)) q) = _
  rw [integralInner_smul_left (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one ht).integrable_mul _ _)]
  simp only [integralInner]
  rw [he]
  ring

/-- The weighted radial Laplacian is symmetric in the (1,1,gamma) pairing. -/
theorem integralInner_semiclassicalJacobi_dirichlet_symm {t : ℝ} (ht : 1<t)
    (γ : ℝ) (p q : ℝ[X]) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ p) q) =
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ q) p) := by
  rw [integralInner_semiclassicalJacobi_dirichlet ht,
    integralInner_semiclassicalJacobi_dirichlet ht, integralInner_comm]

/-- Endpoint-weighted differentiation raises degree by at most one. -/
theorem natDegree_semiclassicalJacobiABWeightedDerivativeMap_le (p : ℝ[X]) :
    (semiclassicalJacobiABWeightedDerivativeMap p).natDegree ≤ p.natDegree+1 := by
  have h := natDegree_semiclassicalJacobi_cAdjoint_le 0 0 p
  simp only [zero_add, C_1, one_mul] at h
  rw [semiclassicalJacobiABWeightedDerivativeMap_apply]
  convert h using 1
  congr 1
  ring

/-- The weighted annular Laplacian raises radial degree by at most one. -/
theorem natDegree_semiclassicalJacobiDirichletMap_le (t : {t : ℝ // t ≠ 0}) (γ : ℝ) (p : ℝ[X]) :
    (semiclassicalJacobiDirichletMap ⟨t,t.property⟩ γ p).natDegree ≤ p.natDegree+1 := by
  change ((4/(t : ℝ)) • semiclassicalJacobiCWeightedDerivativeMap t γ
    (semiclassicalJacobiABWeightedDerivativeMap p)).natDegree ≤ _
  exact (natDegree_smul_le _ _).trans ((natDegree_semiclassicalJacobiCWeightedDerivativeMap_le _ _ _).trans
    (natDegree_semiclassicalJacobiABWeightedDerivativeMap_le p))

end Polynomial
