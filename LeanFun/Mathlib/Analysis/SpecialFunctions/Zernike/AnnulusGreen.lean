/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusLaplacianIntegral

/-! # Cartesian polynomial Green identity on annuli
For boundary-weighted Cartesian polynomials, the integral of the gradient dot
product equals the negative-Laplacian pairing. All boundary terms are proved to
vanish. Reference: Green's first identity applied to the annular Dirichlet trials
of Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 15.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The polynomial negative-Laplacian pairing is symmetric on the entire boundary-weighted space. -/
theorem integralInner_annulus_boundary_laplacian_symm {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p z : MvPolynomial (Fin 2) ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusBoundaryWeight q*p)) (annulusBoundaryWeight q*z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusBoundaryWeight q*z)) (annulusBoundaryWeight q*p) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let B := LinearMap.mulLeft ℝ (annulusBoundaryWeight q)
  let F := (integralBilinForm μ hμ).compl₁₂ (diskLaplacianLinearMap.comp B) B
  have hm (u v : Bool) (m n : ℕ) (a b : Polynomial ℝ) :
      (F-F.flip) (annulusLift ⟨q,ne_of_lt hq.2⟩ u m a) (annulusLift ⟨q,ne_of_lt hq.2⟩ v n b) = 0 := by
    change integralInner μ (IntegrablePair.of μ (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m a)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n b) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) -
      integralInner μ (IntegrablePair.of μ (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n b)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m a) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = 0
    by_cases h : u=v ∧ m=n
    · obtain ⟨rfl, rfl⟩ := h
      dsimp [μ]
      simp only [diskLaplacian_annulusDirichletLift hq]
      rw [integralInner_annulusLift_dirichletLift hq, integralInner_annulusLift_dirichletLift hq,
        integralInner_semiclassicalJacobi_dirichlet_symm (one_lt_annulusParameter hq)]
      exact sub_self _
    · have hne : u≠v ∨ m≠n := by tauto
      rw [integralInner_annulusDirichletLaplacian_eq_zero hq hne,
        integralInner_annulusDirichletLaplacian_eq_zero hq (by tauto)]
      exact sub_self _
  have hk : LinearMap.ker (F-F.flip) = ⊤ := eq_top_of_annulusLift_mem hq _ (by
    intro u m a
    rw [LinearMap.mem_ker]
    have hs : LinearMap.ker ((F-F.flip) (annulusLift ⟨q,ne_of_lt hq.2⟩ u m a)) = ⊤ :=
      eq_top_of_annulusLift_mem hq _ (by intro v n b; exact hm u v m n a b)
    apply LinearMap.ext
    intro y
    have hy : y ∈ LinearMap.ker ((F-F.flip) (annulusLift ⟨q,ne_of_lt hq.2⟩ u m a)) := by rw [hs]; trivial
    exact hy)
  have hp : p ∈ LinearMap.ker (F-F.flip) := by rw [hk]; trivial
  have he := LinearMap.congr_fun (LinearMap.mem_ker.mp hp) z
  exact sub_eq_zero.mp he

/-- Green's first identity for all polynomial trials vanishing by the annular boundary factor. -/
theorem integralInner_annulus_gradient_eq_neg_laplacian {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p z : MvPolynomial (Fin 2) ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 0 (annulusBoundaryWeight q*p)) (pderiv 0 (annulusBoundaryWeight q*z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) +
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 1 (annulusBoundaryWeight q*p)) (pderiv 1 (annulusBoundaryWeight q*z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
    -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusBoundaryWeight q*p)) (annulusBoundaryWeight q*z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let J : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ := (integralBilinForm μ hμ).flip 1
  have hJ (f g : MvPolynomial (Fin 2) ℝ) : J (f*g) = integralInner μ (IntegrablePair.of μ f g (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    simp [J, integralBilinForm, integralInner]
  let f := annulusBoundaryWeight q*p
  let g := annulusBoundaryWeight q*z
  have hz : J (diskLaplacian (f*g)) = 0 := by
    have he : f*g = annulusBoundaryWeight q^2*(p*z) := by dsimp [f,g]; ring
    rw [he]
    simpa [J, integralBilinForm, integralInner] using integral_diskLaplacian_boundary_sq hq (p*z)
  rw [diskLaplacian_mul, map_add, map_add, hJ, hJ] at hz
  have ht : J (2*diskGradientProduct f g) = 2*J (diskGradientProduct f g) := by
    rw [two_mul, map_add, two_mul]
  rw [ht, diskGradientProduct, map_add, hJ, hJ, integralInner_comm μ f,
    integralInner_annulus_boundary_laplacian_symm hq z p] at hz
  change integralInner μ (IntegrablePair.of μ (pderiv 0 f) (pderiv 0 g) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) +
    integralInner μ (IntegrablePair.of μ (pderiv 1 f) (pderiv 1 g) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = -integralInner μ (IntegrablePair.of μ (diskLaplacian f) g (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _))
  linarith

/-- The Cartesian gradient energy of a sector agrees with the completed radial energy. -/
theorem integralInner_annulusDirichlet_gradient {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p z : Polynomial ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 0 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (pderiv 0 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) +
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 1 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (pderiv 1 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
    annulusEnergyScale ⟨q,ne_of_lt hq.2⟩ u m * inner ℝ
      (SemiclassicalJacobiEnergy.polynomialEmbed ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ m p)
      (SemiclassicalJacobiEnergy.polynomialEmbed ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ m z) := by
  calc
    _ = -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) :=
      integralInner_annulus_gradient_eq_neg_laplacian hq _ _
    _ = _ := neg_integralInner_annulusDirichletLaplacian hq u m p z

/-- Distinct angular sectors are orthogonal for Cartesian gradient energy. -/
theorem integralInner_annulusDirichlet_gradient_eq_zero {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {u v : Bool} {m n : ℕ} (h : u ≠ v ∨ m ≠ n) (p z : Polynomial ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 0 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (pderiv 0 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) +
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 1 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (pderiv 1 (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n z)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 := by
  calc
    _ = -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) :=
      integralInner_annulus_gradient_eq_neg_laplacian hq _ _
    _ = 0 := by rw [integralInner_annulusDirichletLaplacian_eq_zero hq h p z, neg_zero]

end MvPolynomial
