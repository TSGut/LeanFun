/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusDivergence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusSupport

/-! # A uniform polynomial Poincaré bound on annuli
For a polynomial trial vanishing on both boundary circles, its squared L² norm
is bounded by its Cartesian gradient energy. The constant is independent of
angular frequency and squared inner radius. The estimate is not claimed sharp.
Reference: the Dirichlet energy formulation of the annular method in
Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace MvPolynomial

/-- The radial divergence identity gives the polynomial dilation integration-by-parts formula. -/
theorem integralInner_annulus_boundary_euler {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (annulusBoundaryWeight q*p) (diskEuler (annulusBoundaryWeight q*p)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
      -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (annulusBoundaryWeight q*p) (annulusBoundaryWeight q*p) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let J : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ := (integralBilinForm μ hμ).flip 1
  have hJ (f g : MvPolynomial (Fin 2) ℝ) : J (f*g) = integralInner μ (IntegrablePair.of μ f g (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    simp [J, integralBilinForm, integralInner]
  let f := annulusBoundaryWeight q*p
  have hz : J (diskRadialDivergence (f*f)) = 0 := by
    have he : f*f = annulusBoundaryWeight q^2*(p*p) := by dsimp [f]; ring
    rw [he]
    simpa [J, integralBilinForm, integralInner] using
      integral_diskRadialDivergence_boundary_sq hq (p*p)
  have he : diskRadialDivergence (f*f) = (f*f+f*f)+(f*diskEuler f+f*diskEuler f) := by
    change (2 : ℝ) • (f*f)+diskEuler (f*f) = _
    rw [diskEuler_mul, show (2 : ℝ) = 1+1 by norm_num, add_smul, one_smul]
    ring
  rw [he, map_add, map_add, map_add, hJ, hJ] at hz
  change integralInner μ (IntegrablePair.of μ f (diskEuler f) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = -integralInner μ (IntegrablePair.of μ f f (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _))
  linarith

/-- A degree- and mode-independent Poincaré estimate for boundary-weighted annular polynomials. -/
theorem integralInner_annulus_boundary_le_gradient {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (annulusBoundaryWeight q*p) (annulusBoundaryWeight q*p) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) ≤
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 0 (annulusBoundaryWeight q*p)) (pderiv 0 (annulusBoundaryWeight q*p)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) +
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (pderiv 1 (annulusBoundaryWeight q*p)) (pderiv 1 (annulusBoundaryWeight q*p)) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let J : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ := (integralBilinForm μ hμ).flip 1
  have hJ (f g : MvPolynomial (Fin 2) ℝ) : J (f*g) = integralInner μ (IntegrablePair.of μ f g (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    simp [J, integralBilinForm, integralInner]
  let f := annulusBoundaryWeight q*p
  let P := diskGradientProduct f f+f*f+(f*diskEuler f+f*diskEuler f)
  have hn : 0 ≤ J P := by
    change 0 ≤ ∫ v, eval v P * eval v 1 ∂μ
    simp only [map_one, mul_one]
    apply integral_nonneg_zernikeAnnulusMeasure hq 0 0 P
      (_hi := by simpa only [map_one, mul_one] using hμ.integrable_mul P 1)
    intro v hv
    dsimp [P]
    simp only [diskGradientProduct, map_add, map_mul]
    change 0 ≤ eval v (pderiv 0 f)*eval v (pderiv 0 f) +
      eval v (pderiv 1 f)*eval v (pderiv 1 f) + eval v f*eval v f +
      (eval v f*eval v (diskEuler f)+eval v f*eval v (diskEuler f))
    have he : eval v (diskEuler f) = v 0*eval v (pderiv 0 f)+v 1*eval v (pderiv 1 f) := by
      change eval v (X 0*pderiv 0 f+X 1*pderiv 1 f) = _
      simp
    rw [he]
    have hid (a b c x y : ℝ) :
        b*b+c*c+a*a+(a*(x*b+y*c)+a*(x*b+y*c)) =
        (a+x*b+y*c)^2+(y*b-x*c)^2+(1-(x^2+y^2))*(b^2+c^2) := by ring
    rw [hid]
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sub_nonneg.mpr hv) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  dsimp [P] at hn
  rw [map_add, map_add, map_add, diskGradientProduct, map_add, hJ, hJ, hJ, hJ] at hn
  have he := integralInner_annulus_boundary_euler hq p
  change integralInner μ (IntegrablePair.of μ f (diskEuler f) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = -integralInner μ (IntegrablePair.of μ f f (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) at he
  change integralInner μ (IntegrablePair.of μ f f (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) ≤
    integralInner μ (IntegrablePair.of μ (pderiv 0 f) (pderiv 0 f) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _))+integralInner μ (IntegrablePair.of μ (pderiv 1 f) (pderiv 1 f) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _))
  linarith

/-- Equivalently, physical polynomial mass is bounded by the negative-Laplacian energy. -/
theorem integralInner_annulus_boundary_le_neg_laplacian {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (annulusBoundaryWeight q*p) (annulusBoundaryWeight q*p) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) ≤
    -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusBoundaryWeight q*p)) (annulusBoundaryWeight q*p) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  rw [← integralInner_annulus_gradient_eq_neg_laplacian hq]
  exact integralInner_annulus_boundary_le_gradient hq p

end MvPolynomial
