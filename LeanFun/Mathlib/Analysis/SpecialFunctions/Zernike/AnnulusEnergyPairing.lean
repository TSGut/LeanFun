/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusDirichlet
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergyBasis

/-! # Physical normalization of annular energy sectors
The planar negative-Laplacian pairing of boundary-vanishing polynomials is the
radial Dirichlet form times its angular and geometric scale. This is a polynomial
identity of integrals; identification with a Sobolev gradient norm is separate.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4 and Proposition 15.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- The physical scale multiplying the radial energy form in one real angular sector. -/
def annulusEnergyScale (q : {q : ℝ // q ≠ 1}) (u : Bool) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ((annulusParameter ⟨q,q.property⟩) ^ (m + 3))⁻¹ *
    zernikeAngularNormSq u m

/-- Every valid real angular sector has strictly positive physical energy scale. -/
theorem annulusEnergyScale_pos {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (hm : u = true → m ≠ 0) : 0 < annulusEnergyScale ⟨q,ne_of_lt hq.2⟩ u m := by
  have ht : 0 < annulusParameter ⟨q,ne_of_lt hq.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have hang : 0 < zernikeAngularNormSq u m := by
    cases u <;> simp only [zernikeAngularNormSq, Bool.false_eq_true, ↓reduceIte] at *
    · split_ifs <;> positivity
    · simp [hm, Real.pi_pos]
  unfold annulusEnergyScale
  positivity

/-- Pairing an unweighted mode with a boundary-weighted mode produces the (1,1,m) measure. -/
theorem integralInner_annulusLift_dirichletLift {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p z : Polynomial ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (annulusLift ⟨q,ne_of_lt hq.2⟩ u m p) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
      annulusEnergyScale ⟨q,ne_of_lt hq.2⟩ u m *
        Polynomial.integralInner (semiclassicalJacobiMeasure ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ 1 1 m) (Polynomial.IntegrablePair.of (semiclassicalJacobiMeasure ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ 1 1 m) p z (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := (m : ℝ)) (one_lt_annulusParameter hq)).integrable_mul _ _)) := by
  simp only [← annulusLift_dirichletWeight hq]
  change integralInner _ (IntegrablePair.of _ (diskRadialLift u _ m) (diskRadialLift u _ m) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = _
  rw [integralInner_annulusRadialLift_same_angular hq (by norm_num) (by norm_num)]
  have hi := integral_semiclassicalJacobiMeasure_annulus ⟨q,hq⟩ 1 1 m
    ⟨(fun x ↦ p.eval x * z.eval x),
      (hasFiniteMoments_semiclassicalJacobiMeasure_one_one
        (γ := (m : ℝ)) (one_lt_annulusParameter hq)).integrable_mul p z⟩
  have he : (∫ s : Ioo q 1, (1-(s : ℝ))^(0 : ℝ)*((s : ℝ)-q)^(0 : ℝ)*(s : ℝ)^m*
      ((p.comp (Polynomial.C (annulusParameter ⟨q,ne_of_lt hq.2⟩)*(1-Polynomial.X))).eval (s : ℝ) *
        ((annularDirichletWeight ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩*z).comp
          (Polynomial.C (annulusParameter ⟨q,ne_of_lt hq.2⟩)*(1-Polynomial.X))).eval (s : ℝ))) =
      ∫ s : Ioo q 1, (1-(s : ℝ))^(1 : ℝ)*((s : ℝ)-q)^(1 : ℝ)*(s : ℝ)^m*
        (p.eval (annulusParameter ⟨q,ne_of_lt hq.2⟩*(1-(s : ℝ)))*z.eval (annulusParameter ⟨q,ne_of_lt hq.2⟩*(1-(s : ℝ)))) := by
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [Polynomial.mul_comp, annularDirichletWeight_comp hq,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_comp, Real.rpow_zero, Real.rpow_one]
    ring
  rw [he]
  unfold annulusEnergyScale Polynomial.integralInner
  have hexp : (1 + 1 + (m : ℝ) + 1) = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hi, hexp, Real.rpow_natCast]
  have ht : 0 < annulusParameter ⟨q,ne_of_lt hq.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have hn : (annulusParameter ⟨q,ne_of_lt hq.2⟩) ^ (1 + 1 + (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  simp only [mul_comm (annulusParameter ⟨q,ne_of_lt hq.2⟩)]
  ring

/-- Distinct angular sectors are orthogonal for the planar negative-Laplacian pairing. -/
theorem integralInner_annulusDirichletLaplacian_eq_zero {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) {u v : Bool} {m n : ℕ}
    (h : u ≠ v ∨ m ≠ n) (p z : Polynomial ℝ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ v n z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 := by
  dsimp only [integralInner, IntegrablePair.of]
  rw [diskLaplacian_annulusDirichletLift hq, ← annulusLift_dirichletWeight hq]
  exact integralInner_annulusRadialLift_eq_zero_of_angular (a := 0) (b := 0) hq (by norm_num) (by norm_num) _ _ h

/-- The radial energy completion agrees with the polynomial planar pairing after scaling. -/
theorem neg_integralInner_annulusDirichletLaplacian {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (u : Bool) (m : ℕ) (p z : Polynomial ℝ) :
    -integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p)) (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m z) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) =
      annulusEnergyScale ⟨q,ne_of_lt hq.2⟩ u m * inner ℝ
        (SemiclassicalJacobiEnergy.polynomialEmbed ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ m p)
        (SemiclassicalJacobiEnergy.polynomialEmbed ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ m z) := by
  simp only [diskLaplacian_annulusDirichletLift hq]
  rw [integralInner_annulusLift_dirichletLift hq,
    SemiclassicalJacobiEnergy.inner_polynomialEmbed]
  ring

end MvPolynomial
