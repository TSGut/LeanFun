/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusRadialL2Injective
public import LeanFun.Mathlib.Analysis.Normed.Lp.OrthogonalSynthesis

/-! # Physical L² synthesis of all annular energy sectors
The inverse square-root sector scaling converts the radial realizations into
orthogonal contractions. Their synthesis extends the physical polynomial lifts
to the entire angular energy Hilbert sum.
Reference: real angular separation in Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory
namespace MvPolynomial.AnnularEnergy

/-- Physical radial realizations of distinct completed angular sectors remain orthogonal. -/
theorem inner_radialL2_eq_zero (q : Set.Ioo (0 : ℝ) 1) {s r : Sector} (h : s ≠ r)
    (x : RadialSpace q s) (y : RadialSpace q r) :
    inner ℝ (radialL2 q s x) (radialL2 q r y) = 0 := by
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) s.val.2).induction
    ?_ (isClosed_eq (by fun_prop) continuous_const) x
  rintro _ ⟨p, rfl⟩
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) r.val.2).induction
    ?_ (isClosed_eq (by fun_prop) continuous_const) y
  rintro _ ⟨z, rfl⟩
  rw [radialL2_polynomialEmbed, radialL2_polynomialEmbed]
  change inner ℝ (MvPolynomial.polynomialToL2 (physicalMeasure_moments q) _)
    (MvPolynomial.polynomialToL2 (physicalMeasure_moments q) _) = 0
  rw [MvPolynomial.inner_polynomialToL2]
  change integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ r.val.1 r.val.2 z) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) = 0
  rw [← annulusLift_dirichletWeight q.property, ← annulusLift_dirichletWeight q.property]
  apply integralInner_annulusRadialLift_eq_zero_of_angular q.property (by norm_num) (by norm_num)
  by_contra! he
  exact h (Subtype.ext (Prod.ext he.1 he.2))

/-- Physical L² realization of a normalized angular energy coordinate. -/
def sectorL2 (q : Set.Ioo (0 : ℝ) 1) (s : Sector) : RadialSpace q s →L[ℝ] PhysicalL2 q :=
  (Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2))⁻¹ • radialL2 q s

/-- Every normalized sector realization is a contraction. -/
theorem norm_sectorL2_le (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (x : RadialSpace q s) :
    ‖sectorL2 q s x‖ ≤ ‖x‖ := by
  have hs : 0 < Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) :=
    Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)
  simp only [sectorL2, smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hs.le)]
  calc
    _ ≤ (Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2))⁻¹ *
        (Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_radialL2_le q s x) (inv_nonneg.mpr hs.le)
    _ = ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

/-- Normalization preserves orthogonality between distinct sectors. -/
theorem inner_sectorL2_eq_zero (q : Set.Ioo (0 : ℝ) 1) (s r : Sector) (h : s ≠ r)
    (x : RadialSpace q s) (y : RadialSpace q r) :
    inner ℝ (sectorL2 q s x) (sectorL2 q r y) = 0 := by
  simp [sectorL2, real_inner_smul_left, inner_smul_right, inner_radialL2_eq_zero q h]

/-- No normalized sector energy vector is lost in its physical L² realization. -/
theorem sectorL2_injective (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :
    Function.Injective (sectorL2 q s) := by
  intro x y h
  apply radialL2_injective q s
  have hs : Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne'
  have he := congrArg (fun z : PhysicalL2 q ↦ Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) • z) h
  simpa [sectorL2, smul_smul, mul_inv_cancel₀ hs] using he

/-- The physical L² realization of the full completed annular energy space. -/
def physicalL2 (q : Set.Ioo (0 : ℝ) 1) : Space q →L[ℝ] PhysicalL2 q :=
  lp.orthogonalSynthesis (sectorL2 q) (norm_sectorL2_le q) (inner_sectorL2_eq_zero q)

/-- The full energy completion has a faithful physical L² realization. -/
theorem physicalL2_injective (q : Set.Ioo (0 : ℝ) 1) :
    Function.Injective (physicalL2 q) :=
  lp.orthogonalSynthesis_injective _ _ _ (sectorL2_injective q)

/-- The normalized physical sector series converges unconditionally in L². -/
theorem hasSum_physicalL2 (q : Set.Ioo (0 : ℝ) 1) (x : Space q) :
    HasSum (fun s ↦ sectorL2 q s (x s)) (physicalL2 q x) :=
  lp.hasSum_orthogonalSynthesis _ _ _ x

/-- The global Poincaré bound persists on the full angular energy completion. -/
theorem norm_physicalL2_le (q : Set.Ioo (0 : ℝ) 1) (x : Space q) :
    ‖physicalL2 q x‖ ≤ ‖x‖ := lp.norm_orthogonalSynthesis_le _ _ _ x

/-- A single energy coordinate has the specified normalized sector realization. -/
theorem physicalL2_sectorEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (x : RadialSpace q s) :
    physicalL2 q (sectorEmbed q s x) = sectorL2 q s x := by
  classical
  exact lp.orthogonalSynthesis_single _ _ _ s x

/-- Physical polynomial embedding cancels the coordinate normalization exactly. -/
theorem physicalL2_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p : Polynomial ℝ) :
    physicalL2 q (polynomialEmbed q s p) = radialPolynomialL2 q s p := by
  have hs : Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne'
  simp only [polynomialEmbed, LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, map_smul, physicalL2_sectorEmbed, sectorL2,
    smul_apply, smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact radialL2_polynomialEmbed q s p

end MvPolynomial.AnnularEnergy
