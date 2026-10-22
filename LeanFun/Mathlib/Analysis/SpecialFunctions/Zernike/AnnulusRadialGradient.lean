/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusL2

/-! # Cartesian gradient classes for completed annular sectors
The two polynomial Cartesian derivatives form a physical L² vector field.
Green's identity makes its normalized lift an isometry for radial energy.
This is a completion of polynomial gradients; weak-derivative identification
against general smooth tests is a subsequent analytical step.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory
namespace MvPolynomial.AnnularEnergy

/-- Two physical L² components, with the Euclidean sum norm for Cartesian gradients. -/
abbrev GradientL2 (q : Set.Ioo (0 : ℝ) 1) := lp (fun _ : Fin 2 ↦ PhysicalL2 q) 2

/-- A polynomial's two Cartesian derivatives as physical L² classes. -/
def polynomialGradient (q : Set.Ioo (0 : ℝ) 1) :
    MvPolynomial (Fin 2) ℝ →ₗ[ℝ] GradientL2 q :=
  (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 0).toLinearMap.comp
      ((MvPolynomial.polynomialToL2 (physicalMeasure_moments q)).comp (pderiv 0).toLinearMap) +
    (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 1).toLinearMap.comp
      ((MvPolynomial.polynomialToL2 (physicalMeasure_moments q)).comp (pderiv 1).toLinearMap)

/-- Each coordinate is exactly its Cartesian partial derivative class. -/
theorem polynomialGradient_apply (q : Set.Ioo (0 : ℝ) 1) (p : MvPolynomial (Fin 2) ℝ)
    (i : Fin 2) : polynomialGradient q p i =
      MvPolynomial.polynomialToL2 (physicalMeasure_moments q) (pderiv i p) := by
  fin_cases i <;> simp [polynomialGradient, lp.single_apply]

/-- The vector-field inner product is the integral of the Cartesian gradient dot product. -/
theorem inner_polynomialGradient (q : Set.Ioo (0 : ℝ) 1) (p z : MvPolynomial (Fin 2) ℝ) :
    inner ℝ (polynomialGradient q p) (polynomialGradient q z) =
      integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (pderiv 0 p) (pderiv 0 z) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) +
      integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (pderiv 1 p) (pderiv 1 z) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  rw [lp.inner_eq_tsum, tsum_fintype, Fin.sum_univ_two]
  simp only [polynomialGradient_apply, MvPolynomial.inner_polynomialToL2, integralInner]

/-- The gradient of a boundary-weighted sector polynomial. -/
def radialPolynomialGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :
    Polynomial ℝ →ₗ[ℝ] GradientL2 q :=
  (polynomialGradient q).comp (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2)

/-- Cartesian gradient inner products agree with scaled radial energy. -/
theorem inner_radialPolynomialGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (p z : Polynomial ℝ) :
    inner ℝ (radialPolynomialGradient q s p) (radialPolynomialGradient q s z) =
      annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 * inner ℝ
        (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p)
        (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 z) := by
  change inner ℝ (polynomialGradient q _) (polynomialGradient q _) = _
  rw [inner_polynomialGradient]
  exact integralInner_annulusDirichlet_gradient q.property s.val.1 s.val.2 p z

/-- Polynomial gradients in the normalized angular energy coordinates. -/
def normalizedPolynomialGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :
    Polynomial ℝ →ₗ[ℝ] GradientL2 q :=
  (Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2))⁻¹ • radialPolynomialGradient q s

/-- The normalization removes the physical sector factor from gradient energy. -/
theorem inner_normalizedPolynomialGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (p z : Polynomial ℝ) :
    inner ℝ (normalizedPolynomialGradient q s p) (normalizedPolynomialGradient q s z) =
      inner ℝ (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p)
        (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 z) := by
  have hs := Real.sq_sqrt (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property).le
  have hn : Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne'
  simp only [normalizedPolynomialGradient, LinearMap.smul_apply, real_inner_smul_left,
    inner_smul_right, inner_radialPolynomialGradient]
  field_simp
  rw [hs]

/-- Normalized polynomial gradients preserve the radial energy norm. -/
theorem norm_normalizedPolynomialGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (p : Polynomial ℝ) :
    ‖normalizedPolynomialGradient q s p‖ =
      ‖SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p‖ := by
  have h := inner_normalizedPolynomialGradient q s p p
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (normalizedPolynomialGradient q s p),
    norm_nonneg (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p)]

/-- Completed normalized sector energy is realized isometrically as Cartesian gradient classes. -/
def sectorGradient (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :
    RadialSpace q s →ₗᵢ[ℝ] GradientL2 q :=
  (normalizedPolynomialGradient q s).extendOfIsometry
    (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed _ _)
    (norm_normalizedPolynomialGradient q s)

/-- The completed sector gradient agrees with its polynomial Cartesian derivatives. -/
theorem sectorGradient_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p : Polynomial ℝ) :
    sectorGradient q s (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p) =
      normalizedPolynomialGradient q s p :=
  LinearMap.extendOfIsometry_eq _ _ _ p

end MvPolynomial.AnnularEnergy
