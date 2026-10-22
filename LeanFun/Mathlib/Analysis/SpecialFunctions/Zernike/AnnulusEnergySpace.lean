/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergyPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergySolve
public import LeanFun.Mathlib.Analysis.Normed.Lp.HilbertSumGalerkin

/-! # The Hilbert sum of annular energy sectors
The zero sine mode is excluded. Coordinates absorb the square root of the
physical sector scale, so the Hilbert sum extends the planar polynomial energy
pairing. No identification with a zero-trace Sobolev space is asserted here.
Reference: the real angular separation in Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Polynomial
namespace MvPolynomial.AnnularEnergy

/-- Valid real harmonics: all cosine modes and the nonzero sine modes. -/
abbrev Sector := {s : Bool × ℕ // s.1 = true → s.2 ≠ 0}

/-- The radial completion parameter corresponding to a nondegenerate annulus. -/
def parameter (q : Set.Ioo (0 : ℝ) 1) : Set.Ioi (1 : ℝ) :=
  ⟨annulusParameter ⟨q,ne_of_lt q.property.2⟩, one_lt_annulusParameter q.property⟩

/-- The completed radial energy space belonging to a real angular harmonic. -/
abbrev RadialSpace (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :=
  SemiclassicalJacobiEnergy.Space (parameter q) s.val.2

/-- The angular Hilbert sum, using physically normalized sector coordinates. -/
abbrev Space (q : Set.Ioo (0 : ℝ) 1) := lp (RadialSpace q) 2

/-- Injection of one normalized angular sector. -/
def sectorEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) : RadialSpace q s →L[ℝ] Space q :=
  lp.singleContinuousLinearMap ℝ (RadialSpace q) 2 s

/-- A physical boundary-weighted polynomial maps to a scaled Hilbert-sum coordinate. -/
def polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) : Polynomial ℝ →ₗ[ℝ] Space q :=
  Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) •
    (sectorEmbed q s).toLinearMap.comp
      (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2)

/-- In each sector the Hilbert-sum inner product is the exact planar polynomial pairing. -/
theorem inner_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p z : Polynomial ℝ) :
    inner ℝ (polynomialEmbed q s p) (polynomialEmbed q s z) =
      -integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 z) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  rw [neg_integralInner_annulusDirichletLaplacian q.property]
  simp only [polynomialEmbed, LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, sectorEmbed, lp.singleContinuousLinearMap_apply,
    real_inner_smul_left, inner_smul_right, lp.inner_single_left, lp.single_apply,
    Pi.single_eq_same]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt
    (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property).le]
  rfl

/-- Different valid angular coordinates are orthogonal. -/
theorem inner_polynomialEmbed_eq_zero (q : Set.Ioo (0 : ℝ) 1) {s r : Sector}
    (h : s ≠ r) (p z : Polynomial ℝ) :
    inner ℝ (polynomialEmbed q s p) (polynomialEmbed q r z) = 0 := by
  simp [polynomialEmbed, sectorEmbed, real_inner_smul_left, inner_smul_right,
    lp.inner_single_left, lp.single_apply, h]

/-- Finite angular sets with radial degree below N define the combined trial spaces. -/
def trialSpace (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ) : Submodule ℝ (Space q) :=
  lp.HilbertSumGalerkin.trialSpace
    (fun s : Sector ↦ SemiclassicalJacobiEnergy.trialSpace (parameter q) s.val.2) c

instance (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ) :
    FiniteDimensional ℝ (trialSpace q c) := by
  unfold trialSpace
  infer_instance

/-- The combined angular and radial polynomial trial spaces have dense union. -/
theorem trialSpace_closure_iSup (q : Set.Ioo (0 : ℝ) 1) :
    (⨆ c, trialSpace q c).topologicalClosure = ⊤ :=
  lp.HilbertSumGalerkin.trialSpace_closure_iSup _
    (fun s ↦ SemiclassicalJacobiEnergy.trialSpace_mono (parameter q) s.val.2)
    (fun s ↦ SemiclassicalJacobiEnergy.trialSpace_closure_iSup (parameter q) s.val.2)

end MvPolynomial.AnnularEnergy
