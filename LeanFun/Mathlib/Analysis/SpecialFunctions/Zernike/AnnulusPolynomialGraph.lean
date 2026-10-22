/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusGradient
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPolynomialSpan
/-! # Cartesian polynomial trials in the completed annular energy graph

Finite annular angular-sector spanning realizes every boundary-weighted
Cartesian polynomial in the completed energy space, with its exact physical
function and gradient classes.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace MvPolynomial.AnnularEnergy
/-- Every boundary-weighted Cartesian polynomial has an exact energy-space realization. -/
theorem exists_functionGradient_polynomial (q : Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∃ x : Space q, functionGradient q x =
      (polynomialToL2 (physicalMeasure_moments q) (annulusBoundaryWeight q*p),
       polynomialGradient q (annulusBoundaryWeight q*p)) := by
  let F := (polynomialToL2 (physicalMeasure_moments q)).prod (polynomialGradient q)
  let B := LinearMap.mulLeft ℝ (annulusBoundaryWeight q)
  let K := (functionGradient q).toLinearMap.range.comap (F.comp B)
  have hK : K = ⊤ := eq_top_of_annulusLift_mem q.property K (by
    intro u m z
    by_cases h : u = true → m ≠ 0
    · let s : Sector := ⟨(u,m),h⟩
      refine ⟨polynomialEmbed q s z, ?_⟩
      change (physicalL2 q (polynomialEmbed q s z),gradientL2 q (polynomialEmbed q s z)) = _
      rw [physicalL2_polynomialEmbed, gradientL2_polynomialEmbed]
      rfl
    · push Not at h
      obtain ⟨rfl,rfl⟩ := h
      have hz : annulusLift ⟨q,ne_of_lt q.property.2⟩ true 0 z = 0 := by
        simp [annulusLift,diskRadialLift,diskHarmonics]
      rw [hz]
      exact K.zero_mem)
  have hp : p ∈ K := by rw [hK]; trivial
  exact hp
end MvPolynomial.AnnularEnergy
