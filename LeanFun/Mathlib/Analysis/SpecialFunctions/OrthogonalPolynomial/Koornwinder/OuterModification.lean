/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.SubtypeDensityMeasure

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Construction
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Connection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.SeparatedModification
import Mathlib.Topology.Algebra.Polynomial

/-!
# Outer-variable modifications of generalised Koornwinder systems

The inner sequence and its polynomial lifts are retained exactly. The squared
scale has no degree restriction. Reference: Dunkl–Xu, §2.6.1;
Gutleb–Olver–Slevinsky, polynomial measure conversion.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace Polynomial
variable {D : Set ℝ}

/-- Shifting by the squared scale commutes with an outer polynomial modification. -/
theorem koornwinderOuterMeasure_withDensity (μ : Measure D) (a u : ℝ[X]) (k : ℕ)
    (_ha : ∀ᵐ x : D ∂μ, 0 ≤ a.eval (x : ℝ)) :
    koornwinderOuterMeasure a k ((Measure.map Subtype.val (Polynomial.subtypeDensityMeasure (u) ((μ).comap Subtype.val))).comap Subtype.val) =
      Polynomial.polynomialDensityMeasure (u) (((koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val))).comap Subtype.val) := by
  rw [map_subtypeDensityMeasure_comap]
  exact polynomialDensityMeasure_comap_comm (a^k) u (μ.map Subtype.val)

end Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}

/-- The normalized Type 1 target keeps the original inner sequence and lifts. -/
noncomputable def outerModification (S : KoornwinderSystem a ρ μ ν)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (ha0 : a ≠ 0) (ha : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ))
    (u : ℝ[X]) (hu0 : u ≠ 0) (hu : ∀ᵐ (x : D) ∂μ, 0 ≤ u.eval (x : ℝ)) :
    KoornwinderSystem a ρ (Polynomial.subtypeDensityMeasure u (μ.comap Subtype.val)) ν := by
  exact koornwinderSystemOfLift a ρ _ ν (hμ.map_subtype_withDensity u hu)
    (hpos.map_subtype_withDensity hμ u hu0 hu) ha0
    ((subtypeDensityMeasure_comap_absolutelyContinuous u μ).ae_le ha)
    S.inner S.inner_orthogonal S.inner_leadingCoeff_pos S.inner_norm S.lift
    (fun k => (subtypeDensityMeasure_comap_absolutelyContinuous u μ).ae_le (S.lift_eval k))

/-- Keeping the inner sequence eliminates every cross-inner-index entry. -/
theorem connectionEntry_eq_zero_of_same_inner
    (S : KoornwinderSystem a ρ μ ν) {μ' : Measure D}
    (T : KoornwinderSystem a ρ μ' ν) [SFinite μ'] [SFinite ν]
    (hρ : Continuous ρ) (hμ' : μ' ≪ μ) (hinner : S.inner=T.inner)
    {n k m j : ℕ} (hkj : k ≠ j)
    (hi : Integrable (fun x => eval x (S.polynomial n k)*eval x (T.polynomial m j))
      (koornwinderMeasure ρ μ' ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : S.connectionEntry T n k m j = 0 := by
  rw [S.connectionEntry_eq T hρ hμ' n k m j (hi := hi)]
  have hz := S.inner_orthogonal.orthogonal k j hkj
  simp only [Polynomial.integralInner] at hz ⊢
  rw [← hinner, hz, mul_zero]

/-- Type 1 support is bounded in the outer label and diagonal in the inner label. -/
theorem connectionEntry_eq_zero_of_outer_modification
    (S : KoornwinderSystem a ρ μ ν) (u : ℝ[X])
    (T : KoornwinderSystem a ρ (Polynomial.subtypeDensityMeasure (u) ((μ).comap Subtype.val)) ν)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (hu : ∀ᵐ (x : D) ∂μ, 0 ≤ u.eval (x : ℝ)) (hinner : S.inner=T.inner)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : k ≠ j ∨ n < m ∨ m+u.natDegree < n) :
    S.connectionEntry T n k m j
      (hi := (T.hasFiniteMoments hρ ((subtypeDensityMeasure_comap_absolutelyContinuous u μ).ae_le ha)).integrable_mul _ _) = 0 := by
  let := (hμ.map_subtype_withDensity u hu).isFiniteMeasure_subtype
  let := hν.isFiniteMeasure
  have hM := T.hasFiniteMoments hρ ((subtypeDensityMeasure_comap_absolutelyContinuous u μ).ae_le ha)
  rcases hout with hkj | hout
  · exact S.connectionEntry_eq_zero_of_same_inner T hρ
      (subtypeDensityMeasure_comap_absolutelyContinuous u μ) hinner hkj (hi := hM.integrable_mul _ _)
  by_cases hkj : k=j
  · subst j
    rw [S.connectionEntry_same_inner T hρ (subtypeDensityMeasure_comap_absolutelyContinuous u μ)
      ((subtypeDensityMeasure_comap_absolutelyContinuous u μ).ae_le ha)]
    have hm := hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x)))) k
    have hn : ∀ᵐ x ∂koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val), 0 ≤ u.eval (x : ℝ) := by
      exact (polynomialDensityMeasure_comap_absolutelyContinuous (a^k)
        (μ.map Subtype.val)).ae_le (ae_nonneg_eval_map_subtype hu)
    have hT := T.outer_orthogonal k
    rw [koornwinderOuterMeasure_withDensity μ a u k S.scale_nonneg] at hT
    have hz := (S.outer_orthogonal k).integralInner_eq_zero_of_polynomial_modification hm u hn hT
      (by omega : n-k < m-k ∨ m-k+u.natDegree < n-k)
    simp only [Polynomial.integralInner] at hz ⊢
    rw [koornwinderOuterMeasure_withDensity μ a u k S.scale_nonneg, hz, zero_mul]
  · exact S.connectionEntry_eq_zero_of_same_inner T hρ
      (subtypeDensityMeasure_comap_absolutelyContinuous u μ) hinner hkj (hi := hM.integrable_mul _ _)

end MvPolynomial.KoornwinderSystem
