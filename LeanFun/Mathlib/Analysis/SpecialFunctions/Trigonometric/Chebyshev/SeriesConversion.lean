/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCoefficientMap
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.UltrasphericalLadder

/-! # Convergent ultraspherical basis conversion
The existing real bases and conversion matrices also act on complex series.
Weighted absolute convergence justifies reconstruction; banded rows need only
finitely many input coefficients. Reference: Olver--Townsend (2013), Section 2.
-/

public section
namespace Polynomial

/-- Raising levels computes each certified output coefficient from a finite window. -/
theorem ultraspherical_series_conversion_eq_sum {k N : ℕ} (hk : k ≤ N)
    (a : ℕ → ℂ) (i : ℕ) :
    (ultrasphericalBasis k).seriesCoefficientMap (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom (.ofBanded _ _ _ _ a
        (ultrasphericalBasis_conversion_isBanded hk) i) =
      ∑ j ∈ Finset.range (i + 2 * (N - k) + 1),
        a j * ((ultrasphericalBasis N).repr (ultrasphericalBasis k j) i : ℂ) :=
  (ultrasphericalBasis k).seriesCoefficientMap_eq_sum_of_isBanded
    (ultrasphericalBasis N) LinearMap.id Complex.ofRealHom a
    (ultrasphericalBasis_conversion_isBanded hk) i

/-- Weighted reconstruction holds in either direction, including zero modes. -/
theorem hasSum_ultraspherical_series_conversion (k N : ℕ) (a : ℕ → ℂ) (z : ℂ)
    (w : ℕ → ℝ)
    (hw : ∀ i, ‖(ultrasphericalBasis N i).eval₂ Complex.ofRealHom z‖ ≤ w i)
    (ha : Summable (fun j ↦ ‖a j‖ *
      ∑ i ∈ ((ultrasphericalBasis N).repr (ultrasphericalBasis k j)).support,
        ‖(((ultrasphericalBasis N).repr (ultrasphericalBasis k j)) i : ℂ)‖ * w i)) :
    HasSum (fun i ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm
      ((ultrasphericalBasis k).summable_norm_seriesCoefficientMap_terms (ultrasphericalBasis N)
        LinearMap.id Complex.ofRealHom a z w hw ha) Prod.snd i))
      (∑' j, a j * (ultrasphericalBasis k j).eval₂ Complex.ofRealHom z) :=
  (ultrasphericalBasis k).hasSum_seriesCoefficientMap (ultrasphericalBasis N)
    LinearMap.id Complex.ofRealHom a z
    ((ultrasphericalBasis k).summable_norm_seriesCoefficientMap_terms (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom a z w hw ha)

/-- With convergent coefficient rows the weighted reconstruction factors into
coefficients times basis modes, for either direction of conversion. -/
theorem hasSum_ultraspherical_series_conversion_of_rows (k N : ℕ) (a : ℕ → ℂ) (z : ℂ)
    (w : ℕ → ℝ)
    (hw : ∀ i, ‖(ultrasphericalBasis N i).eval₂ Complex.ofRealHom z‖ ≤ w i)
    (ha : Summable (fun j ↦ ‖a j‖ *
      ∑ i ∈ ((ultrasphericalBasis N).repr (ultrasphericalBasis k j)).support,
        ‖(((ultrasphericalBasis N).repr (ultrasphericalBasis k j)) i : ℂ)‖ * w i))
    (rows : ∀ i, (ultrasphericalBasis k).SeriesCoefficientInput (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom i) (hrows : ∀ i, (rows i).val = a) :
    HasSum (fun i ↦ (ultrasphericalBasis k).seriesCoefficientMap (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom (rows i) * (ultrasphericalBasis N i).eval₂ Complex.ofRealHom z)
      (∑' j, a j * (ultrasphericalBasis k j).eval₂ Complex.ofRealHom z) :=
  (ultrasphericalBasis k).hasSum_seriesCoefficientMap_of_rows (ultrasphericalBasis N)
    LinearMap.id Complex.ofRealHom a z
    ((ultrasphericalBasis k).summable_norm_seriesCoefficientMap_terms (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom a z w hw ha) rows hrows

/-- Raising levels supplies convergent rows automatically by bandedness. -/
theorem hasSum_ultraspherical_series_conversion_of_le {k N : ℕ} (hk : k ≤ N)
    (a : ℕ → ℂ) (z : ℂ) (w : ℕ → ℝ)
    (hw : ∀ i, ‖(ultrasphericalBasis N i).eval₂ Complex.ofRealHom z‖ ≤ w i)
    (ha : Summable (fun j ↦ ‖a j‖ *
      ∑ i ∈ ((ultrasphericalBasis N).repr (ultrasphericalBasis k j)).support,
        ‖(((ultrasphericalBasis N).repr (ultrasphericalBasis k j)) i : ℂ)‖ * w i)) :
    HasSum (fun i ↦ (ultrasphericalBasis k).seriesCoefficientMap (ultrasphericalBasis N)
      LinearMap.id Complex.ofRealHom (.ofBanded _ _ _ _ a
        (ultrasphericalBasis_conversion_isBanded hk) i) *
      (ultrasphericalBasis N i).eval₂ Complex.ofRealHom z)
      (∑' j, a j * (ultrasphericalBasis k j).eval₂ Complex.ofRealHom z) :=
  hasSum_ultraspherical_series_conversion_of_rows k N a z w hw ha _ (fun _ ↦ rfl)

end Polynomial
