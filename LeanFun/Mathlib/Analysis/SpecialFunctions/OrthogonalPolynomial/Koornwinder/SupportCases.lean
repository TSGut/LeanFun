/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Support
public import LeanFun.Mathlib.MeasureTheory.Measure.EvenDensity
import Mathlib.Topology.Algebra.Polynomial

/-!
# Support bounds in both ordinary Koornwinder cases

Separated polynomial modifications admit degree-independent containing support
sets. The single Type 2 factors are the cases l=1 and h=1.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, polynomial modifications.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}

/-- Affine scales give a finite rectangular support, without an inner parity assumption. -/
theorem connectionEntry_affine_support {μ : Measure D} {ν : Measure ℝ} (c h g : ℝ[X]) (l : ℕ)
    (S : KoornwinderSystem (c^2) (fun x => c.eval (x : ℝ)) μ ν)
    (T : KoornwinderSystem (c^2) (fun x => c.eval (x : ℝ))
      (Polynomial.subtypeDensityMeasure ((c^l*h)) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hc : ∀ᵐ (x : D) ∂μ, 0 ≤ c.eval (x : ℝ)) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ))
    (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval (x : ℝ)) (hcdeg : c.natDegree ≤ 1) (hgdeg : g.natDegree ≤ l)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : ¬ ∃ s r : ℕ, s ≤ h.natDegree+l ∧ r ≤ l ∧ n=m+s ∧ k=j+r) :
    S.connectionEntry T n k m j = 0 := by
  have ha : ∀ᵐ (x : D) ∂μ, c.eval (x : ℝ)^2 = (c^2).eval (x : ℝ) := by simp
  have hb : ∀ᵐ (x : D) ∂μ, c.eval (x : ℝ)^1 = c.eval (x : ℝ) := by simp
  by_cases hi : k < j ∨ j+g.natDegree < k
  · exact S.connectionEntry_eq_zero_of_inner_modification h g l T hμ hν (c.continuous.comp continuous_subtype_val) hc hh hg hi
  have hkj : k=j+1*(k-j) := by omega
  have hr : k-j ≤ l := by omega
  by_cases ho : n < m ∨ m+h.natDegree+l < n
  · exact S.connectionEntry_eq_zero_of_outer_band h g l T hμ hν (c.continuous.comp continuous_subtype_val) ha 1 hb hc hh hg
      hcdeg hk hj hkj hr (by simpa using ho)
  exfalso
  apply hout
  exact ⟨n-m,k-j,by omega,hr,by omega,by omega⟩

/-- Quadratic squared scales give even inner steps and bounded total-degree steps. -/
theorem connectionEntry_quadratic_support {μ : Measure D} {ν : Measure ℝ} [ν.IsNegInvariant]
    (a h g : ℝ[X]) (l : ℕ) {ρ : D → ℝ}
    (S : KoornwinderSystem a ρ μ ν)
    (T : KoornwinderSystem a ρ
      (Polynomial.subtypeDensityMeasure ((a^l*h)) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hνpos : Polynomial.HasPositiveDefiniteIntegral ν) (hg0 : g ≠ 0)
    (hρ : Continuous ρ) (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ)) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval (x : ℝ))
    (hgpar : ∀ x, g.eval (-x) = g.eval (x : ℝ)) (hadeg : a.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2*l) {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : ¬ ∃ s r : ℕ, s ≤ h.natDegree+2*l ∧ r ≤ l ∧ n=m+s ∧ k=j+2*r) :
    S.connectionEntry T n k m j (hi :=
      (T.hasFiniteMoments hρ
        ((subtypeDensityMeasure_comap_absolutelyContinuous (a^l*h) μ).ae_le ha)).integrable_mul _ _) = 0 := by
  have hMt := T.hasFiniteMoments hρ
    ((subtypeDensityMeasure_comap_absolutelyContinuous (a^l*h) μ).ae_le ha)
  have hapos := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
  by_cases hi : k < j ∨ j+g.natDegree < k
  · exact S.connectionEntry_eq_zero_of_inner_modification h g l T hμ hν hρ hapos hh hg hi
      (hi := hMt.integrable_mul _ _)
  by_cases hp : k % 2 ≠ j % 2
  · have hu : ∀ᵐ (x : D) ∂μ, 0 ≤ (a^l*h).eval (x : ℝ) := by
      filter_upwards [hapos,hh] with x hx hy
      simpa only [Polynomial.eval_mul,Polynomial.eval_pow] using mul_nonneg (pow_nonneg hx l) hy
    let := (hμ.map_subtype_withDensity (a^l*h) hu).isFiniteMeasure_subtype
    let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
    let := isNegInvariant_polynomialDensityMeasure_comap g ν hgpar
    rw [S.connectionEntry_eq T hρ (subtypeDensityMeasure_comap_absolutelyContinuous (a^l*h) μ)
      n k m j (hi := hMt.integrable_mul _ _),
      integralInner_eq_zero_of_opposite_parity
        (S.inner_orthogonal.comp_neg_X hν hνpos k)
        (T.inner_orthogonal.comp_neg_X (hν.polynomialDensityMeasure g hg)
          (hνpos.polynomialDensityMeasure hν g hg0 hg) j) hp, mul_zero]
  have hkj : k=j+2*((k-j)/2) := by omega
  have hr : (k-j)/2 ≤ l := by omega
  by_cases ho : n < m ∨ m+h.natDegree+2*l < n
  · exact S.connectionEntry_eq_zero_of_outer_band h g l T hμ hν hρ ha 2 ha hapos hh hg
      hadeg hk hj hkj hr ho
  exfalso
  apply hout
  exact ⟨n-m,(k-j)/2,by omega,hr,by omega,hkj⟩

end MvPolynomial.KoornwinderSystem
