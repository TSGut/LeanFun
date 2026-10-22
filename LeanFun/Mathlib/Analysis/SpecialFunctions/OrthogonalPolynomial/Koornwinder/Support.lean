/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.ScaleTransfer

/-!
# Outer bandwidth for compatible separated modifications

The scale-power calculation covers both ordinary Koornwinder cases, without
classical formulas for either one-dimensional family.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, polynomial modifications.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a b : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (h g : ℝ[X]) (l : ℕ)
    (T : KoornwinderSystem a ρ
      (Polynomial.subtypeDensityMeasure ((b^l*h)) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (step : ℕ) (hb : ∀ᵐ (x : D) ∂μ, ρ x^step = b.eval (x : ℝ))
    (hbpos : ∀ᵐ (x : D) ∂μ, 0 ≤ b.eval (x : ℝ)) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ))
    (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval (x : ℝ))

include hμ hν hρ hbpos hh hg

/-- Inner orthogonality bounds the inner connection bandwidth. -/
theorem connectionEntry_eq_zero_of_inner_modification {n k m j : ℕ}
    (hout : k < j ∨ j+g.natDegree < k)
    (hi : Integrable (fun x => eval x (S.polynomial n k)*eval x (T.polynomial m j))
      (koornwinderMeasure ρ (Polynomial.subtypeDensityMeasure ((b^l*h)) ((μ).comap Subtype.val))
        (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : S.connectionEntry T n k m j = 0 := by
  have hu : ∀ᵐ (x : D) ∂μ, 0 ≤ (b^l*h).eval (x : ℝ) := by
    filter_upwards [hbpos,hh] with x hx hy
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow] using mul_nonneg (pow_nonneg hx _) hy
  let := (hμ.map_subtype_withDensity (b^l*h) hu).isFiniteMeasure_subtype
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  rw [S.connectionEntry_eq T hρ (subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ) n k m j (hi := hi),
    S.inner_orthogonal.integralInner_eq_zero_of_polynomial_modification hν g hg
      T.inner_orthogonal hout, mul_zero]

include ha hb

/-- Degree-compatible scales give an outer bandwidth independent of truncation. -/
theorem connectionEntry_eq_zero_of_outer_band
    (hdegree : b.natDegree ≤ step) {n k m j r : ℕ}
    (hk : k ≤ n) (hj : j ≤ m) (hkj : k=j+step*r) (hr : r ≤ l)
    (hout : n < m ∨ m+h.natDegree+step*l < n) :
    S.connectionEntry T n k m j (hi :=
      (T.hasFiniteMoments hρ
        ((subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ).ae_le ha)).integrable_mul _ _) = 0 := by
  have hu : ∀ᵐ (x : D) ∂μ, 0 ≤ (b^l*h).eval (x : ℝ) := by
    filter_upwards [hbpos,hh] with x hx hy
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow] using mul_nonneg (pow_nonneg hx _) hy
  have hapos := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
  have hμ' := hμ.map_subtype_withDensity (b^l*h) hu
  let := hμ'.isFiniteMeasure_subtype
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  rw [S.connectionEntry_of_scale_gap T hρ (subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ)
    ((subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ).ae_le ha) step
    ((subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ).ae_le hb) n k m j r hkj]
  have hd (t : ℕ) : (b^t).natDegree ≤ step*t := by
    rw [natDegree_pow]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left t hdegree
  rcases hout with hout | hout
  · have hp : (b^r*S.outer k (n-k)).natDegree < m-j := by
      have ht := natDegree_mul_le (p := b^r) (q := S.outer k (n-k))
      rw [Sequence.natDegree_eq] at ht
      have := hd r
      omega
    rw [(T.outer_orthogonal j).integralInner_eq_zero_of_degree_lt
      (hμ'.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype ((subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ).ae_le hapos)) j)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hp)), zero_mul]
  · rw [integralInner_koornwinder_modification_transfer a b h ρ ha step hb hbpos hh
      _ _ l j k r hr hkj
      (hi := (T.outer_orthogonal j).hasFiniteMoments.integrable_mul _ _)
      (hj := (S.outer_orthogonal k).hasFiniteMoments.integrable_mul _ _), Polynomial.integralInner_comm]
    have hp : (b^(l-r)*h*T.outer j (m-j)).natDegree < n-k := by
      have ht := natDegree_mul_le (p := b^(l-r)*h) (q := T.outer j (m-j))
      have hs := natDegree_mul_le (p := b^(l-r)) (q := h)
      rw [Sequence.natDegree_eq] at ht
      have := hd (l-r)
      have he : step*(l-r)+step*r=step*l := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hr]
      omega
    rw [(S.outer_orthogonal k).integralInner_eq_zero_of_degree_lt
      (hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype hapos) k)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hp)), zero_mul]

end MvPolynomial.KoornwinderSystem
