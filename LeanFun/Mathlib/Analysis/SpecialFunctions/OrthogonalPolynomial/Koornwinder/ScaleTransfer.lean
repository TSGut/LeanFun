/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Connection

import Mathlib.Topology.Algebra.Polynomial

/-!
# Radius powers in separated measure conversion

A single calculation covers polynomial scales and square-root scales.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, measure conversion.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}

/-- A compatible inner-degree gap moves a polynomial radius power into the outer pairing. -/
theorem connectionEntry_of_scale_gap
    {a b : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    [SFinite μ'] [SFinite ν'] (hρ : Continuous ρ) (hμ' : μ' ≪ μ)
    (ha : ∀ᵐ (x : D) ∂μ', ρ x^2 = a.eval (x : ℝ)) (step : ℕ)
    (hb : ∀ᵐ (x : D) ∂μ', ρ x^step = b.eval (x : ℝ))
    (n k m j r : ℕ) (hkj : k=j+step*r) :
    S.connectionEntry T n k m j =
      Polynomial.integralInner (koornwinderOuterMeasure a j ((Measure.map Subtype.val μ').comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a j ((Measure.map Subtype.val μ').comap Subtype.val)) (b^r*S.outer k (n-k)) (T.outer j (m-j))) *
        Polynomial.integralInner ν' (Polynomial.IntegrablePair.of ν' (S.inner k) (T.inner j)) := by
  rw [S.connectionEntry_eq T hρ hμ']
  congr 1
  rw [Polynomial.integralInner, integral_koornwinderOuterMeasure_map_subtype μ' a
    (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))) j ⟨fun x => (b^r*S.outer k (n-k)).eval x*(T.outer j (m-j)).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩]
  dsimp only
  apply integral_congr_ae
  filter_upwards [ha,hb] with x hx hy
  simp only [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [← hx, ← hy, ← pow_mul, ← pow_mul, show k+j=2*j+step*r by omega, pow_add]
  ring

end MvPolynomial.KoornwinderSystem
namespace Polynomial
variable {D : Set ℝ}

/-- Transfer the shifted outer pairing to the original outer measure. -/
theorem integralInner_koornwinder_modification_transfer {μ : Measure D}
    (a b h : ℝ[X]) (ρ : D → ℝ)
    (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (step : ℕ) (hb : ∀ᵐ (x : D) ∂μ, ρ x^step = b.eval (x : ℝ))
    (hbpos : ∀ᵐ (x : D) ∂μ, 0 ≤ b.eval (x : ℝ)) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ))
    (p q : ℝ[X]) (l j k r : ℕ) (hr : r ≤ l) (hkj : k=j+step*r)
    (hi : Integrable (fun x => (b^r*p).eval (x : ℝ)*q.eval (x : ℝ))
      (koornwinderOuterMeasure a j ((Measure.map Subtype.val (Polynomial.subtypeDensityMeasure ((b^l*h)) ((μ).comap Subtype.val))).comap Subtype.val)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => p.eval (x : ℝ)*(b^(l-r)*h*q).eval (x : ℝ))
      (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (koornwinderOuterMeasure a j ((Measure.map Subtype.val (Polynomial.subtypeDensityMeasure ((b^l*h)) ((μ).comap Subtype.val))).comap Subtype.val)) (IntegrablePair.of (koornwinderOuterMeasure a j ((Measure.map Subtype.val (Polynomial.subtypeDensityMeasure ((b^l*h)) ((μ).comap Subtype.val))).comap Subtype.val)) (b^r*p) q) =
      integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) p (b^(l-r)*h*q)) := by
  have hapos : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ) := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
  have hu : ∀ᵐ (x : D) ∂μ, 0 ≤ (b^l*h).eval (x : ℝ) := by
    filter_upwards [hbpos,hh] with x hx hy
    simpa only [eval_mul,eval_pow] using mul_nonneg (pow_nonneg hx _) hy
  obtain ⟨w, hw, hwval, _, hwmeasure⟩ :=
    exists_subtypeDensityMeasure_extension (D := D) (b^l*h)
  simp only [integralInner]
  rw [integral_koornwinderOuterMeasure_map_subtype _ a
      ((subtypeDensityMeasure_comap_absolutelyContinuous (b^l*h) μ).ae_le hapos)
      j ⟨_, hi⟩,
    integral_koornwinderOuterMeasure_map_subtype μ a hapos k ⟨_, hj⟩]
  dsimp only
  rw [hwmeasure, integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integral_congr_ae
  filter_upwards [ha,hb,hu] with x hx hy hux
  rw [hwval x hux]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, eval_mul,eval_pow]
  rw [← hx, ← hy]
  have he : step*l+2*j+step*r = 2*k+step*(l-r) := by
    have ht : step*(l-r)+step*r=step*l := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hr]
    rw [hkj]
    nlinarith
  simp only [← pow_mul]
  calc
    _ = ρ x^(step*l+2*j+step*r) * (h.eval (x : ℝ)*p.eval (x : ℝ)*q.eval (x : ℝ)) := by
      simp only [pow_add]
      ring
    _ = ρ x^(2*k+step*(l-r)) * (h.eval (x : ℝ)*p.eval (x : ℝ)*q.eval (x : ℝ)) := by rw [he]
    _ = _ := by simp only [pow_add]; ring

end Polynomial
