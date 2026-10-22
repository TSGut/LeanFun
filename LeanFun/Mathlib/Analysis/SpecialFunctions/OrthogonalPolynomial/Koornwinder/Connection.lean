/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

import Mathlib.Topology.Algebra.Polynomial

/-!
# Mixed pairings for separated measure changes

Source lift identities transfer by absolute continuity of the modified outer
measure. Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, Lemma 2.8.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}

/-- Source coefficients against a normalized target separated system. -/
noncomputable def connectionEntry (S : KoornwinderSystem a ρ μ ν)
    (T : KoornwinderSystem a ρ μ' ν') (n k m j : ℕ)
    (input : KoornwinderMeasureInput ρ μ' ν' := by
      first
        | assumption
        | exact KoornwinderMeasureInput.ofContinuous _ _ (by fun_prop)
        | (apply KoornwinderMeasureInput.ofMoments
           · aesop (rule_sets := [PolynomialIntegrability])
           · fun_prop))
    (hi : Integrable (fun v => eval v (S.polynomial n k)*eval v (T.polynomial m j))
      (koornwinderMeasure ρ μ' ν') := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : ℝ :=
  integralInner (koornwinderMeasure ρ μ' ν') (IntegrablePair.of (koornwinderMeasure ρ μ' ν') (S.polynomial n k) (T.polynomial m j))

/-- Modified mixed pairings split into outer and inner factors. -/
theorem connectionEntry_eq (S : KoornwinderSystem a ρ μ ν)
    (T : KoornwinderSystem a ρ μ' ν') [SFinite μ'] [SFinite ν']
    (hρ : Continuous ρ) (hμ' : μ' ≪ μ) (n k m j : ℕ)
    (hi : Integrable (fun v => eval v (S.polynomial n k)*eval v (T.polynomial m j))
      (koornwinderMeasure ρ μ' ν') := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    S.connectionEntry T n k m j =
      (∫ x, (S.outer k (n-k)).eval (x : ℝ) * (T.outer j (m-j)).eval (x : ℝ) * ρ x^(k+j) ∂μ') *
        Polynomial.integralInner ν' (Polynomial.IntegrablePair.of ν' (S.inner k) (T.inner j)) := by
  have he := (koornwinderMeasure_integral
    (KoornwinderMeasureInput.ofContinuous μ' ν' hρ)
    ⟨fun v ↦ eval v (S.polynomial n k*T.polynomial m j), by simpa only [map_mul] using hi⟩).2
  simp only [map_mul] at he
  rw [connectionEntry, integralInner, he, Polynomial.integralInner, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hμ'.ae_le (S.eval_polynomial n k)),
    Measure.quasiMeasurePreserving_fst.ae (T.eval_polynomial m j)] with v hv hw
  rw [hv v.2, hw v.2, pow_add]
  ring

/-- Equal inner labels give the usual shifted outer pairing. -/
theorem connectionEntry_same_inner (S : KoornwinderSystem a ρ μ ν)
    (T : KoornwinderSystem a ρ μ' ν') [SFinite μ'] [SFinite ν']
    (hρ : Continuous ρ) (hμ' : μ' ≪ μ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (n m k : ℕ) :
    S.connectionEntry T n k m k =
      Polynomial.integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ').comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ').comap Subtype.val)) (S.outer k (n-k)) (T.outer k (m-k))) *
        Polynomial.integralInner ν' (Polynomial.IntegrablePair.of ν' (S.inner k) (T.inner k)) := by
  rw [S.connectionEntry_eq T hρ hμ' n k m k
    (hi := (T.hasFiniteMoments hρ ha).integrable_mul _ _)]
  congr 1
  rw [Polynomial.integralInner, integral_koornwinderOuterMeasure (Measure.map Subtype.val μ') a
    ((ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const a.continuous.measurable)).mpr
        (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x)))) k
    ⟨fun x => (S.outer k (n-k)).eval x*(T.outer k (m-k)).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩]
  dsimp only
  have he := integral_map (μ := μ') measurable_subtype_coe.aemeasurable
    (((a.continuous.pow k).mul
      ((S.outer k (n-k)).continuous.mul (T.outer k (m-k)).continuous)).aestronglyMeasurable)
  simp only [Pi.mul_apply, Pi.pow_apply] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [show k+k=2*k by omega, pow_mul, hx]
  ring

/-- Positive leading orientations make every same-label connection entry positive. -/
theorem connectionEntry_diag_pos (S : KoornwinderSystem a ρ μ ν)
    (T : KoornwinderSystem a ρ μ' ν')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hρ : Continuous ρ) (habs : μ' ≪ μ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (n k : ℕ) : 0 < S.connectionEntry T n k n k := by
  let := hμ'.isFiniteMeasure_subtype
  let := hν'.isFiniteMeasure
  rw [S.connectionEntry_same_inner T hρ habs ha]
  apply mul_pos
  · exact (T.outer_orthogonal k).integralInner_pos_of_leadingCoeff_pos
      (hμ'.koornwinderOuterMeasure a ((ae_map_iff measurable_subtype_coe.aemeasurable
        (measurableSet_le measurable_const a.continuous.measurable)).mpr
          (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x)))) k)
      ((S.outer k).natDegree_eq _) (S.outer_leadingCoeff_pos k (n-k))
      (T.outer_leadingCoeff_pos k (n-k)) (by rw [T.outer_norm]; exact zero_lt_one)
  · exact T.inner_orthogonal.integralInner_pos_of_leadingCoeff_pos hν'
      (S.inner.natDegree_eq k) (S.inner_leadingCoeff_pos k) (T.inner_leadingCoeff_pos k)
      (by rw [T.inner_norm]; exact zero_lt_one)

end MvPolynomial.KoornwinderSystem
