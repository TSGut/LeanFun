/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Conversion
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.IntegrationByParts

/-! # Differentiation weighted at the external semiclassical singularity
The map (t-x)p'-(gamma+1)p goes from (a,b,gamma+1) to (a+1,b+1,gamma).
This is the second first-order factor of the annular Laplacian.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Sections 3.4 and 4.1.
-/

@[expose] public section
open MeasureTheory
namespace Polynomial

/-- Parameter shifts transport polynomial pairings exactly. -/
theorem integralInner_semiclassicalJacobi_shift {t α β γ : ℝ} (ht : 1<t)
    (a b c : ℕ) (p q : ℝ[X])
    (hi : Integrable (fun x => p.eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+a) (β+b) (γ+c)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => (semiclassicalJacobiShiftDensity t a b c*p).eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+a) (β+b) (γ+c)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+a) (β+b) (γ+c)) p q) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (semiclassicalJacobiShiftDensity t a b c*p) q) := by
  simp only [integralInner]
  have he := (integral_semiclassicalJacobi_shift_integrable ht α β γ a b c ⟨_, hi⟩).2
  simpa only [eval_mul, mul_assoc] using he

/-- Raising only the external parameter inserts the linear factor t-x. -/
theorem integralInner_semiclassicalJacobi_gamma_add_one {t α β γ : ℝ} (ht : 1<t)
    (p q : ℝ[X])
    (hi : Integrable (fun x => p.eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => ((C t-X)*p).eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) p q) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) ((C t-X)*p) q) := by
  simpa only [integralInner, semiclassicalJacobiShiftDensity, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, one_mul, mul_one, add_zero, mul_comm, mul_left_comm, mul_assoc] using
    integralInner_semiclassicalJacobi_shift (α := α) (β := β) (γ := γ) ht 0 0 1 p q
      (hi := by simpa using hi)
      (hj := by simpa [semiclassicalJacobiShiftDensity, mul_comm, mul_left_comm, mul_assoc] using hj)

/-- Raising the two endpoint parameters inserts x(1-x). -/
theorem integralInner_semiclassicalJacobi_ab_add_one {t α β γ : ℝ} (ht : 1<t)
    (p q : ℝ[X])
    (hi : Integrable (fun x => p.eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => (X*(1-X)*p).eval x*q.eval x) (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) p q) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (X*(1-X)*p) q) := by
  simpa only [integralInner, semiclassicalJacobiShiftDensity, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, one_mul, mul_one, add_zero, mul_comm, mul_left_comm, mul_assoc] using
    integralInner_semiclassicalJacobi_shift (α := α) (β := β) (γ := γ) ht 1 1 0 p q
      (hi := by simpa using hi)
      (hj := by simpa [semiclassicalJacobiShiftDensity, mul_comm, mul_left_comm, mul_assoc] using hj)

/-- The polynomial action of differentiation weighted at the third singularity. -/
noncomputable def semiclassicalJacobiCWeightedDerivativeMap (t γ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (C t-X)).comp derivative - LinearMap.mulLeft ℝ (C (γ+1))

/-- Partial weighted differentiation has a quadratic/linear polynomial adjoint. -/
theorem integralInner_semiclassicalJacobi_cWeightedDerivative {t α β γ : ℝ}
    (ht : 1<t) (hα : -1<α) (hβ : -1<β) (p q : ℝ[X]) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (semiclassicalJacobiCWeightedDerivativeMap t γ p) q (h := (hasFiniteMoments_semiclassicalJacobiMeasure ht (by linarith) (by linarith)).integrable_mul _ _)) =
      -integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) p (X*(1-X)*q.derivative+(C (α+1)*(1-X)-C (β+1)*X)*q)) := by
  have hM := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht hα hβ
  have hT := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
    (show -1<α+1 by linarith) (show -1<β+1 by linarith)
  change integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (hT.pair ((C t-X)*p.derivative-C (γ+1)*p) q) = _
  have hMg := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ+1) ht hα hβ
  have hTg := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ+1) ht
    (show -1<α+1 by linarith) (show -1<β+1 by linarith)
  rw [integralInner_sub_left hT,
    ← integralInner_semiclassicalJacobi_gamma_add_one (α := α+1) (β := β+1) (γ := γ)
      ht p.derivative q (hi := hTg.integrable_mul _ _) (hj := hT.integrable_mul _ _),
    integralInner_semiclassicalJacobi_derivative ht hα hβ,
    integralInner_semiclassicalJacobi_ab_add_one (α := α) (β := β) (γ := γ)
      ht (C (γ+1)*p) q (hi := hT.integrable_mul _ _) (hj := hM.integrable_mul _ _),
    integralInner_semiclassicalJacobi_gamma_add_one (α := α) (β := β) (γ := γ)
      ht p _ (hi := hMg.integrable_mul _ _) (hj := hM.integrable_mul _ _)]
  have he : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) p (semiclassicalJacobiSigma t*q.derivative+semiclassicalJacobiTau t α β γ*q) (h := hM.integrable_mul _ _)) +
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (X*(1-X)*(C (γ+1)*p)) q (h := hM.integrable_mul _ _)) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) ((C t-X)*p) (X*(1-X)*q.derivative+(C (α+1)*(1-X)-C (β+1)*X)*q) (h := hM.integrable_mul _ _)) := by
    rw [integralInner, integralInner, integralInner, ← integral_add
      (hM.integrable_mul p _) (hM.integrable_mul _ q)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_one,
      semiclassicalJacobiSigma, semiclassicalJacobiTau]
    ring
  linarith

end Polynomial
