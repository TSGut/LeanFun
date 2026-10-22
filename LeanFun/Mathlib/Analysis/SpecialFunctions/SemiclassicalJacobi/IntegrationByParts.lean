/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Pearson
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.MeasureModification

/-! # Polynomial integration by parts for the semiclassical hierarchy
The Pearson identity gives the derivative adjoint between the original and
simultaneously raised measures, throughout the integrable parameter range.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

public section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Simultaneously raising all parameters multiplies polynomial pairings by the cubic sigma. -/
theorem integralInner_semiclassicalJacobi_add_one {t α β γ : ℝ}
    (ht : 1 < t) (p q : ℝ[X])
    (hi : Integrable (fun x => (semiclassicalJacobiSigma t*p).eval x * q.eval x)
      (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) p q (h := by
        rw [integrable_semiclassicalJacobiMeasure_iff] at hi ⊢
        convert hi using 1
        funext x
        rw [semiclassicalJacobiWeight_add_one]
        simp only [semiclassicalJacobiSigma, eval_mul, eval_sub, eval_X, eval_one, eval_C]
        ring)) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (semiclassicalJacobiSigma t*p) q) := by
  have hpq : Integrable (fun x ↦ p.eval x * q.eval x)
      (semiclassicalJacobiMeasure ⟨t, ht⟩ (α+1) (β+1) (γ+1)) := by
    rw [integrable_semiclassicalJacobiMeasure_iff] at hi ⊢
    convert hi using 1
    funext x
    rw [semiclassicalJacobiWeight_add_one]
    simp only [semiclassicalJacobiSigma, eval_mul, eval_sub, eval_X, eval_one, eval_C]
    ring
  simp only [integralInner]
  erw [integral_semiclassicalJacobiMeasure ⟨t, ht⟩ (α+1) (β+1) (γ+1) ⟨_, hpq⟩,
    integral_semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ ⟨_, hi⟩]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [semiclassicalJacobiWeight_add_one]
  simp only [semiclassicalJacobiSigma, eval_mul, eval_sub, eval_X, eval_one, eval_C]
  ring

/-- Derivative adjoint identity with the shifted measure, with endpoint terms already discharged. -/
theorem integralInner_semiclassicalJacobi_derivative {t α β γ : ℝ}
    (ht : 1 < t) (hα : -1 < α) (hβ : -1 < β) (p q : ℝ[X]) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) p.derivative q (h :=
        (hasFiniteMoments_semiclassicalJacobiMeasure ht (by linarith) (by linarith)).integrable_mul _ _)) =
      - integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) p (semiclassicalJacobiSigma t*q.derivative + semiclassicalJacobiTau t α β γ*q)) := by
  have hM := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht hα hβ
  have he := integral_semiclassicalJacobi_pearson (γ := γ) ht hα hβ (p*q)
  have hp : semiclassicalJacobiSigma t*(p*q).derivative + semiclassicalJacobiTau t α β γ*(p*q) =
      (semiclassicalJacobiSigma t*p.derivative)*q +
        p*(semiclassicalJacobiSigma t*q.derivative + semiclassicalJacobiTau t α β γ*q) := by
    rw [derivative_mul]
    ring
  rw [hp] at he
  simp only [eval_add, eval_mul] at he
  have ha := integral_add (hM.integrable_mul (semiclassicalJacobiSigma t*p.derivative) q)
    (hM.integrable_mul p (semiclassicalJacobiSigma t*q.derivative + semiclassicalJacobiTau t α β γ*q))
  simp only [eval_add, eval_mul] at ha
  rw [ha] at he
  rw [integralInner_semiclassicalJacobi_add_one ht p.derivative q (hi := hM.integrable_mul _ _)]
  simp only [integralInner, eval_mul, eval_add]
  linarith

end Polynomial
