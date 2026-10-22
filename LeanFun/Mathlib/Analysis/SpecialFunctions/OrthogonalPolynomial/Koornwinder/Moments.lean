/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Measure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.MvPolynomial

import Mathlib.Topology.Algebra.Polynomial

/-!
# Moments of generalised Koornwinder measures

Polynomial squared scales preserve all bivariate polynomial moments, even on
unbounded or disconnected supports. Reference: Dunkl–Xu, §2.6.1.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Finite moments of both factors give finite moments after separated transport. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_koornwinderMeasure {D : Set ℝ} {μ : Measure D} {ν : Measure ℝ} {ρ : D → ℝ}
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (a : ℝ[X]) (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) :
    HasFiniteMoments (koornwinderMeasure ρ μ ν) := by
  let := hμ.isFiniteMeasure
  let := Measure.isFiniteMeasure_of_map (μ := μ) measurable_subtype_coe.aemeasurable
  let := hν.isFiniteMeasure
  have hall (p : MvPolynomial (Fin 2) ℝ) :
      MemLp (fun v => eval v p) 2 (koornwinderMeasure ρ μ ν) := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      exact MemLp.ae_eq (Filter.Eventually.of_forall (fun v => (map_add (eval v) p q).symm))
        (hp.add hq)
    | monomial d c =>
      apply (memLp_two_iff_integrable_sq (monomial d c).continuous_eval.aestronglyMeasurable).mpr
      change Integrable ((fun v => eval v (monomial d c))^2) _
      rw [koornwinderMeasure, integrable_map_measure
        ((monomial d c).continuous_eval.pow 2).aestronglyMeasurable
        (continuous_koornwinderCoordinates hρ).measurable.aemeasurable]
      have hx := hμ.integrable_mul
        (Polynomial.C (c^2)*Polynomial.X^(2*d 0)*a^(d 1)) 1
      have hx' : Integrable (fun x : D =>
          (Polynomial.C (c^2)*Polynomial.X^(2*d 0)*a^(d 1)).eval (x : ℝ) *
            (1 : ℝ[X]).eval (x : ℝ)) μ :=
        (integrable_map_measure
          (((Polynomial.C (c^2)*Polynomial.X^(2*d 0)*a^(d 1)).continuous.mul
            (1 : ℝ[X]).continuous).aestronglyMeasurable)
          measurable_subtype_coe.aemeasurable).mp hx
      have hz := hν (Polynomial.X^(d 1))
      have hi := hx'.mul_prod hz
      apply hi.congr
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha] with v hv
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, mul_one] at *
      simp only [Function.comp_def, Pi.pow_apply, eval_monomial]
      rw [Finsupp.prod_fintype _ _ (by simp)]
      simp only [
        Fin.prod_univ_two, koornwinderCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hv]
      simp only [mul_pow, ← pow_mul, Nat.mul_comm]
      ring
  intro p
  exact (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).mp (hall p)

end MvPolynomial
