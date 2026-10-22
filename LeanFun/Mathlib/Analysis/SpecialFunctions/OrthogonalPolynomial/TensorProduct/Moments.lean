/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.L2Space

/-! # Polynomial moments of finite product measures
Square integrability of every coordinate polynomial gives square integrability
of every multivariate polynomial. Reference: finite-product integration.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- Finite polynomial moments are preserved under finite products of measures. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_pi (μ : σ → Measure ℝ)
    (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i)) : HasFiniteMoments (Measure.pi μ) := by
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ (hμ i).isFiniteMeasure
  have hm : ∀ p : MvPolynomial σ ℝ, MemLp (fun x ↦ eval x p) 2 (Measure.pi μ) := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial d a =>
      apply (memLp_two_iff_integrable_sq (monomial d a).continuous_eval.aestronglyMeasurable).2
      have hi := Integrable.fintype_prod (fun i ↦ hμ i (Polynomial.X ^ d i))
      convert hi.const_mul (a ^ 2) using 1
      funext x
      simp [eval_monomial, Finsupp.prod_fintype, mul_pow, Finset.prod_pow]
    | add p q hp hq =>
      apply MemLp.ae_eq (hf_Lp := hp.add hq)
      filter_upwards [] with x
      simp only [Pi.add_apply, eval_add]
  intro p
  exact (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).1 (hm p)

end MvPolynomial
