/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.FunctionalSpaces.DirichletSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
/-! # Cartesian calculus of real multivariate polynomials

Polynomial partial differentiation agrees with Fréchet differentiation in
coordinate directions. This gives integration by parts against compactly
supported smooth tests. Reference: Evans, *Partial Differential Equations*,
Chapter 5 (weak derivatives).
-/

@[expose] public noncomputable section
namespace MvPolynomial
variable {n : ℕ}
/-- Real multivariate polynomial evaluation is smooth. -/
theorem contDiff_eval (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ ↦ eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin n → ℝ ↦ c))
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | mul_X p j hp =>
    simpa only [eval_mul, eval_X] using
      hp.mul (by fun_prop : ContDiff ℝ ⊤ (fun x : Fin n → ℝ ↦ x j))
/-- The algebraic partial derivative equals the Cartesian Fréchet derivative. -/
theorem fderiv_eval_single (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ ↦ eval y p) x (Pi.single i 1) = eval x (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [eval_add]
    rw [fderiv_fun_add (p.contDiff_eval.differentiable (by simp)).differentiableAt
      (q.contDiff_eval.differentiable (by simp)).differentiableAt]
    simp [hp, hq]
  | mul_X p j hp =>
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul (p.contDiff_eval.differentiable (by simp)).differentiableAt
      (differentiableAt_apply j x)]
    rw [(hasFDerivAt_apply j x).fderiv]
    by_cases h : j = i <;> simp [hp, pderiv_X, h]
open MeasureTheory DirichletSpace
variable (Ω : TopologicalSpace.Opens (Fin n → ℝ))
/-- Polynomial evaluation satisfies integration by parts against compactly supported smooth tests. -/
theorem integral_eval_mul_testDerivative (p : MvPolynomial (Fin n) ℝ)
    (φ : TestFunction Ω ℝ ⊤) (i : Fin n) :
    (∫ x, eval x p * testDerivative Ω i φ x) =
      -(∫ x, eval x (pderiv i p) * φ x) := by
  have hi (p : MvPolynomial (Fin n) ℝ) (φ : TestFunction Ω ℝ ⊤) :
      Integrable (fun x ↦ eval x p * φ x) :=
    (p.continuous_eval.mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun x ↦ eval x p) (g := fun x ↦ φ x) (v := Pi.single i 1)
    (by simpa only [fderiv_eval_single] using hi (pderiv i p) φ)
    (by simpa only [testDerivative_apply] using hi p (testDerivative Ω i φ))
    (hi p φ)
    (fun x _ ↦ (p.contDiff_eval.differentiable (by simp)).differentiableAt)
    (fun x _ ↦ (φ.contDiff.differentiable (by simp)).differentiableAt)
  simpa only [testDerivative_apply, fderiv_eval_single] using h
end MvPolynomial
