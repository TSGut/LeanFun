/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraApproximation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Almost-everywhere differentiation of polynomial Volterra kernels

The first-kind differentiation identity is valid for locally integrable inputs,
not only continuous inputs. Reference: Linz, Analytical and Numerical Methods
for Volterra Equations (1985), first-kind equations with differentiable kernels.
Application: the injectivity step in Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace MvPolynomial

/-- Locally integrable inputs remain integrable after polynomial kernel multiplication. -/
theorem intervalIntegrable_polynomialKernel_mul (K : MvPolynomial (Fin 2) ℝ)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (x a b : ℝ) :
    IntervalIntegrable (fun y ↦ eval (![x, y] : Fin 2 → ℝ) K * f y) volume a b := by
  have hi : IntervalIntegrable f volume a b := intervalIntegrable_iff.mpr
    ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  exact hi.continuousOn_mul ((K.continuous_eval.comp (by fun_prop)).continuousOn)

/-- Kernel addition commutes with Volterra integration for locally integrable inputs. -/
private theorem polynomialKernelIntegral_add (K L : MvPolynomial (Fin 2) ℝ)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (K + L) * f y) = (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) + (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) L * f y) := by
  funext x
  simp only [eval_add, add_mul, Pi.add_apply]
  exact intervalIntegral.integral_add
    (intervalIntegrable_polynomialKernel_mul K hf x 0 x)
    (intervalIntegrable_polynomialKernel_mul L hf x 0 x)

/-- The outer kernel coordinate becomes multiplication of the output. -/
private theorem polynomialKernelIntegral_mul_X_zero (K : MvPolynomial (Fin 2) ℝ) (f : ℝ → ℝ) (_hf : LocallyIntegrable f volume) :
    (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (K * X 0) * f y) = fun x ↦ (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x * x := by
  funext x
  simp only [eval_mul, eval_X, Matrix.cons_val_zero]
  simp_rw [show ∀ y, eval (![x, y] : Fin 2 → ℝ) K * x * f y =
      (eval (![x, y] : Fin 2 → ℝ) K * f y) * x by intro y; ring]
  exact intervalIntegral.integral_mul_const x _

/-- The inner kernel coordinate becomes multiplication of the input. -/
private theorem polynomialKernelIntegral_mul_X_one (K : MvPolynomial (Fin 2) ℝ) (f : ℝ → ℝ) (_hf : LocallyIntegrable f volume) :
    (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (K * X 1) * f y) = (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * (fun y ↦ y * f y) y) := by
  funext x
  simp [mul_assoc]

/-- Polynomial Volterra kernels send locally integrable inputs to continuous outputs. -/
private theorem continuous_polynomialKernelIntegral (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    Continuous ((fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y)) := by
  induction K using MvPolynomial.induction_on generalizing f with
  | C c =>
    have hi (a b : ℝ) : IntervalIntegrable f volume a b := intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
    change Continuous (fun x ↦ (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (C c) * f y) x)
    simpa only [eval_C, intervalIntegral.integral_const_mul] using
      (intervalIntegral.continuous_primitive hi 0).const_mul c
  | add K L hK hL =>
    rw [polynomialKernelIntegral_add K L hf]
    exact (hK f hf).add (hL f hf)
  | mul_X K i hK =>
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at *
    · rw [polynomialKernelIntegral_mul_X_zero _ _ hf]
      exact (hK f hf).mul continuous_id
    · rw [polynomialKernelIntegral_mul_X_one _ _ hf]
      exact hK _ (hf.continuous_mul continuous_id)

/-- Almost-everywhere Leibniz differentiation for polynomial Volterra kernels. -/
private theorem ae_hasDerivAt_polynomialKernelIntegral (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, HasDerivAt ((fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y))
      (eval (fun _ ↦ x) K * f x + (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K) * f y) x) x := by
  induction K using MvPolynomial.induction_on generalizing f with
  | C c =>
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
    change HasDerivAt (fun t ↦ (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (C c) * f y) t) _ x
    simpa [pderiv_C, intervalIntegral.integral_const_mul] using
      (hx 0).const_mul c
  | add K L hK hL =>
    filter_upwards [hK f hf, hL f hf] with x hx hy
    rw [polynomialKernelIntegral_add K L hf]
    convert hx.add hy using 1
    rw [show pderiv 0 (K + L) = pderiv 0 K + pderiv 0 L from map_add _ _ _,
      congrFun (polynomialKernelIntegral_add (pderiv 0 K) (pderiv 0 L) hf) x]
    simp only [eval_add, add_mul, Pi.add_apply]
    ring
  | mul_X K i hK =>
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at *
    · filter_upwards [hK f hf] with x hx
      rw [polynomialKernelIntegral_mul_X_zero _ _ hf]
      convert hx.mul (hasDerivAt_id x) using 1
      · rfl
      · simp only [pderiv_mul, pderiv_X_self, mul_one]
        rw [congrFun (polynomialKernelIntegral_add (pderiv 0 K * X 0) K hf) x]
        simp only [Pi.add_apply]
        rw [congrFun (polynomialKernelIntegral_mul_X_zero (pderiv 0 K) f hf) x]
        simp only [eval_mul, eval_X, id_eq]
        ring
    · have hg : LocallyIntegrable (fun y ↦ y * f y) volume :=
        hf.continuous_mul continuous_id
      filter_upwards [hK (fun y ↦ y * f y) hg] with x hx
      rw [polynomialKernelIntegral_mul_X_one _ _ hf]
      convert hx using 1
      simp [mul_assoc, mul_comm, mul_left_comm]

/-- Polynomial kernels and locally integrable inputs supply every oriented row.
Reference: Linz (1985), the first-kind differentiation identity. -/
def _root_.Real.VolterraIntegralInput.ofPolynomial
    (K : MvPolynomial (Fin 2) ℝ) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (x : ℝ) : Real.VolterraIntegralInput x :=
  .ofKernel (fun z ↦ eval z K) f (intervalIntegrable_polynomialKernel_mul K hf x 0 x)

/-- Polynomial-kernel integration is additive whenever the two row products exist. -/
theorem polynomialVolterraIntegral_add (K L : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (x : ℝ)
    (hK : IntervalIntegrable (fun y ↦ eval ![x,y] K * f y) volume 0 x)
    (hL : IntervalIntegrable (fun y ↦ eval ![x,y] L * f y) volume 0 x) :
    Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z (K+L)) f
      (by simpa only [eval_add, add_mul] using hK.add hL)) =
    Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z K) f hK) +
      Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z L) f hL) := by
  simp only [Real.volterraIntegral_ofKernel, eval_add, add_mul]
  exact intervalIntegral.integral_add hK hL

/-- Multiplication by the outer coordinate multiplies the integral by its endpoint. -/
theorem polynomialVolterraIntegral_mul_X_zero (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (x : ℝ)
    (h : IntervalIntegrable (fun y ↦ eval ![x,y] K * f y) volume 0 x) :
    Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z (K * X 0)) f
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using h.mul_const x)) =
      Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z K) f h) * x := by
  simp only [Real.volterraIntegral_ofKernel, eval_mul, eval_X, Matrix.cons_val_zero]
  simp_rw [show ∀ y, eval (![x, y] : Fin 2 → ℝ) K * x * f y =
      (eval (![x, y] : Fin 2 → ℝ) K * f y) * x by intro y; ring]
  exact intervalIntegral.integral_mul_const x _

/-- Moving the inner coordinate into the input preserves the same integrable product. -/
theorem polynomialVolterraIntegral_mul_X_one (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (x : ℝ)
    (h : IntervalIntegrable (fun y ↦ eval ![x,y] K * (y * f y)) volume 0 x) :
    Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z (K * X 1)) f
      (by simpa [mul_assoc] using h)) =
      Real.volterraIntegral (.ofKernel (x := x) (fun z ↦ eval z K) (fun y ↦ y * f y) h) := by
  simp [Real.volterraIntegral_ofKernel, mul_assoc]

/-- Polynomial Volterra kernels send locally integrable inputs to continuous outputs. -/
theorem continuous_polynomialVolterraIntegral (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    Continuous (fun x ↦ Real.volterraIntegral (.ofPolynomial K hf x)) := by
  simpa only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] using
    continuous_polynomialKernelIntegral K f hf

/-- Almost-everywhere Leibniz differentiation for polynomial Volterra kernels. -/
theorem ae_hasDerivAt_polynomialVolterraIntegral (K : MvPolynomial (Fin 2) ℝ)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, HasDerivAt (fun t ↦ Real.volterraIntegral (.ofPolynomial K hf t))
      (eval (fun _ ↦ x) K * f x +
        Real.volterraIntegral (.ofPolynomial (pderiv 0 K) hf x)) x := by
  simpa only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] using
    ae_hasDerivAt_polynomialKernelIntegral K f hf

end MvPolynomial
