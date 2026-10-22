/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2NormBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraExponentialFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraExponentialTail
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraFiniteResidual

/-! # Finite-data error certificates for exponential Volterra solves

The bound separates data error, polynomial-kernel error and the finite residual.
No finite-section inverse bound is needed. Reference: Gutleb's thesis, §2.7,
and the residual identity for boundedly invertible operators.
-/
@[expose] public noncomputable section
open Polynomial
namespace MvPolynomial
local notation "E" => lp (fun _ : ℕ ↦ ℝ) 2

/-- A numerical full-inverse bound, valid for every real exponential parameter. -/
theorem norm_inverse_volterraExponentialOperator_le_numeric (lam : ℝ) :
    ‖Ring.inverse (volterraExponentialOperator lam)‖ ≤ Real.exp (5*|lam|) := by
  apply (norm_inverse_volterraExponentialOperator_le lam).trans
  apply Real.exp_le_exp.mpr
  have h := add_le_add norm_reflectedJacobiOneZeroL2_le norm_shiftedJacobiOneZeroL2_le
  nlinarith [abs_nonneg lam]

/-- Numerical raw operator truncation error, with both factor radii discharged. -/
theorem norm_volterraExponentialPartial_operator_sub_le_numeric (lam : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (m L : ℕ) (hL : m^2 ≤ L) :
    ‖volterraPreconditionedL2 (volterraExponentialPartial lam L)-volterraExponentialOperator lam‖ ≤
      q^m*Real.exp (7*|lam| /q) := by
  convert norm_volterraExponentialPartial_operator_sub_le_geometric lam
    norm_reflectedJacobiOneZeroL2_le norm_shiftedJacobiOneZeroL2_le hq hq1 m L hL using 1
  congr 2
  ring

/-- Data and operator errors combine with the full approximate residual.
The approximate vector need not solve its retained equations exactly. -/
theorem norm_volterraExponential_solution_error_le (lam : ℝ) (g d v : E)
    (B : E →L[ℝ] E) {δ ε : ℝ} (hd : ‖g-d‖ ≤ δ)
    (hB : ‖B-volterraExponentialOperator lam‖ ≤ ε) :
    ‖v-Ring.inverse (volterraExponentialOperator lam) g‖ ≤
      Real.exp (5*|lam|)*(δ+‖d-B v‖+ε*‖v‖) := by
  have hr : ‖volterraExponentialOperator lam v-g‖ ≤ δ+‖d-B v‖+ε*‖v‖ := by
    rw [norm_sub_rev]
    have h1 := dist_triangle g d (volterraExponentialOperator lam v)
    have h2 := dist_triangle d (B v) (volterraExponentialOperator lam v)
    simp only [dist_eq_norm] at h1 h2
    have h3 : ‖B v-volterraExponentialOperator lam v‖ ≤ ε*‖v‖ :=
      ((B-volterraExponentialOperator lam).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    linarith
  apply (ContinuousLinearMap.norm_sub_inverse_apply_le_residual _
    (isUnit_and_stable_volterraExponentialOperator lam).1 g v).trans
  exact mul_le_mul (norm_inverse_volterraExponentialOperator_le_numeric lam) hr
    (norm_nonneg _) (Real.exp_pos _).le

/-- A certificate using a polynomial approximation of the exponential kernel and a data-tail bound. -/
theorem norm_volterraExponential_polynomial_certificate (lam : ℝ) (g d v : E)
    {δ q : ℝ} (hd : ‖g-d‖ ≤ δ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m L : ℕ) (hL : m^2 ≤ L) :
    ‖v-Ring.inverse (volterraExponentialOperator lam) g‖ ≤
      Real.exp (5*|lam|)*(δ+
        ‖d-volterraPreconditionedL2 (volterraExponentialPartial lam L) v‖+
        q^m*Real.exp (7*|lam| /q)*‖v‖) :=
  norm_volterraExponential_solution_error_le lam g d v _ hd
    (norm_volterraExponentialPartial_operator_sub_le_numeric lam hq hq1 m L hL)

/-- A finite-data certificate: the residual and input norms are finite sums.
The residual includes all rows up to the rectangular degree cutoff. -/
theorem norm_volterraExponential_finite_certificate (lam : ℝ) (g : E)
    (c d : ℕ →₀ ℝ) (N M : ℕ) (hc : ∀ n ∈ c.support, n < N)
    (hd : ∀ n ∈ d.support, n < M) {δ q : ℝ} (hg : ‖g-lp.finsuppL2 d‖ ≤ δ)
    (hq : 0 < q) (hq1 : q ≤ 1) (m L : ℕ) (hL : m^2 ≤ L) :
    ‖lp.finsuppL2 c-Ring.inverse (volterraExponentialOperator lam) g‖ ≤
      Real.exp (5*|lam|)*(δ+
        Real.sqrt (∑ i ∈ Finset.range (max M (N+(volterraExponentialPartial lam L).totalDegree)),
          (d i-(-1 : ℝ)^i*((i : ℝ)+1)*
            volterraProriolCoefficients (volterraExponentialPartial lam L) c i)^2)+
        q^m*Real.exp (7*|lam| /q)*Real.sqrt (∑ i ∈ Finset.range N, (c i)^2)) := by
  have h := norm_volterraExponential_polynomial_certificate lam g (lp.finsuppL2 d)
    (lp.finsuppL2 c) hg hq hq1 m L hL
  rwa [norm_volterraFiniteResidual_eq _ c d N M hc hd,lp.norm_finsuppL2_eq_sqrt_sum c N hc] at h
end MvPolynomial
