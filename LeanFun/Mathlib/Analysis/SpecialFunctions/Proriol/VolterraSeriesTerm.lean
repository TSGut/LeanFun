/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraKernelMajorant
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Joint coefficient bounds for Volterra kernel series

A weighted absolute coefficient controls the physical monomial, its inner-variable
derivative, and its ordered operator. Reference: Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
open Polynomial
namespace MvPolynomial

/-- A bivariate monomial, with the outer coordinate first. -/
def volterraSeriesTerm (i j : ℕ) (c : ℝ) : MvPolynomial (Fin 2) ℝ :=
  monomial (Finsupp.single 0 i + Finsupp.single 1 j) c

/-- Physical evaluation of a kernel-series monomial. -/
theorem eval_volterraSeriesTerm (i j : ℕ) (c : ℝ) (z : Fin 2 → ℝ) :
    eval z (volterraSeriesTerm i j c) = c*z 0^i*z 1^j := by
  have he : volterraSeriesTerm i j c = C c * X 0^i * X 1^j := by
    simp [volterraSeriesTerm, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial]
  rw [he]
  simp

/-- A single nonnegative weight controls values, inner derivatives and ordered operators. -/
def volterraSeriesWeight (R S : ℝ) (i j : ℕ) (c : ℝ) : ℝ :=
  |c| *R^i*S^j*(j+1)

/-- The joint coefficient weight is nonnegative for nonnegative radii. -/
theorem volterraSeriesWeight_nonneg {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (i j : ℕ) (c : ℝ) : 0 ≤ volterraSeriesWeight R S i j c := by
  unfold volterraSeriesWeight
  positivity

/-- A physical monomial is bounded on the box by its joint coefficient weight. -/
theorem norm_eval_volterraSeriesTerm_le {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (i j : ℕ) (c : ℝ) (z : Fin 2 → ℝ) (hx : |z 0| ≤ R) (hy : |z 1| ≤ S) :
    ‖eval z (volterraSeriesTerm i j c)‖ ≤ volterraSeriesWeight R S i j c := by
  rw [eval_volterraSeriesTerm, norm_mul, norm_mul, norm_pow, norm_pow]
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx i)
    (abs_nonneg c)) (pow_le_pow_left₀ (abs_nonneg _) hy j) (by positivity) (by positivity)
  change |c| *|z 0| ^i*|z 1| ^j ≤ _
  exact hp.trans (by unfold volterraSeriesWeight; nlinarith [show 0 ≤ |c| *R^i*S^j by positivity])

/-- The ordered action of one kernel monomial. -/
theorem volterraPreconditionedL2_seriesTerm (i j : ℕ) (c : ℝ) :
    volterraPreconditionedL2 (volterraSeriesTerm i j c) =
      c • (reflectedJacobiOneZeroL2^i*shiftedJacobiOneZeroL2^j) := by
  rw [volterraSeriesTerm,volterraPreconditionedL2_monomial]
  simp

/-- Radii dominating the ordered factor norms also bound each operator term. -/
theorem norm_volterraPreconditionedL2_seriesTerm_le {R S : ℝ}
    (hR : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hS : ‖shiftedJacobiOneZeroL2‖ ≤ S)
    (i j : ℕ) (c : ℝ) :
    ‖volterraPreconditionedL2 (volterraSeriesTerm i j c)‖ ≤
      volterraSeriesWeight R S i j c := by
  have hp (A : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
      ‖A^n‖ ≤ ‖A‖^n := by
    cases n with
    | zero =>
      simp only [pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n => exact norm_pow_le' A (Nat.succ_pos n)
  have hR0 := (norm_nonneg _).trans hR
  have hS0 := (norm_nonneg _).trans hS
  rw [volterraPreconditionedL2_seriesTerm,norm_smul]
  apply (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
    (mul_le_mul ((hp _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hR i))
      ((hp _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hS j)) (norm_nonneg _) (by positivity)))
    (norm_nonneg c)).trans
  change |c| *(R^i*S^j) ≤ _
  unfold volterraSeriesWeight
  nlinarith [show 0 ≤ |c| *R^i*S^j by positivity]

/-- The inner-variable derivative of a series monomial has the same summable bound. -/
theorem norm_volterraSeriesTerm_derivative_le {R S : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S)
    (i j : ℕ) (c x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ S) :
    ‖c*x^i*((j : ℝ)*y^(j-1))‖ ≤ volterraSeriesWeight R S i j c := by
  have hpow : |y| ^(j-1) ≤ S^j :=
    (pow_le_pow_left₀ (abs_nonneg _) hy _).trans (pow_le_pow_right₀ hS (Nat.sub_le _ _))
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hj]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx i) (abs_nonneg c))
    (mul_le_mul_of_nonneg_left hpow hj) (by positivity) (by positivity)
  apply hb.trans
  unfold volterraSeriesWeight
  nlinarith [show 0 ≤ |c| *R^i*S^j by positivity]
end MvPolynomial
