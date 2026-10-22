/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraExponentialSolve

/-! # Ordered exponential factorisation for the Volterra operator

The two exponentials retain the outer/inner order; no commutation is assumed.
Reference: the Banach algebra exponential series and Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
open Polynomial
namespace MvPolynomial
local notation "E" => lp (fun _ : ℕ ↦ ℝ) 2
local notation "H" => reflectedJacobiOneZeroL2
local notation "J" => shiftedJacobiOneZeroL2

/-- The exponential kernel gives an ordered product of operator exponentials. -/
theorem volterraExponentialOperator_eq (lam : ℝ) :
    volterraExponentialOperator lam =
      NormedSpace.exp (lam • H) * NormedSpace.exp ((-lam) • J) := by
  have hp (x : ℝ) (A : E →L[ℝ] E) (n : ℕ) : (x • A)^n = x^n • A^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,pow_succ,pow_succ]
      apply ContinuousLinearMap.ext
      intro v
      simp only [mul_apply_eq_comp,smul_apply,
        map_smul,smul_smul,mul_comm]
  have hm (x y : ℝ) (A B : E →L[ℝ] E) :
      (x • A)*(y • B) = (x*y) • (A*B) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [mul_apply_eq_comp,smul_apply,
      map_smul,smul_smul,mul_comm]
  unfold volterraExponentialOperator volterraSeriesOperator VolterraSeriesOperatorInput.ofWeight
  simp_rw [volterraPreconditionedL2_seriesTerm]
  have he (n : ℕ) : volterraExponentialCoefficient lam n •
      (H^(Nat.unpair n).1 * J^(Nat.unpair n).2) =
      (((Nat.unpair n).1.factorial : ℝ)⁻¹ • (lam • H)^(Nat.unpair n).1) *
        (((Nat.unpair n).2.factorial : ℝ)⁻¹ • ((-lam) • J)^(Nat.unpair n).2) := by
    simp only [volterraExponentialCoefficient,hp,hm,smul_smul,div_eq_mul_inv]
    congr 1
    ring
  simp_rw [he]
  have hr := Nat.pairEquiv.symm.tsum_eq (fun k : ℕ × ℕ ↦
    ((k.1.factorial : ℝ)⁻¹ • (lam • H)^k.1) *
      ((k.2.factorial : ℝ)⁻¹ • ((-lam) • J)^k.2))
  simp only [Nat.pairEquiv_symm_apply] at hr
  rw [hr, ← tsum_mul_tsum_of_summable_norm
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (lam • H))
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) ((-lam) • J))]
  rw [NormedSpace.exp_eq_tsum ℝ]

/-- The full inverse reverses the order of the two exponential factors. -/
theorem inverse_volterraExponentialOperator (lam : ℝ) :
    Ring.inverse (volterraExponentialOperator lam) =
      NormedSpace.exp (lam • J) * NormedSpace.exp ((-lam) • H) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  rw [volterraExponentialOperator_eq, Ring.inverse_mul (Or.inl (NormedSpace.isUnit_exp _)),
    Ring.inverse_exp, Ring.inverse_exp]
  have hn (x : ℝ) (A : E →L[ℝ] E) : -(x • A) = (-x) • A := by
    apply ContinuousLinearMap.ext
    intro v
    change -(x • A v) = (-x) • A v
    exact (_root_.neg_smul x (A v)).symm
  rw [hn,hn,neg_neg]

private theorem norm_exp_le (A : E →L[ℝ] E) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have hp (n : ℕ) : ‖A^n‖ ≤ ‖A‖^n := by
    cases n with
    | zero => exact ContinuousLinearMap.norm_id_le
    | succ n => exact norm_pow_le' A (Nat.succ_pos n)
  rw [NormedSpace.exp_eq_tsum ℝ]
  have he : (∑' n : ℕ, ‖A‖^n / (n.factorial : ℝ)) = Real.exp ‖A‖ := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
  rw [← he]
  apply tsum_of_norm_bounded (Real.summable_pow_div_factorial ‖A‖).hasSum
  intro n
  simp only [norm_smul, norm_inv, Real.norm_natCast, div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp n)
    (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))

/-- An explicit bound for the full inverse, separate from finite-section inverse bounds. -/
theorem norm_inverse_volterraExponentialOperator_le (lam : ℝ) :
    ‖Ring.inverse (volterraExponentialOperator lam)‖ ≤
      Real.exp (|lam| *(‖H‖+‖J‖)) := by
  rw [inverse_volterraExponentialOperator]
  calc
    _ ≤ ‖NormedSpace.exp (lam • J)‖ * ‖NormedSpace.exp ((-lam) • H)‖ := norm_mul_le _ _
    _ ≤ Real.exp ‖lam • J‖ * Real.exp ‖(-lam) • H‖ :=
      mul_le_mul (norm_exp_le _) (norm_exp_le _) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; simp only [norm_smul,Real.norm_eq_abs,abs_neg]; ring

/-- A full residual certifies solution error with an explicit exponential constant. -/
theorem norm_sub_volterraExponential_solution_le (lam : ℝ) (g v : E) :
    ‖v-Ring.inverse (volterraExponentialOperator lam) g‖ ≤
      Real.exp (|lam| *(‖H‖+‖J‖)) * ‖g-volterraExponentialOperator lam v‖ := by
  rw [norm_sub_rev g]
  exact (ContinuousLinearMap.norm_sub_inverse_apply_le_residual _
    (isUnit_and_stable_volterraExponentialOperator lam).1 g v).trans
    (mul_le_mul_of_nonneg_right (norm_inverse_volterraExponentialOperator_le lam) (norm_nonneg _))
end MvPolynomial
