/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSeriesSolve
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Pairing

/-! # The exponential Volterra kernel as an absolutely majorized series

The product of the two exponential series represents exp(lam(x-y)) for every real lam.
The natural-number pairing enumerates all bivariate monomials; square-index
cutoffs correspond to rectangular exponent sets. Reference: the exponential
power series and Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
open Polynomial Set Filter
open scoped Topology
namespace MvPolynomial

/-- Coefficients of exp(lam x) exp(-lam y), in the standard pairing enumeration. -/
def volterraExponentialCoefficient (lam : ℝ) (n : ℕ) : ℝ :=
  lam^(Nat.unpair n).1 / (Nat.unpair n).1.factorial *
    (-lam)^(Nat.unpair n).2 / (Nat.unpair n).2.factorial

private theorem exp_series_norm_summable (x : ℝ) :
    Summable (fun n : ℕ ↦ ‖x^n/(n.factorial : ℝ)‖) := by
  simpa only [norm_div,norm_pow,Real.norm_natCast] using Real.summable_pow_div_factorial ‖x‖

/-- The exponential coefficient weights are summable for arbitrary nonnegative radii. -/
theorem summable_volterraExponentialWeight (lam : ℝ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Summable (fun n ↦ volterraSeriesWeight R S (Nat.unpair n).1 (Nat.unpair n).2
      (volterraExponentialCoefficient lam n)) := by
  have hs := (Real.summable_pow_div_factorial (|lam| *R)).mul_of_nonneg
    (Real.summable_pow_div_factorial (2*|lam| *S)) (fun n ↦ by positivity) (fun n ↦ by positivity)
  have hp : Summable (fun n ↦ ((|lam| *R)^(Nat.unpair n).1 / ((Nat.unpair n).1.factorial : ℝ))*
      ((2*|lam| *S)^(Nat.unpair n).2 / ((Nat.unpair n).2.factorial : ℝ))) :=
    by simpa only [Function.comp_def,Nat.pairEquiv_symm_apply] using
      (Nat.pairEquiv.symm.summable_iff.mpr hs)
  apply hp.of_nonneg_of_le
    (fun n ↦ volterraSeriesWeight_nonneg hR hS _ _ _) (fun n ↦ ?_)
  have hn : ((Nat.unpair n).2 : ℝ)+1 ≤ (2 : ℝ)^(Nat.unpair n).2 := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := (Nat.unpair n).2))
  have hcast (k : ℕ) : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
  have hc : volterraSeriesWeight R S (Nat.unpair n).1 (Nat.unpair n).2
      (volterraExponentialCoefficient lam n) =
      ((|lam| *R)^(Nat.unpair n).1 / ((Nat.unpair n).1.factorial : ℝ))*
      ((|lam| *S)^(Nat.unpair n).2 / ((Nat.unpair n).2.factorial : ℝ))*((Nat.unpair n).2+1) := by
    simp only [volterraSeriesWeight,volterraExponentialCoefficient,abs_div,abs_mul,
      abs_pow,abs_neg,hcast,mul_pow]
    ring
  rw [hc]
  have hb := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ ((|lam| *R)^(Nat.unpair n).1 / ((Nat.unpair n).1.factorial : ℝ))*
      ((|lam| *S)^(Nat.unpair n).2 / ((Nat.unpair n).2.factorial : ℝ)) by positivity)
  convert hb using 1
  simp only [mul_pow]
  ring
/-- The exponential series supplies a convergent input at every real point. -/
def VolterraSeriesKernelInput.ofExponential (lam : ℝ) (z : Fin 2 → ℝ) :
    VolterraSeriesKernelInput (fun n ↦ (Nat.unpair n).1) (fun n ↦ (Nat.unpair n).2) z :=
  VolterraSeriesKernelInput.ofWeight _ _ (volterraExponentialCoefficient lam)
    (abs_nonneg (z 0)) (abs_nonneg (z 1))
    (summable_volterraExponentialWeight lam (abs_nonneg (z 0)) (abs_nonneg (z 1)))
    ⟨z, le_rfl, le_rfl⟩

/-- The paired bivariate series is exactly the exponential convolution kernel. -/
theorem volterraSeriesKernel_exponential (lam : ℝ) (z : Fin 2 → ℝ) :
    volterraSeriesKernel (fun n ↦ (Nat.unpair n).1) (fun n ↦ (Nat.unpair n).2)
      (VolterraSeriesKernelInput.ofExponential lam z) = Real.exp (lam*(z 0-z 1)) := by
  simp only [volterraSeriesKernel, VolterraSeriesKernelInput.ofExponential,
    VolterraSeriesKernelInput.ofWeight]
  have he (n : ℕ) : volterraExponentialCoefficient lam n * z 0^(Nat.unpair n).1 *
      z 1^(Nat.unpair n).2 =
      ((lam*z 0)^(Nat.unpair n).1 / (Nat.unpair n).1.factorial) *
        (((-lam)*z 1)^(Nat.unpair n).2 / (Nat.unpair n).2.factorial) := by
    simp only [volterraExponentialCoefficient,mul_pow]
    ring
  simp_rw [he]
  have hr := Nat.pairEquiv.symm.tsum_eq
    (fun k : ℕ × ℕ ↦ ((lam*z 0)^k.1/(k.1.factorial : ℝ))*
      (((-lam)*z 1)^k.2/(k.2.factorial : ℝ)))
  simp only [Nat.pairEquiv_symm_apply] at hr
  rw [hr]
  rw [← tsum_mul_tsum_of_summable_norm (exp_series_norm_summable (lam*z 0))
    (exp_series_norm_summable ((-lam)*z 1))]
  have hexp (x : ℝ) : (∑' n : ℕ, x^n/(n.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
  rw [hexp,hexp,← Real.exp_add]
  congr 1
  ring

end MvPolynomial
