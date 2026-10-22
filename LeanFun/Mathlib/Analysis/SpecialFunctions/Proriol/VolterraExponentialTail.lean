/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraExponentialSolve

/-! # Explicit geometric bounds for paired exponential truncations

A cutoff at least m squared omits only exponent pairs with sum at least m.
Enlarging the majorant radii gives a geometric bound without an infinite tail.
Reference: the exponential power series and natural-number square pairing.
-/
@[expose] public noncomputable section
open Polynomial
namespace MvPolynomial
local notation "a" => (fun n ↦ Prod.fst (Nat.unpair n))
local notation "b" => (fun n ↦ Prod.snd (Nat.unpair n))

private theorem weight_bound (lam : ℝ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (n : ℕ) :
    volterraSeriesWeight R S (a n) (b n) (volterraExponentialCoefficient lam n) ≤
      ((|lam| *R)^(a n) / ((a n).factorial : ℝ))*
        ((2*|lam| *S)^(b n) / ((b n).factorial : ℝ)) := by
  have hn : ((b n : ℕ) : ℝ)+1 ≤ (2 : ℝ)^(b n) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := b n))
  have hcast (k : ℕ) : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
  have hc : volterraSeriesWeight R S (a n) (b n) (volterraExponentialCoefficient lam n) =
      ((|lam| *R)^(a n) / ((a n).factorial : ℝ))*
      ((|lam| *S)^(b n) / ((b n).factorial : ℝ))*((b n : ℝ)+1) := by
    simp only [volterraSeriesWeight,volterraExponentialCoefficient,abs_div,abs_mul,
      abs_pow,abs_neg,hcast,mul_pow]
    ring
  rw [hc]
  have hb := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ ((|lam| *R)^(a n) / ((a n).factorial : ℝ))*
      ((|lam| *S)^(b n) / ((b n).factorial : ℝ)) by positivity)
  convert hb using 1
  simp only [mul_pow]
  ring

/-- A closed-form bound for the total joint coefficient majorant. -/
theorem tsum_volterraExponentialWeight_le (lam : ℝ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    (∑' n, volterraSeriesWeight R S (a n) (b n) (volterraExponentialCoefficient lam n)) ≤
      Real.exp (|lam| *R+2*|lam| *S) := by
  let f (k : ℕ × ℕ) := ((|lam| *R)^k.1/(k.1.factorial : ℝ))*
    ((2*|lam| *S)^k.2/(k.2.factorial : ℝ))
  have hs := (Real.summable_pow_div_factorial (|lam| *R)).mul_of_nonneg
    (Real.summable_pow_div_factorial (2*|lam| *S)) (fun n ↦ by positivity) (fun n ↦ by positivity)
  have hp : Summable (fun n ↦ f (Nat.unpair n)) := by
    simpa only [Function.comp_def,Nat.pairEquiv_symm_apply] using
      (Nat.pairEquiv.symm.summable_iff.mpr hs)
  apply (Summable.tsum_le_tsum (weight_bound lam hR hS)
    (summable_volterraExponentialWeight lam hR hS) hp).trans_eq
  have hr := Nat.pairEquiv.symm.tsum_eq f
  simp only [Nat.pairEquiv_symm_apply] at hr
  rw [hr]
  have hnorm (x : ℝ) : Summable (fun n : ℕ ↦ ‖x^n/(n.factorial : ℝ)‖) := by
    simpa only [norm_div,norm_pow,Real.norm_natCast] using Real.summable_pow_div_factorial ‖x‖
  rw [show f = (fun k : ℕ × ℕ ↦ ((|lam| *R)^k.1/(k.1.factorial : ℝ))*
    ((2*|lam| *S)^k.2/(k.2.factorial : ℝ))) from rfl,
    ← tsum_mul_tsum_of_summable_norm (hnorm _) (hnorm _)]
  have he (x : ℝ) : (∑' n : ℕ, x^n/(n.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
  rw [he,he,Real.exp_add]

private theorem cutoff_degree {m N n : ℕ} (hN : m^2 ≤ N) :
    m ≤ a (n+N)+b (n+N) := by
  by_contra h
  have hm : max (a (n+N)) (b (n+N))+1 ≤ m := by omega
  have hp := Nat.pair_lt_max_add_one_sq (a (n+N)) (b (n+N))
  rw [Nat.pair_unpair] at hp
  have hsq := Nat.pow_le_pow_left hm 2
  omega

private theorem weight_scale (lam R S q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    volterraSeriesWeight R S (a n) (b n) (volterraExponentialCoefficient lam n) =
      q^(a n+b n) * volterraSeriesWeight (R/q) (S/q) (a n) (b n)
        (volterraExponentialCoefficient lam n) := by
  simp only [volterraSeriesWeight,div_pow,pow_add]
  field_simp

/-- An explicit geometric bound for the common physical and operator tail.
The cutoff N may be arbitrary; m squared must not exceed N. -/
theorem volterraExponentialTail_le_geometric (lam : ℝ) {R S q : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hq : 0 < q) (hq1 : q ≤ 1)
    (m N : ℕ) (hN : m^2 ≤ N) :
    volterraSeriesTail a b ⟨volterraExponentialCoefficient lam,
      summable_volterraExponentialWeight lam hR hS⟩ N ≤
      q^m * Real.exp ((|lam| *R+2*|lam| *S)/q) := by
  let w (n : ℕ) := volterraSeriesWeight (R/q) (S/q) (a n) (b n)
    (volterraExponentialCoefficient lam n)
  have hw : Summable w := summable_volterraExponentialWeight lam
    (div_nonneg hR hq.le) (div_nonneg hS hq.le)
  have hw0 (n : ℕ) : 0 ≤ w n := volterraSeriesWeight_nonneg
    (div_nonneg hR hq.le) (div_nonneg hS hq.le) _ _ _
  have hb (n : ℕ) : volterraSeriesWeight R S (a (n+N)) (b (n+N))
      (volterraExponentialCoefficient lam (n+N)) ≤ q^m*w (n+N) := by
    rw [weight_scale lam R S q hq.ne']
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hq.le hq1 (cutoff_degree hN)) (hw0 _)
  have htail : (∑' n, w (n+N)) ≤ ∑' n, w n := by
    rw [← hw.sum_add_tsum_nat_add N]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ ↦ hw0 n))
  unfold volterraSeriesTail
  calc
    _ ≤ ∑' n, q^m*w (n+N) := Summable.tsum_le_tsum hb
      ((summable_nat_add_iff N).mpr (summable_volterraExponentialWeight lam hR hS))
      (((summable_nat_add_iff N).mpr hw).mul_left _)
    _ = q^m * ∑' n, w (n+N) := tsum_mul_left
    _ ≤ q^m * ∑' n, w n := mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ q^m * Real.exp (|lam| *(R/q)+2*|lam| *(S/q)) := mul_le_mul_of_nonneg_left
      (tsum_volterraExponentialWeight_le lam (div_nonneg hR hq.le) (div_nonneg hS hq.le))
      (by positivity)
    _ = _ := by congr 2; ring
/-- Explicit physical-kernel error, with no infinite coefficient tail left in the bound. -/
theorem norm_volterraExponentialPartial_sub_le_geometric (lam : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (m N : ℕ) (hN : m^2 ≤ N)
    (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
    ‖eval z (volterraExponentialPartial lam N)-Real.exp (lam*(z 0-z 1))‖ ≤
      q^m * Real.exp (3*|lam| /q) := by
  apply (norm_volterraExponentialPartial_sub_le lam (R := 1) (S := 1)
    le_rfl le_rfl N z hz).trans
  convert volterraExponentialTail_le_geometric lam (R := 1) (S := 1)
    zero_le_one zero_le_one hq hq1 m N hN using 1
  congr 2
  ring

/-- Explicit raw operator-norm error, with radii bounding the two ordered factors. -/
theorem norm_volterraExponentialPartial_operator_sub_le_geometric (lam : ℝ) {R S q : ℝ}
    (hR : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hS : ‖shiftedJacobiOneZeroL2‖ ≤ S)
    (hq : 0 < q) (hq1 : q ≤ 1) (m N : ℕ) (hN : m^2 ≤ N) :
    ‖volterraPreconditionedL2 (volterraExponentialPartial lam N)-volterraExponentialOperator lam‖ ≤
      q^m * Real.exp ((|lam| *R+2*|lam| *S)/q) := by
  have hR0 := (norm_nonneg _).trans hR
  have hS0 := (norm_nonneg _).trans hS
  exact (norm_volterraSeriesPartial_sub_operator_le a b (volterraExponentialCoefficient lam)
    (summable_volterraExponentialWeight lam hR0 hS0) hR hS N).trans
    (volterraExponentialTail_le_geometric lam hR0 hS0 hq hq1 m N hN)
end MvPolynomial
