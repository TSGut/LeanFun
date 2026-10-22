/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtis

/-! # Explicit Clenshaw--Curtis weights
Both nodal endpoints and the highest DCT frequency have their correct half
factors. Reference: ATAP, Chapters 4 and 19; Trefethen (2008), SIAM Review.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open MeasureTheory

/-- Half factors at the two ends of the extrema index range. -/
noncomputable def extremaEndpointWeight (N : {n : ℕ // 0 < n})
    (j : Fin (N.val + 1)) : ℝ :=
  if j.val = 0 ∨ j.val = N.val then 1 / 2 else 1

/-- The half-weighted sum as an ordinary finite weighted sum. -/
theorem extremaSum_eq_sum_endpointWeight (N : {n : ℕ // 0 < n}) (f : ℕ → ℝ) :
    extremaSum N f = ∑ j : Fin (N.val + 1), extremaEndpointWeight N j * f j := by
  rcases N with ⟨N, hNp⟩
  have hN : N ≠ 0 := Nat.ne_of_gt hNp
  simp only [extremaEndpointWeight]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (if j = 0 ∨ j = N then (1 / 2 : ℝ) else 1) * f j)]
  rw [Finset.sum_range_succ]
  have he : ∑ j ∈ Finset.range N, (if j = 0 ∨ j = N then (1 / 2 : ℝ) else 1) * f j =
      (∑ j ∈ Finset.range N, f j) - f 0 / 2 := by
    have hj (j : ℕ) (hj : j ∈ Finset.range N) :
        (if j = 0 ∨ j = N then (1 / 2 : ℝ) else 1) * f j = f j - (if j = 0 then f 0 / 2 else 0) := by
      have hjN : j ≠ N := ne_of_lt (Finset.mem_range.mp hj)
      by_cases hz : j = 0
      · subst j; simp; ring
      · simp [hz, hjN]
    rw [Finset.sum_congr rfl hj, Finset.sum_sub_distrib]
    simp [Nat.pos_of_ne_zero hN]
  rw [he]
  simp only [or_true, ite_true]
  dsimp only [extremaSum]
  ring

/-- The scalar moment equals the integral of the corresponding mode. -/
theorem integralMoment_eq_integral (k : ℕ) :
    integralMoment k = ∫ x in (-1 : ℝ)..1, (T ℝ k).eval x := (integral_eval_T k).symm

/-- The cosine-transform formula for the nodal Clenshaw--Curtis weights. -/
noncomputable def clenshawCurtisWeight (N : {n : ℕ // 0 < n})
    (j : Fin (N.val + 1)) : ℝ :=
  extremaEndpointWeight N j / N.val * ∑ k ∈ Finset.range (N.val + 1),
    (if k = 0 ∨ k = N.val then 1 else 2) * integralMoment k *
      (T ℝ k).eval (classicalNode N j)

/-- The weight formula on its classical index domain. -/
theorem clenshawCurtisWeight_eq_sum (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    clenshawCurtisWeight N j = extremaEndpointWeight N j / N.val *
      ∑ k ∈ Finset.range (N.val + 1),
        (if k = 0 ∨ k = N.val then 1 else 2) * integralMoment k *
          (T ℝ k).eval (classicalNode N j) := rfl

/-- The explicit weights evaluate the coefficient-defined quadrature. -/
theorem clenshawCurtis_eq_sum_weights (N : {n : ℕ // 0 < n}) (f : ℝ → ℝ) :
    clenshawCurtis N.val f =
      ∑ j : Fin (N.val + 1), clenshawCurtisWeight N j * f (classicalNode N j) := by
  simp only [clenshawCurtis, dite_eq_right (Nat.ne_of_gt N.property), extremaCoefficient_eq_sum (Nat.ne_of_gt N.property),
    extremaSum_eq_sum_endpointWeight N]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [clenshawCurtisWeight_eq_sum, Finset.mul_sum, Finset.sum_mul, classicalNode]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Odd modes have zero moment. -/
@[simp] theorem integralMoment_odd (k : ℕ) : integralMoment (2 * k + 1) = 0 := by
  rw [integralMoment_eq_ite, ite_eq_right (Nat.not_even_iff_odd.mpr ⟨k,rfl⟩)]

/-- Even moments in their rational form. -/
theorem integralMoment_even (k : ℕ) :
    integralMoment (2 * k) = 2 / (1 - (2 * (k : ℝ)) ^ 2) := by
  norm_num [integralMoment_eq_ite]

/-- The absolute even moments telescope. -/
theorem sum_abs_integralMoment_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1), |integralMoment k| = 3 - 1 / (2 * (m : ℝ) + 1) := by
  induction m with
  | zero => norm_num [integralMoment_eq_ite]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, integralMoment_odd, abs_zero, add_zero, ih]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, integralMoment_even]
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hd : 1 - (2 * ((m + 1 : ℕ) : ℝ)) ^ 2 < 0 := by push_cast; nlinarith
    rw [abs_of_neg (div_neg_of_pos_of_neg (by norm_num) hd)]
    push_cast at hd ⊢
    rw [show 1 - (2 * ((m : ℝ) + 1)) ^ 2 = -((2 * m + 1) * (2 * m + 3)) by ring]
    have h1 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring

/-- The absolute moment sum stays strictly below three at every finite cutoff. -/
theorem sum_abs_integralMoment_lt_three (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), |integralMoment k| < 3 := by
  apply lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (show N + 1 ≤ 2 * N + 1 by omega)) (fun _ _ _ ↦ abs_nonneg _))
  rw [sum_abs_integralMoment_even]
  have : 0 < 1 / (2 * (N : ℝ) + 1) := by positivity
  linarith

/-- A parity-explicit cosine formula, with the top frequency halved whether
N is even or odd. -/
theorem clenshawCurtisWeight_cosine (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    clenshawCurtisWeight N j = extremaEndpointWeight N j / N.val *
      ∑ k ∈ Finset.range (N.val + 1), (if k = 0 ∨ k = N.val then 1 else 2) *
        (if Even k then 2 / (1 - (k : ℝ) ^ 2) else 0) *
          Real.cos ((k : ℝ) * (Real.pi * (j : ℕ) / N.val)) := by
  have hN : N.val ≠ 0 := Nat.ne_of_gt N.property
  have hm (k : ℕ) : integralMoment k = if Even k then 2 / (1 - (k : ℝ) ^ 2) else 0 := by
    rw [integralMoment_eq_integral, integral_eval_T_eq_ite]
  simp only [clenshawCurtisWeight_eq_sum, hm, classicalNode, node, T_real_cos, Int.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm Real.pi ((j : ℕ) : ℝ)]

/-- The cosine kernel defining the weights is strictly positive on [-1,1]. -/
theorem clenshawCurtis_kernel_pos (N : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < ∑ k ∈ Finset.range (N + 1),
      (if k = 0 ∨ k = N then (1 : ℝ) else 2) * integralMoment k * (T ℝ k).eval x := by
  have ht (k : ℕ) : (if k = 0 then (6 : ℝ) else 0) - 2 * |integralMoment k| ≤
      (if k = 0 ∨ k = N then (1 : ℝ) else 2) * integralMoment k * (T ℝ k).eval x := by
    by_cases hk : k = 0
    · subst k; norm_num [integralMoment_eq_ite]
    rw [ite_eq_right hk, zero_sub]
    let a : ℝ := if k = 0 ∨ k = N then 1 else 2
    have ha : 0 ≤ a := by dsimp [a]; split_ifs <;> norm_num
    have ha2 : a ≤ 2 := by dsimp [a]; split_ifs <;> norm_num
    have hab : |a * integralMoment k * (T ℝ k).eval x| ≤ 2 * |integralMoment k| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      calc
        _ ≤ a * |integralMoment k| := mul_le_of_le_one_right
          (mul_nonneg ha (abs_nonneg _)) (abs_eval_T_real_le_one _ (abs_le.mpr hx))
        _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (abs_nonneg _)
    exact (neg_le_neg hab).trans (neg_abs_le _)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (N + 1)) ↦ ht k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ite_true] at hs
  linarith [sum_abs_integralMoment_lt_three N]

/-- Every Clenshaw--Curtis nodal weight is strictly positive for positive order. -/
theorem clenshawCurtisWeight_pos (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    0 < clenshawCurtisWeight N j := by
  rw [clenshawCurtisWeight_eq_sum]
  apply mul_pos _ (clenshawCurtis_kernel_pos N.val node_mem_Icc)
  apply div_pos
  · dsimp [extremaEndpointWeight]; split_ifs <;> norm_num
  · exact_mod_cast N.property

/-- The weights have the mass of the original interval. -/
theorem sum_clenshawCurtisWeight (N : {n : ℕ // 0 < n}) :
    ∑ j : Fin (N.val + 1), clenshawCurtisWeight N j = 2 := by
  have he := clenshawCurtis_eval (Nat.ne_of_gt N.property) (p := (1 : ℝ[X])) (by simp)
  rw [clenshawCurtis_eq_sum_weights N] at he
  simpa only [eval_one, mul_one, intervalIntegral.integral_const, sub_neg_eq_add,
    one_add_one_eq_two, smul_eq_mul] using he

/-- All positive-degree moments are nonpositive (odd moments are zero). -/
theorem integralMoment_nonpos {k : ℕ} (hk : 0 < k) : integralMoment k ≤ 0 := by
  by_cases h1 : k = 1
  · subst k; norm_num [integralMoment_eq_ite]
  rw [integralMoment_eq_integral, integral_eval_T_eq_ite]
  split_ifs
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    apply div_nonpos_of_nonneg_of_nonpos (by norm_num)
    nlinarith
  · exact le_rfl

/-- The signed moment sum is the complementary absolute moment sum. -/
theorem sum_integralMoment (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), integralMoment k =
      4 - ∑ k ∈ Finset.range (N + 1), |integralMoment k| := by
  have ht (k : ℕ) : integralMoment k =
      (if k = 0 then (4 : ℝ) else 0) - |integralMoment k| := by
    by_cases hk : k = 0
    · subst k; norm_num [integralMoment_eq_ite]
    · rw [ite_eq_right hk, zero_sub, abs_of_nonpos (integralMoment_nonpos (Nat.pos_of_ne_zero hk))]
      ring
  conv_lhs => rw [Finset.sum_congr rfl (fun k _ ↦ ht k)]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range,
    Nat.zero_lt_succ, ite_true]

/-- Removing half of the constant and highest frequencies gives the endpoint kernel. -/
theorem sum_endpoint_modes {N : ℕ} (hN : N ≠ 0) :
    (∑ k ∈ Finset.range (N + 1),
      (if k = 0 ∨ k = N then (1 : ℝ) else 2) * integralMoment k) =
      2 * (∑ k ∈ Finset.range (N + 1), integralMoment k) - 2 - integralMoment N := by
  have he (k : ℕ) : (if k = 0 ∨ k = N then (1 : ℝ) else 2) * integralMoment k =
      2 * integralMoment k - (if k = 0 then integralMoment 0 else 0) -
        (if k = N then integralMoment N else 0) := by
    by_cases h0 : k = 0
    · subst k; norm_num [Ne.symm hN, integralMoment_eq_ite]
    · by_cases hk : k = N
      · subst k; simp [hN]; ring
      · simp [h0, hk]
  rw [Finset.sum_congr rfl (fun k _ ↦ he k)]
  norm_num [Finset.sum_sub_distrib, ← Finset.mul_sum, integralMoment_eq_ite]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

/-- Both endpoint weights agree. -/
theorem clenshawCurtisWeight_last (N : {n : ℕ // 0 < n}) :
    clenshawCurtisWeight N (Fin.last N.val) = clenshawCurtisWeight N 0 := by
  have hN : N.val ≠ 0 := Nat.ne_of_gt N.property
  have he (k : ℕ) : integralMoment k * (-1 : ℝ) ^ k = integralMoment k := by
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow, mul_one]
    · simp [integralMoment_eq_ite, (Nat.not_even_iff_odd.mpr hk)]
  simp only [clenshawCurtisWeight_eq_sum, classicalNode, Fin.val_last, Fin.val_zero, extremaEndpointWeight, or_true, true_or, ite_true,
    node_eq_one, node_eq_neg_one hN, T_eval_one, mul_one, T_eval_neg_one,
    Int.cast_negOnePow_natCast, mul_assoc, he]

/-- Endpoint weight for even positive order. -/
theorem clenshawCurtisWeight_zero_even (m : {n : ℕ // 0 < n}) :
    clenshawCurtisWeight ⟨2 * m.val, by omega⟩ 0 =
      1 / ((2 * (m.val : ℝ)) ^ 2 - 1) := by
  rcases m with ⟨m, hmp⟩
  have hm : m ≠ 0 := Nat.ne_of_gt hmp
  have hN : 2 * m ≠ 0 := by omega
  rw [clenshawCurtisWeight_eq_sum]
  simp only [classicalNode, Fin.val_zero, node_eq_one, T_eval_one, mul_one]
  rw [sum_endpoint_modes hN, sum_integralMoment, sum_abs_integralMoment_even,
    integralMoment_even]
  simp only [extremaEndpointWeight, Fin.val_zero, true_or, ite_true, Nat.cast_mul, Nat.cast_ofNat]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [show (2 * (m : ℝ)) ^ 2 - 1 = (2 * m - 1) * (2 * m + 1) by ring,
    show 1 - (2 * (m : ℝ)) ^ 2 = -((2 * m - 1) * (2 * m + 1)) by ring]
  have hminus : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have hplus : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

/-- Endpoint weight for odd order, including the two-point rule. -/
theorem clenshawCurtisWeight_zero_odd (m : ℕ) :
    clenshawCurtisWeight ⟨2 * m + 1, by omega⟩ 0 = 1 / ((2 * (m : ℝ) + 1) ^ 2) := by
  rw [clenshawCurtisWeight_eq_sum]
  simp only [classicalNode, Fin.val_zero, node_eq_one, T_eval_one, mul_one]
  rw [sum_endpoint_modes (by omega), sum_integralMoment, Finset.sum_range_succ,
    integralMoment_odd, abs_zero, add_zero, sum_abs_integralMoment_even]
  simp only [extremaEndpointWeight, Fin.val_zero, true_or, ite_true, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring


/-- Classical cardinal-integral characterization of positive-order weights. -/
theorem clenshawCurtisWeight_eq_integral_basis (N : {n : ℕ // 0 < n})
    (j : Fin (N.val + 1)) :
    clenshawCurtisWeight N j = ∫ x in (-1 : ℝ)..1,
      (Lagrange.classicalBasis (Finset.range (N.val + 1)) (classicalNode N) j
        (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode N).injOn
          (Finset.mem_range.mpr j.isLt))).eval x := by
  classical
  let l := Lagrange.classicalBasis (Finset.range (N.val + 1)) (classicalNode N) j
    (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode N).injOn
      (Finset.mem_range.mpr j.isLt))
  have hjm : j.val ∈ Finset.range (N.val + 1) := Finset.mem_range.mpr j.isLt
  have hp : l.degree ≤ N.val := by
    change (Lagrange.basis (Finset.range (N.val + 1)) (classicalNode N) j).degree ≤ N.val
    rw [Lagrange.degree_basis (strictAntiOn_classicalNode N).injOn hjm]
    simp
  have he := clenshawCurtis_eval (Nat.ne_of_gt N.property) hp
  rw [clenshawCurtis_eq_sum_weights N, Finset.sum_eq_single j] at he
  · have hjv : l.eval (classicalNode N j) = 1 :=
      Lagrange.eval_basis_self (strictAntiOn_classicalNode N).injOn hjm
    simpa only [hjv, mul_one] using he
  · intro i _ hij
    have hiv : l.eval (classicalNode N i) = 0 :=
      Lagrange.eval_basis_of_ne (fun h => hij (Fin.ext h.symm))
        (Finset.mem_range.mpr i.isLt)
    simp only [hiv, mul_zero]
  · simp

end Polynomial.Chebyshev
