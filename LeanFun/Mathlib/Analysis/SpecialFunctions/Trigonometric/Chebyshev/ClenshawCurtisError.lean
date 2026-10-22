/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtisWeights

/-! # Positive-rule Clenshaw--Curtis error bounds
Exactness and positive weights transfer arbitrary polynomial competitor bounds
to quadrature. Reference: ATAP, proof of Theorem 19.3.
-/

public section
namespace Polynomial.Chebyshev
open MeasureTheory Set

/-- Nodal perturbations are amplified by at most two. -/
theorem abs_clenshawCurtis_sub_le {N : ℕ} (hN : N ≠ 0) {f g : ℝ → ℝ} {ε : ℝ}
    (hfg : ∀ j ≤ N, |f (node N j) - g (node N j)| ≤ ε) :
    |clenshawCurtis N f - clenshawCurtis N g| ≤ 2 * ε := by
  rw [clenshawCurtis_eq_sum_weights ⟨N, Nat.pos_of_ne_zero hN⟩, clenshawCurtis_eq_sum_weights ⟨N, Nat.pos_of_ne_zero hN⟩,
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ j : Fin (N + 1),
        |clenshawCurtisWeight ⟨N, Nat.pos_of_ne_zero hN⟩ j * (f (node N j) - g (node N j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (N + 1), clenshawCurtisWeight ⟨N, Nat.pos_of_ne_zero hN⟩ j * ε := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_pos (clenshawCurtisWeight_pos ⟨N, Nat.pos_of_ne_zero hN⟩ j)]
      exact mul_le_mul_of_nonneg_left (hfg j (Nat.le_of_lt_succ j.isLt))
        (clenshawCurtisWeight_pos ⟨N, Nat.pos_of_ne_zero hN⟩ j).le
    _ = _ := by rw [← Finset.sum_mul, sum_clenshawCurtisWeight ⟨N, Nat.pos_of_ne_zero hN⟩]

/-- Every degree-N uniform competitor gives a direct quadrature bound of 4ε.
Only interval integrability of the data is required. -/
theorem abs_integral_sub_clenshawCurtis_le_of_competitor {N : ℕ} (hN : N ≠ 0)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-1) 1) {p : ℝ[X]}
    (hp : p.degree ≤ N) {ε : ℝ}
    (hε : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ ε) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f| ≤ 4 * ε := by
  have hq := abs_clenshawCurtis_sub_le hN (f := f) (g := fun x ↦ p.eval x) (ε := ε)
    (fun j (_ : j ≤ N) ↦ hε (node N j) node_mem_Icc)
  have hi : |∫ x in (-1 : ℝ)..1, f x - p.eval x| ≤ 2 * ε := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (f := fun x ↦ f x - p.eval x)
      (fun x hx ↦ by
        rw [Real.norm_eq_abs]
        apply hε x
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using he
  have he : (∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f =
      (∫ x in (-1 : ℝ)..1, f x - p.eval x) -
        (clenshawCurtis N f - clenshawCurtis N (fun x ↦ p.eval x)) := by
    rw [intervalIntegral.integral_sub hf (p.continuous.intervalIntegrable _ _),
      clenshawCurtis_eval hN hp]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hi hq).trans_eq (by ring))

end Polynomial.Chebyshev
