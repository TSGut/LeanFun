/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtisError
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.CoefficientAliasing

/-! # Clenshaw--Curtis errors on individual modes
Aliasing preserves parity, so every odd mode is integrated exactly, including
unresolved frequencies. References: ATAP, Chapters 4 and 19, Theorem 19.3.
-/

public section
namespace Polynomial.Chebyshev

/-- The quadrature of a Chebyshev mode is the moment of its folded frequency. -/
theorem clenshawCurtis_eval_T_alias {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    clenshawCurtis N (fun x ↦ (T ℝ k).eval x) = integralMoment (aliasIndex N k) := by
  simp only [clenshawCurtis, dite_eq_right hN]
  have he (j : Fin (N + 1)) :=
    extremaCoefficient_eval_T_alias hN (Nat.le_of_lt_succ j.isLt) k
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ (if aliasIndex N k = j then (1 : ℝ) else 0) * integralMoment j)]
  simp [ite_mul, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff.mpr (aliasIndex_le hN k)]

/-- Every odd mode has zero quadrature, regardless of its degree (ATAP 19.3). -/
theorem clenshawCurtis_eval_T_odd {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    clenshawCurtis N (fun x ↦ (T ℝ (↑(2 * k + 1 : ℕ))).eval x) = 0 := by
  rw [clenshawCurtis_eval_T_alias hN]
  have hp := aliasIndex_mod_two hN (2 * k + 1)
  have he : aliasIndex N (2 * k + 1) = 2 * (aliasIndex N (2 * k + 1) / 2) + 1 := by omega
  rw [he, integralMoment_odd]

/-- Positive weights of total mass two bound the quadrature of every mode. -/
theorem abs_clenshawCurtis_eval_T_le_two {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    |clenshawCurtis N (fun x ↦ (T ℝ k).eval x)| ≤ 2 := by
  have h := abs_clenshawCurtis_sub_le hN (f := fun x ↦ (T ℝ k).eval x)
    (g := fun _ ↦ 0) (ε := 1) (fun j _ ↦ by
      simpa using abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr (node_mem_Icc (n := N) (i := j))))
  simpa [clenshawCurtis_eq_sum_weights ⟨N, Nat.pos_of_ne_zero hN⟩] using h

/-- The unweighted moment of any mode of degree at least four is at most 2/15. -/
theorem abs_integralMoment_le_two_fifteenths {k : ℕ} (hk : 4 ≤ k) :
    |integralMoment k| ≤ 2 / 15 := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  rw [integralMoment_eq_ite]
  split_ifs
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_neg (by nlinarith : 1 - (k : ℝ)^2 < 0)]
    apply (div_le_iff₀ (by nlinarith : 0 < -(1 - (k : ℝ)^2))).2
    nlinarith
  · norm_num

/-- The modewise constant used in the sharper analytic quadrature bound. -/
theorem abs_integralMoment_sub_clenshawCurtis_le {N k : ℕ}
    (hN : N ≠ 0) (hk : 4 ≤ k) :
    |integralMoment k - clenshawCurtis N (fun x ↦ (T ℝ k).eval x)| ≤ 32 / 15 := by
  exact (abs_sub _ _).trans ((add_le_add (abs_integralMoment_le_two_fifteenths hk)
    (abs_clenshawCurtis_eval_T_le_two hN k)).trans_eq (by norm_num))

end Polynomial.Chebyshev
