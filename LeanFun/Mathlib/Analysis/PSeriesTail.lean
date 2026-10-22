/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.PSeries

/-!
# An explicit tail bound for a p-series

The integral comparison used in ATAP, Theorem 7.2.
-/

public section

open Set MeasureTheory

namespace Real

/-- The tail of the `(ν + 1)`-power series is bounded by its integral,
`1 / (ν M^ν)`, when both natural numbers `ν` and `M` are positive. -/
theorem tsum_one_div_nat_add_pow_le {ν M : ℕ} (hν : 1 ≤ ν) (hM : 0 < M) :
    (∑' k : ℕ, 1 / ((k + (M + 1) : ℕ) : ℝ) ^ (ν + 1)) ≤
      1 / ((ν : ℝ) * (M : ℝ) ^ ν) := by
  have hν' : (0 : ℝ) < ν := by exact_mod_cast (show 0 < ν by omega)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hexp : -((ν + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-((ν + 1 : ℕ) : ℝ))) (Ici (M : ℝ)) := by
    intro x hx y hy hxy
    exact rpow_le_rpow_of_nonpos (hM'.trans_le hx) hxy (le_of_lt (hexp.trans (by norm_num)))
  have hi := hanti.tsum_comp_add_le_integral M (integrableOn_Ioi_rpow_of_lt hexp hM')
    (fun x hx ↦ rpow_nonneg (hM'.trans hx).le _)
  have hterm (k : ℕ) : ((k + M + 1 : ℕ) : ℝ) ^ (-((ν + 1 : ℕ) : ℝ)) =
      1 / ((k + (M + 1) : ℕ) : ℝ) ^ (ν + 1) := by
    rw [rpow_neg (by positivity), rpow_natCast]
    simp only [Nat.add_assoc, one_div]
  simp_rw [hterm] at hi
  rw [integral_Ioi_rpow_of_lt hexp hM'] at hi
  have he : -((ν + 1 : ℕ) : ℝ) + 1 = -(ν : ℝ) := by push_cast; ring
  rw [he, rpow_neg hM'.le, rpow_natCast] at hi
  convert hi using 1
  field_simp

end Real
