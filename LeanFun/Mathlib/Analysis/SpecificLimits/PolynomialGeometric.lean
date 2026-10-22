/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform convergence from polynomial times geometric error bounds

Every fixed-degree polynomial is dominated by rho^N when rho > 1.
Reference: the geometric convergence estimates in ATAP, Chapter 8.
-/

public section
open Filter
open scoped Topology

/-- A shifted fixed-degree polynomial is dominated by every geometric sequence
with ratio greater than one. -/
theorem tendsto_natCast_add_one_pow_div_const_pow (d : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ d / ρ ^ n) atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt d hρ).comp
    (tendsto_add_atTop_nat 1)).mul_const ρ
  convert h using 1
  · funext n
    dsimp
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  · simp

/-- A uniform polynomial-times-geometric error bound implies uniform convergence. -/
theorem tendstoUniformlyOn_of_polynomial_geometric_bound {ι E : Type*}
    [NormedAddCommGroup E] {u : ℕ → ι → E} {f : ι → E} {s : Set ι}
    (d : ℕ) {A B C ρ : ℝ} (hρ : 1 < ρ)
    (hb : ∀ N x, x ∈ s → ‖f x - u N x‖ ≤
      (1 + A * ((N : ℝ) + 1) ^ d) * (C / (ρ ^ N * B))) :
    TendstoUniformlyOn u f atTop s := by
  let e := fun N : ℕ ↦ (1 + A * ((N : ℝ) + 1) ^ d) * (C / (ρ ^ N * B))
  have he : Tendsto e atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ ↦ 1 / ρ ^ N) atTop (𝓝 (0 : ℝ)) := by
      simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 hρ
    have hd := tendsto_natCast_add_one_pow_div_const_pow d hρ
    have h := (h0.add (hd.const_mul A)).mul_const (C / B)
    convert h using 1
    · funext N
      dsimp [e]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    · simp
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with N hN
  intro x hx
  simpa only [dist_eq_norm] using (hb N x hx).trans_lt hN
