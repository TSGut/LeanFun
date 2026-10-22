/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraL2

/-! # Operator-norm stability of Volterra kernels

Uniform approximation on the physical triangle controls the L² operator norm.
Reference: Gutleb–Olver, arXiv:1906.03907, Sections 3.1–3.2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped Topology InnerProductSpace
namespace Real

variable {K L : (Fin 2 → ℝ) → ℝ}
  (hK : ContinuousOn K volterraTriangle) (hL : ContinuousOn L volterraTriangle)
  {M N δ : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
  (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)
  (bL : ∀ z ∈ volterraTriangle, |L z| ≤ N)
  (hδ : 0 ≤ δ) (hKL : ∀ z ∈ volterraTriangle, |K z - L z| ≤ δ)

/-- Subtracting physical kernels subtracts their bounded L² realizations. -/
theorem volterraL2Operator_sub :
    volterraL2Operator hK hM bK - volterraL2Operator hL hN bL =
      volterraL2Operator (hK.sub hL) hδ hKL := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [sub_apply, inner_sub_right]
  simp only [inner_volterraL2Operator]
  rw [← mul_sub, ← integral_sub (integrable_volterraL2_pair hK hM bK f g)
    (integrable_volterraL2_pair hL hN bL f g)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [volterraL2Kernel, Pi.sub_apply]
  split_ifs <;> ring

include hδ hKL in
/-- The uniform kernel error bounds the physical operator-norm error. -/
theorem norm_volterraL2Operator_sub_le :
    ‖volterraL2Operator hK hM bK - volterraL2Operator hL hN bL‖ ≤ δ := by
  rw [volterraL2Operator_sub hK hL hM hN bK bL hδ hKL]
  exact norm_volterraL2Operator_le (hK.sub hL) hδ hKL

/-- Polynomial kernels approximate a continuous Volterra operator in operator norm. -/
theorem exists_polynomial_near_volterraL2Operator {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : MvPolynomial (Fin 2) ℝ) (N : ℝ) (hN : 0 ≤ N)
      (bp : ∀ z ∈ volterraTriangle, |MvPolynomial.eval z p| ≤ N),
      ‖volterraL2Operator p.continuous_eval.continuousOn hN bp -
        volterraL2Operator hK hM bK‖ < ε := by
  obtain ⟨p, hp⟩ := MvPolynomial.exists_polynomial_near_volterraKernel hK
    (half_pos hε)
  have bp : ∀ z ∈ volterraTriangle, |MvPolynomial.eval z p| ≤ M + ε / 2 := by
    intro z hz
    calc
      _ ≤ |MvPolynomial.eval z p - K z| + |K z| := by simpa only [sub_add_cancel] using abs_add_le (MvPolynomial.eval z p - K z) (K z)
      _ ≤ ε / 2 + M := add_le_add (hp z hz).le (bK z hz)
      _ = _ := add_comm _ _
  refine ⟨p, M + ε / 2, by positivity, bp, ?_⟩
  exact (norm_volterraL2Operator_sub_le p.continuous_eval.continuousOn hK
    (by positivity) hM bp bK (half_pos hε).le
    (fun z hz ↦ (hp z hz).le)).trans_lt (half_lt_self hε)

/-- Vanishing uniform kernel errors imply convergence in operator norm. -/
theorem tendsto_volterraL2Operator_of_error_bounds
    {Ks : ℕ → (Fin 2 → ℝ) → ℝ}
    (hs : ∀ n, ContinuousOn (Ks n) volterraTriangle)
    {B e : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (bs : ∀ n z, z ∈ volterraTriangle → |Ks n z| ≤ B n)
    (he : ∀ n, 0 ≤ e n)
    (err : ∀ n z, z ∈ volterraTriangle → |Ks n z - K z| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ volterraL2Operator (hs n) (hB n) (bs n)) atTop
      (𝓝 (volterraL2Operator hK hM bK)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_volterraL2Operator_sub_le (hs n) hK (hB n) hM
      (bs n) bK (he n) (err n)) hte

end Real
