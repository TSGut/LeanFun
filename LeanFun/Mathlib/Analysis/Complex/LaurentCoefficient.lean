/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanFun.Mathlib.MeasureTheory.Integral.CircleDomain

/-!
# Bounds for Laurent coefficient integrals

The contour estimate used for analytic Chebyshev coefficient decay.
Reference: ATAP, proof of Theorem 8.1.
-/

public section

open Complex Metric Set Filter
open scoped Topology
open scoped Real

namespace Complex

/-- Cauchy's estimate for a Laurent coefficient on a circle of positive radius
(ATAP, proof of Theorem 8.1). -/
private theorem norm_laurent_integral_le_circleIntegral {f : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M) (n : ℕ)
    (_hi : CircleIntegrable (fun z => f z / z ^ (n + 1)) 0 r) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), f z / z ^ (n + 1))‖ ≤
      M / r ^ n := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z ↦ f z / z ^ (n + 1)) (c := 0) hr.le (C := M / r ^ (n + 1)) (by
      intro z hz
      have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
      rw [norm_div, norm_pow, hz']
      exact div_le_div_of_nonneg_right (hf z hz) (by positivity))
  simp only [smul_eq_mul] at h
  convert h using 1
  field_simp
  ring

/-- Deforming a Laurent coefficient contour through a closed annulus preserves it
(ATAP, proof of Theorem 8.1). The annulus excludes zero. -/
private theorem laurent_integral_eq_of_annulus_circleIntegral {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R \ ball 0 r, AnalyticAt ℂ f z) (n : ℕ) :
    (∮ z in C(0, R), f z / z ^ (n + 1)) =
      ∮ z in C(0, r), f z / z ^ (n + 1) := by
  have hz0 : ∀ z ∈ closedBall (0 : ℂ) R \ ball 0 r, z ≠ 0 := by
    intro z hz he
    subst z
    exact hz.2 (by simpa using hr)
  have hd : ∀ z ∈ closedBall (0 : ℂ) R \ ball 0 r,
      DifferentiableAt ℂ (fun z ↦ f z / z ^ (n + 1)) z := by
    intro z hz
    exact (hf z hz).differentiableAt.div
      (differentiableAt_id.pow _) (pow_ne_zero _ (hz0 z hz))
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) countable_empty
  · exact fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact hd z ⟨mem_closedBall.mpr (mem_ball.mp hz.1.1).le,
      fun h ↦ hz.1.2 (mem_closedBall.mpr (mem_ball.mp h).le)⟩

/-- A bounded analytic function on an open annulus has geometrically bounded
nonnegative Laurent coefficients, without boundary continuity (ATAP, Theorem 8.1). -/
private theorem norm_laurent_integral_le_of_open_annulus_circleIntegral {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ)
    (hf : ∀ z, 1 ≤ ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ f z)
    (hb : ∀ z, 1 ≤ ‖z‖ → ‖z‖ < ρ → ‖f z‖ ≤ M) (n : ℕ) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, 1), f z / z ^ (n + 1))‖ ≤
      M / ρ ^ n := by
  have hr (r : ℝ) (hr1 : 1 ≤ r) (hrρ : r < ρ) :
      ‖(2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, 1), f z / z ^ (n + 1))‖ ≤
        M / r ^ n := by
    rw [← laurent_integral_eq_of_annulus_circleIntegral (by norm_num : (0 : ℝ) < 1) hr1 (by
      intro z hz
      have hz1 : 1 ≤ ‖z‖ := by simpa using hz.2
      have hzr : ‖z‖ ≤ r := by simpa using hz.1
      exact hf z hz1 (hzr.trans_lt hrρ)) n]
    apply norm_laurent_integral_le_circleIntegral (lt_of_lt_of_le zero_lt_one hr1) ?_ n ?_
    · intro z hz
      have hz' : ‖z‖ = r := by simpa using hz
      exact hb z (hz' ▸ hr1) (hz' ▸ hrρ)
    · apply ContinuousOn.circleIntegrable (zero_le_one.trans hr1)
      intro z hz
      have hz' : ‖z‖ = r := by simpa using hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hz' ▸ (zero_lt_one.trans_le hr1))
      exact ((hf z (hz' ▸ hr1) (hz' ▸ hrρ)).continuousAt.div
        (continuousAt_id.pow _) (pow_ne_zero _ hz0)).continuousWithinAt
  have hc : ContinuousAt (fun r : ℝ ↦ M / r ^ n) ρ :=
    continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hρ)))
  apply ge_of_tendsto (x := 𝓝[<] ρ) (hc.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, eventually_gt_nhds hρ |>.filter_mono nhdsWithin_le_nhds]
    with r hrρ hr1
  exact hr r hr1.le hrρ

/-- Laurent's contour estimate for every integrable contour input, expressed
through its bounded numerator (ATAP, proof of Theorem 8.1). -/
theorem norm_laurent_integral_le (r : Set.Ioi (0 : ℝ)) {M : ℝ} (n : ℕ)
    (g : CircleIntegralInput 0 r.val)
    (hb : ∀ z, ‖z.val ^ (n + 1) * g.val z‖ ≤ M) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ * circleIntegralOn g‖ ≤ M / r.val ^ n := by
  have hr0 : 0 < r.val := r.property
  have hbound : ∀ z, ‖g.val z‖ ≤ M / r.val ^ (n + 1) := by
    intro z
    have hz : ‖z.val‖ = r.val := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hr0] using z.property
    have h := hb z
    rw [norm_mul, norm_pow, hz] at h
    exact (le_div_iff₀ (pow_pos hr0 _)).2 (by simpa only [mul_comm] using h)
  have h := norm_circleIntegralOn_le g hbound
  have hpi : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by simp
  rw [norm_mul, hpi, ← div_eq_inv_mul, div_le_iff₀ Real.two_pi_pos]
  calc
    ‖circleIntegralOn g‖ ≤ 2 * Real.pi * |r.val| * (M / r.val ^ (n + 1)) := h
    _ = M / r.val ^ n * (2 * Real.pi) := by
      rw [abs_of_pos hr0, pow_succ]
      field_simp [ne_of_gt hr0]

/-- Contour deformation for genuine integrable inputs with the given Laurent
integrands (ATAP, proof of Theorem 8.1). -/
theorem laurent_integral_eq_of_annulus {f : ℂ → ℂ} (r R : Set.Ioi (0 : ℝ))
    (hrR : r.val ≤ R.val)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R.val \ ball 0 r.val, AnalyticAt ℂ f z) (n : ℕ)
    (gR : CircleIntegralInput 0 R.val) (gr : CircleIntegralInput 0 r.val)
    (hR : ∀ z, gR.val z = f z / z.val ^ (n + 1))
    (hrg : ∀ z, gr.val z = f z / z.val ^ (n + 1)) :
    circleIntegralOn gR = circleIntegralOn gr := by
  rw [circleIntegralOn_eq_circleIntegral gR (fun z => f z / z ^ (n + 1))
    (fun z => (hR z).symm),
    circleIntegralOn_eq_circleIntegral gr (fun z => f z / z ^ (n + 1))
    (fun z => (hrg z).symm)]
  exact laurent_integral_eq_of_annulus_circleIntegral r.property hrR hf n

/-- The open-annulus estimate on actual integrable contour inputs, without
assuming analyticity inside the inner circle (ATAP, Theorem 8.1). -/
theorem norm_laurent_integral_le_of_open_annulus {f : ℂ → ℂ} {M : ℝ} (ρ : Set.Ioi (1 : ℝ))
    (hf : ∀ z, 1 ≤ ‖z‖ → ‖z‖ < ρ.val → AnalyticAt ℂ f z)
    (hb : ∀ z, 1 ≤ ‖z‖ → ‖z‖ < ρ.val → ‖f z‖ ≤ M) (n : ℕ)
    (g : CircleIntegralInput 0 1)
    (hg : ∀ z, g.val z = f z / z.val ^ (n + 1)) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ * circleIntegralOn g‖ ≤ M / ρ.val ^ n := by
  rw [circleIntegralOn_eq_circleIntegral g (fun z => f z / z ^ (n + 1))
    (fun z => (hg z).symm)]
  exact norm_laurent_integral_le_of_open_annulus_circleIntegral ρ.property hf hb n

end Complex
