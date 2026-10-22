/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Affine
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtis

/-! # Chebyshev interpolation and quadrature on general intervals
Transport the canonical algorithms through affine coordinates, retaining their
full-constant coefficient convention. Reference: ATAP, Chapters 6, 8 and 19.
-/

public section
namespace Polynomial.Chebyshev
open Set MeasureTheory Complex

private theorem integrable_of_affine {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun t ↦ f (intervalMap a b t)) volume (-1) 1) :
    IntervalIntegrable f volume a b := by
  let c := (b - a) / 2
  let d := (a + b) / 2
  have hc : c ≠ 0 := ne_of_gt (half_pos (sub_pos.mpr hab))
  have hm : IntervalIntegrable (fun y ↦ f (y + d)) volume (-c) c :=
    (IntervalIntegrable.comp_mul_left_iff hc).mp (by
      simpa only [neg_div, div_self hc, intervalMap, c, d] using hf)
  have hh := (IntervalIntegrable.comp_add_right_iff).mp hm
  convert hh using 1 <;> dsimp [c, d] <;> ring


/-- The DCT polynomial pulled back to `[a,b]` matches all the mapped extrema. -/
theorem eval_dctInterpolant_interval_node {a b : ℝ} (hab : a < b)
    {N : ℕ} (hN : N ≠ 0) (f : ℝ → ℝ) {j : ℕ} (hj : j ≤ N) :
    (dctInterpolant N (fun t ↦ f (intervalMap a b t))).eval
      (intervalCoord a ⟨b, ne_of_lt hab⟩ (intervalMap a b (node N j))) = f (intervalMap a b (node N j)) := by
  rw [intervalCoord_intervalMap hab]
  exact eval_dctInterpolant_node hN _ hj

/-- Integrating the transported DCT interpolant gives the scaled canonical rule. -/
theorem integral_dctInterpolant_interval {a b : ℝ} (hab : a < b) (N : ℕ) (f : ℝ → ℝ) :
    (∫ x in a..b, (dctInterpolant N (fun t ↦ f (intervalMap a b t))).eval
      (intervalCoord a ⟨b, ne_of_lt hab⟩ x)) =
      (b - a) / 2 * clenshawCurtis N (fun t ↦ f (intervalMap a b t)) := by
  have hi : IntervalIntegrable (fun x ↦
      (dctInterpolant N (fun t ↦ f (intervalMap a b t))).eval
        (intervalCoord a ⟨b, ne_of_lt hab⟩ x)) volume a b := by
    apply Continuous.intervalIntegrable
    exact (dctInterpolant N _).continuous.comp (by unfold intervalCoord; fun_prop)
  rw [integral_comp_intervalMap a b ⟨_, hi⟩]
  simp only [intervalCoord_intervalMap hab, clenshawCurtis_eq_integral_dctInterpolant]

/-- Clenshaw--Curtis remains exact on physical polynomials of degree at most `N`. -/
theorem clenshawCurtis_interval_eval {a b : ℝ} (hab : a < b)
    {N : ℕ} (hN : N ≠ 0) {p : ℝ[X]} (hp : p.degree ≤ N) :
    (b - a) / 2 * clenshawCurtis N (fun t ↦ p.eval (intervalMap a b t)) =
      ∫ x in a..b, p.eval x := by
  let q := p.comp (Polynomial.C ((b - a) / 2) * X + Polynomial.C ((a + b) / 2))
  have hc : (b - a) / 2 ≠ 0 := ne_of_gt (half_pos (sub_pos.mpr hab))
  have hd : (Polynomial.C ((b - a) / 2) * X + Polynomial.C ((a + b) / 2)).degree = 1 := by
    rw [degree_add_eq_left_of_degree_lt (degree_C_lt_degree_C_mul_X hc), degree_C_mul_X hc]
  have hq : q.degree ≤ N := by
    dsimp only [q]
    rwa [degree_comp (by rw [hd]; norm_num), hd, mul_one]
  have he (t : ℝ) : q.eval t = p.eval (intervalMap a b t) := by simp [q, intervalMap]
  rw [integral_comp_intervalMap a b ⟨_, p.continuous.intervalIntegrable _ _⟩]
  congr 1
  simpa only [he] using clenshawCurtis_eval hN hq

/-- A canonical interpolation error `E` gives physical quadrature error at most
`(b-a)*E`, with the Jacobian accounted for exactly. -/
theorem abs_integral_sub_clenshawCurtis_interval_le {a b E : ℝ} (hab : a < b)
    {N : ℕ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun t ↦ f (intervalMap a b t)) volume (-1) 1)
    (he : ∀ t ∈ Icc (-1 : ℝ) 1,
      |f (intervalMap a b t) - (dctInterpolant N (fun u ↦ f (intervalMap a b u))).eval t| ≤ E) :
    |(∫ x in a..b, f x) - (b - a) / 2 * clenshawCurtis N (fun t ↦ f (intervalMap a b t))| ≤
      (b - a) * E := by
  rw [integral_comp_intervalMap a b ⟨f, integrable_of_affine hab hf⟩, ← mul_sub, abs_mul,
    abs_of_pos (half_pos (sub_pos.mpr hab))]
  have h := mul_le_mul_of_nonneg_left (abs_integral_sub_clenshawCurtis_le hf he)
    (half_pos (sub_pos.mpr hab)).le
  convert h using 1
  ring

/-- Geometric error on `[a,b]` when `F` is the analytic extension in canonical
coordinates. No boundary analyticity is assumed (ATAP, Theorem 8.2). -/
theorem abs_integral_sub_clenshawCurtis_interval_le_of_analytic
    {a b : ℝ} (hab : a < b) {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M) {N : ℕ} (hN : N ≠ 0) :
    |(∫ x in a..b, (F (intervalCoord a ⟨b, ne_of_lt hab⟩ x)).re) -
      (b - a) / 2 * clenshawCurtis N (fun t ↦ (F t).re)| ≤
      4 * (b - a) * M / (ρ ^ N * (ρ - 1)) := by
  have hc : ContinuousOn (fun t : ℝ ↦ (F t).re) (Icc (-1) 1) :=
    Complex.continuous_re.continuousOn.comp
      (hF.continuousOn.comp Complex.continuous_ofReal.continuousOn
        (fun t ht ↦ ofReal_mem_bernsteinEllipse hρ ht)) (fun _ _ ↦ mem_univ _)
  have hi : IntervalIntegrable (fun t : ℝ ↦ (F t).re) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hc)
  have hp : IntervalIntegrable (fun x ↦ (F (intervalCoord a ⟨b, ne_of_lt hab⟩ x)).re)
      volume a b := integrable_of_affine hab (by simpa only [intervalCoord_intervalMap hab] using hi)
  rw [integral_comp_intervalMap a b ⟨_, hp⟩]
  simp only [intervalCoord_intervalMap hab]
  rw [← mul_sub, abs_mul, abs_of_pos (half_pos (sub_pos.mpr hab))]
  have h := mul_le_mul_of_nonneg_left
    (abs_integral_sub_clenshawCurtis_le_of_analytic hρ hF hM hN)
    (half_pos (sub_pos.mpr hab)).le
  convert h using 1
  ring

end Polynomial.Chebyshev
