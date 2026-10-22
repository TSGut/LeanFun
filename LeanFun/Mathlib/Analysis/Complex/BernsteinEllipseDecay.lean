/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Complex.BernsteinEllipse
public import LeanFun.Mathlib.Analysis.Complex.LaurentCoefficient

/-!
# Laurent bounds on Bernstein ellipses

The complex-analysis step of Chebyshev coefficient decay. Only analyticity and
a bound in the open ellipse are assumed. Reference: ATAP, Theorem 8.1.
-/

public section

namespace Complex

/-- A unit-circle point has real part in the approximation interval. -/
theorem unitCircle_re_mem (z : Metric.sphere (0 : ℂ) |(1 : ℝ)|) :
    z.val.re ∈ Set.Icc (-1 : ℝ) 1 := by
  have hn : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using z.property
  exact abs_le.mp ((Complex.abs_re_le_norm z.val).trans_eq hn)

/-- A unit-circle point is nonzero. -/
theorem unitCircle_ne_zero (z : Metric.sphere (0 : ℂ) |(1 : ℝ)|) : z.val ≠ 0 := by
  apply norm_pos_iff.mp
  have hn : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using z.property
  rw [hn]
  norm_num

/-- On the unit circle, the Joukowski map is the real-part projection (ATAP Ch. 8). -/
theorem joukowski_unitCircle (z : Metric.sphere (0 : ℂ) |(1 : ℝ)|) :
    joukowski ⟨z.val, unitCircle_ne_zero z⟩ = (z.val.re : ℂ) := by
  have hn : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using z.property
  change (z.val + z.val⁻¹) / 2 = _
  rw [Complex.inv_eq_conj hn]
  apply Complex.ext <;> simp

/-- The integrable Laurent input of continuous interval data on the unit circle.
Reference: ATAP, Theorems 3.1 and 8.1. -/
@[expose] noncomputable def joukowskiLaurentInput
    (f : C(Set.Icc (-1 : ℝ) 1, ℂ)) (n : ℕ) : CircleIntegralInput 0 1 :=
  CircleIntegralInput.ofContinuous
    (fun z => f ⟨z.val.re, unitCircle_re_mem z⟩ / z.val ^ (n + 1)) (by
      have hp : Continuous (fun z : Metric.sphere (0 : ℂ) |(1 : ℝ)| =>
          (⟨z.val.re, unitCircle_re_mem z⟩ : Set.Icc (-1 : ℝ) 1)) :=
        (Complex.continuous_re.comp continuous_subtype_val).subtype_mk _
      exact (f.continuous.comp hp).div (continuous_subtype_val.pow _)
        (fun z => pow_ne_zero _ (unitCircle_ne_zero z)))

/-- Characterization of the actual-circle Laurent input (ATAP, Theorem 3.1). -/
theorem joukowskiLaurentInput_apply (f : C(Set.Icc (-1 : ℝ) 1, ℂ)) (n : ℕ)
    (z : Metric.sphere (0 : ℂ) |(1 : ℝ)|) :
    (joukowskiLaurentInput f n).val z =
      f ⟨z.val.re, unitCircle_re_mem z⟩ / z.val ^ (n + 1) := rfl

/-- The Laurent coefficients of the Joukowski pullback decay geometrically
(ATAP, Theorem 8.1), on actual integrable unit-circle inputs. -/
theorem norm_joukowski_laurent_integral_le {f : ℂ → ℂ} {M : ℝ} (ρ : Set.Ioi (1 : ℝ)) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hb : ∀ w ∈ bernsteinEllipse ρ, ‖f w‖ ≤ M) (n : ℕ)
    (g : CircleIntegralInput 0 1)
    (hg : ∀ z, g.val z = f (joukowski ⟨z.val, unitCircle_ne_zero z⟩) /
      z.val ^ (n + 1)) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ * circleIntegralOn g‖ ≤ M / ρ.val ^ n := by
  have hm (z : ℂ) (hz1 : 1 ≤ ‖z‖) (hzρ : ‖z‖ < ρ.val) :
      (z + z⁻¹) / 2 ∈ bernsteinEllipse ρ := by
    have hz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz1)
    change joukowski ⟨z, hz⟩ ∈ _
    apply (joukowski_mem_bernsteinEllipse_iff ρ.property ⟨z, hz⟩).2
    exact ⟨(inv_lt_one_of_one_lt₀ ρ.property).trans_le hz1, hzρ⟩
  apply norm_laurent_integral_le_of_open_annulus (f := fun z => f ((z + z⁻¹) / 2))
    ρ ?_ ?_ n g ?_
  · intro z hz1 hzρ
    exact (hf _ (hm z hz1 hzρ)).comp (f := fun w : ℂ => (w + w⁻¹) / 2)
      (analyticAt_joukowski_expression (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz1)))
  · intro z hz1 hzρ
    exact hb _ (hm z hz1 hzρ)
  · intro z
    exact hg z

end Complex
