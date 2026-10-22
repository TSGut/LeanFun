/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Classical contour inputs and circle integrals

Integrability is bundled for the actual line integrand. Functions are defined
only on the circle, including the degenerate constant curve at radius zero.
Reference: ATAP, proof of Theorem 8.1.
-/
public section
open MeasureTheory Complex Metric Real
noncomputable section
namespace Complex
/-- A function on the actual contour, with integrability of its parametrized
line integrand. The radius may be zero (a constant curve) or signed.
Reference: ATAP, proof of Theorem 8.1. -/
abbrev CircleIntegralInput (c : ℂ) (r : ℝ) :=
  {f : sphere c |r| → ℂ // IntervalIntegrable
    (fun θ : ℝ => (circleMap 0 r θ * I) *
      f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) volume 0 (2 * π)}

/-- Classical integral on a circle; no values outside the contour are needed. -/
def circleIntegralOn {c : ℂ} {r : ℝ} (f : CircleIntegralInput c r) : ℂ :=
  ∫ θ in 0..2 * π, (circleMap 0 r θ * I) *
    f.val ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩

theorem circleIntegralOn_spec {c : ℂ} {r : ℝ} (f : CircleIntegralInput c r) :
    IntervalIntegrable (fun θ : ℝ => (circleMap 0 r θ * I) *
      f.val ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) volume 0 (2 * π) ∧
    circleIntegralOn f = ∫ θ in 0..2 * π, (circleMap 0 r θ * I) *
      f.val ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩ :=
  ⟨f.property, rfl⟩

/-- Internal bridge: the global representative is used only on the contour. -/
theorem circleIntegralOn_eq_circleIntegral {c : ℂ} {r : ℝ}
    (f : CircleIntegralInput c r) (F : ℂ → ℂ)
    (hF : ∀ z : sphere c |r|, F z = f.val z) :
    circleIntegralOn f = circleIntegral F c r := by
  unfold circleIntegralOn circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [deriv_circleMap, smul_eq_mul, hF ⟨_, circleMap_mem_sphere' c r θ⟩]

/-- Restrict a globally represented integrable function to its actual contour.
This constructor is an internal bridge, with no values assigned off the circle. -/
def CircleIntegralInput.ofCircleIntegrable {c : ℂ} {r : ℝ}
    (F : ℂ → ℂ) (hF : CircleIntegrable F c r) : CircleIntegralInput c r :=
  ⟨fun z => F z, by simpa only [deriv_circleMap, smul_eq_mul] using hF.out⟩

/-- Continuous functions on the circle give classical contour inputs. -/
@[expose] def CircleIntegralInput.ofContinuous {c : ℂ} {r : ℝ}
    (f : sphere c |r| → ℂ) (hf : Continuous f) : CircleIntegralInput c r :=
  ⟨f, by
    have hc : Continuous (fun θ : ℝ =>
        f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) :=
      hf.comp ((continuous_circleMap c r).subtype_mk _)
    exact (((continuous_circleMap 0 r).mul continuous_const).mul hc).intervalIntegrable _ _⟩

@[simp] theorem CircleIntegralInput.ofContinuous_val {c : ℂ} {r : ℝ}
    (f : sphere c |r| → ℂ) (hf : Continuous f) :
    (ofContinuous f hf).val = f := rfl

/-- Adding integrable contour inputs preserves integrability. -/
def CircleIntegralInput.add {c : ℂ} {r : ℝ}
    (f g : CircleIntegralInput c r) : CircleIntegralInput c r :=
  ⟨fun z => f.val z + g.val z, by
    simpa only [mul_add] using f.property.add g.property⟩

theorem circleIntegralOn_add {c : ℂ} {r : ℝ} (f g : CircleIntegralInput c r) :
    circleIntegralOn (f.add g) = circleIntegralOn f + circleIntegralOn g := by
  simp only [circleIntegralOn, CircleIntegralInput.add, mul_add]
  exact intervalIntegral.integral_add f.property g.property

/-- The classical length-times-bound estimate (ATAP, proof of Theorem 8.1). -/
theorem norm_circleIntegralOn_le {c : ℂ} {r M : ℝ}
    (f : CircleIntegralInput c r) (hf : ∀ z, ‖f.val z‖ ≤ M) :
    ‖circleIntegralOn f‖ ≤ 2 * π * |r| * M := by
  calc
    ‖circleIntegralOn f‖ ≤ |r| * M * |2 * π - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro θ _
      calc
        ‖(circleMap 0 r θ * I) * f.val ⟨_, circleMap_mem_sphere' c r θ⟩‖ =
            |r| * ‖f.val ⟨_, circleMap_mem_sphere' c r θ⟩‖ := by
          simp only [norm_mul, norm_I, norm_circleMap_zero, mul_one]
        _ ≤ |r| * M := mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
    _ = 2 * π * |r| * M := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
      ring

@[simp] theorem circleIntegralOn_radius_zero {c : ℂ} (f : CircleIntegralInput c 0) :
    circleIntegralOn f = 0 := by
  simp [circleIntegralOn, circleMap]
end Complex
