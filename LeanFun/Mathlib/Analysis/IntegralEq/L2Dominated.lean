/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Dominated convergence for real L² representatives

A square-integrable majorant gives norm convergence of L² classes.
Reference: the Lebesgue dominated convergence theorem.
-/

public noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace MeasureTheory
variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
  {l : Filter ι} [l.IsCountablyGenerated]

/-- The squared norm of an L² class is the integral of the squared representative. -/
theorem L2.norm_sq_eq_integral_sq (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

/-- Dominated convergence of representatives gives norm convergence in real L². -/
theorem tendsto_L2_of_dominated
    (f : ι → X → ℝ) (g : X → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ)
    (B : X → ℝ) (hB : Integrable (fun x ↦ B x ^ 2) μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, |f i x - g x| ≤ B x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) :
    Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
  have hs : Tendsto (fun i ↦ ∫ x, (f i x - g x) ^ 2 ∂μ) l (𝓝 0) := by
    simpa only [integral_zero, Pi.pow_apply, Pi.sub_apply] using
      (tendsto_integral_filter_of_dominated_convergence (f := fun _ : X ↦ (0 : ℝ))
        (fun x ↦ B x ^ 2)
        (Eventually.of_forall (fun i ↦ ((hf i).aestronglyMeasurable.sub
          hg.aestronglyMeasurable).pow 2))
        (Eventually.of_forall (fun i ↦ (hb i).mono (fun x hx ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2))) hB
        (ht.mono (fun x hx ↦ by simpa using (hx.sub_const (g x)).pow 2)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (i : ι) : ‖(hf i).toLp (f i) - hg.toLp g‖ ^ 2 =
      ∫ x, (f i x - g x) ^ 2 ∂μ := by
    rw [L2.norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf i).toLp (f i)) (hg.toLp g),
      (hf i).coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
    simp only [hx, Pi.sub_apply, hfx, hgx]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, ← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

end MeasureTheory
