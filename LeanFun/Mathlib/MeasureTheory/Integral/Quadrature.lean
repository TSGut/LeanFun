/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-! # Error bounds for positive quadrature rules
A positive finite rule that integrates constants and a competitor exactly has
error at most twice the measure mass times the uniform competitor error.
Reference: the positive-weight argument in ATAP, proof of Theorem 19.3.
-/

public section
namespace MeasureTheory
open Set

/-- Positive quadrature transfers a uniform competitor bound to an integration
error bound. The measured space and sampled points need not form an interval
(ATAP, proof of Theorem 19.3). -/
theorem abs_integral_sub_sum_le_of_nonneg_weights
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (s : Finset ι) (v : ι → α) (w : ι → ℝ) {f g : α → ℝ} {ε : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = μ.real univ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hexact : ∫ x, g x ∂μ = ∑ i ∈ s, w i * g (v i))
    (hae : ∀ᵐ x ∂μ, |f x - g x| ≤ ε)
    (hnodes : ∀ i ∈ s, |f (v i) - g (v i)| ≤ ε) :
    |(∫ x, f x ∂μ) - ∑ i ∈ s, w i * f (v i)| ≤ 2 * μ.real univ * ε := by
  have hi : |∫ x, (f x - g x) ∂μ| ≤ ε * μ.real univ := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_of_norm_le_const
      (f := fun x ↦ f x - g x) (by simpa only [Real.norm_eq_abs] using hae))
  have hs : |∑ i ∈ s, w i * (f (v i) - g (v i))| ≤ ε * μ.real univ := by
    calc
      _ ≤ ∑ i ∈ s, |w i * (f (v i) - g (v i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, w i * ε := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw i hi)]
        exact mul_le_mul_of_nonneg_left (hnodes i hi) (hw i hi)
      _ = _ := by rw [← Finset.sum_mul, hmass, mul_comm]
  have he : (∫ x, f x ∂μ) - ∑ i ∈ s, w i * f (v i) =
      (∫ x, (f x - g x) ∂μ) - ∑ i ∈ s, w i * (f (v i) - g (v i)) := by
    rw [integral_sub hf hg, hexact]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hi hs).trans_eq (by ring))

end MeasureTheory
