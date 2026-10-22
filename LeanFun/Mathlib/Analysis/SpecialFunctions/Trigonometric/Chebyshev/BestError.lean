/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.NearBest
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform best error and near-best interpolation
Use the genuine supremum norm on continuous functions on the compact interval.
The best error is an infimum; attainment is not needed. Reference: ATAP, Chapter 16.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Set

/-- Restrict a complex polynomial to the real approximation interval. -/
noncomputable def polynomialOnInterval (p : ℂ[X]) : C(Icc (-1 : ℝ) 1, ℂ) :=
  ⟨fun x ↦ p.eval (x : ℂ), by fun_prop⟩

/-- Best uniform error among complex polynomials of degree at most N. -/
noncomputable def bestUniformError (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) : ℝ :=
  sInf {e | ∃ p : ℂ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
    e = ‖f - polynomialOnInterval p‖}

private theorem competitorErrors_nonempty (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    {e | ∃ p : ℂ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      e = ‖f - polynomialOnInterval p‖}.Nonempty :=
  ⟨_, 0, by simp, rfl⟩

/-- The best error is nonnegative; the infimum is over a nonempty bounded-below set. -/
theorem bestUniformError_nonneg (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    0 ≤ bestUniformError N f := by
  apply le_csInf (competitorErrors_nonempty N f)
  rintro e ⟨p, _, rfl⟩
  exact norm_nonneg _

/-- Every admissible competitor bounds the best error from above. -/
theorem bestUniformError_le (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) {p : ℂ[X]}
    (hp : p.degree < ((N + 1 : ℕ) : WithBot ℕ)) :
    bestUniformError N f ≤ ‖f - polynomialOnInterval p‖ := by
  apply csInf_le
  · exact ⟨0, fun e ⟨q, _, he⟩ ↦ he ▸ norm_nonneg _⟩
  · exact ⟨p, hp, rfl⟩

/-- The continuous extrema interpolant on the compact interval. -/
noncomputable def interpolationOnInterval (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    C(Icc (-1 : ℝ) 1, ℂ) :=
  polynomialOnInterval (∑ j : Fin (N + 1),
    Polynomial.C (f ⟨extremaGridNode N j, extremaGridNode_mem_Icc N j⟩) * extremaCardinal N j)

/-- Uniform near-best interpolation against the best-error infimum, without
assuming existence of a minimizing polynomial (ATAP, Chapter 16). -/
theorem norm_sub_interpolationOnInterval_le_bestUniformError
    (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    ‖f - interpolationOnInterval N f‖ ≤
      (1 + extremaLebesgueConstant N) * bestUniformError N f := by
  have hL : 0 ≤ extremaLebesgueConstant N :=
    (extremaLebesgueFunction_nonneg N 0).trans
      (extremaLebesgueFunction_le_constant N (by norm_num))
  have hpos : 0 < 1 + extremaLebesgueConstant N := by linarith
  rw [mul_comm]
  apply (div_le_iff₀ hpos).mp
  apply le_csInf (competitorErrors_nonempty N f)
  rintro e ⟨p, hp, rfl⟩
  apply (div_le_iff₀ hpos).mpr
  rw [mul_comm]
  apply (ContinuousMap.norm_le _ (mul_nonneg hpos.le (norm_nonneg _))).mpr
  intro x
  have he := norm_sub_extremaInterpolant_le_lebesgueConstant hp
    (f := fun t ↦ if ht : t ∈ Icc (-1 : ℝ) 1 then f ⟨t, ht⟩ else 0)
    (ε := ‖f - polynomialOnInterval p‖)
    (fun t ht ↦ by
      simpa [ht, polynomialOnInterval] using
        (f - polynomialOnInterval p).norm_coe_le_norm ⟨t, ht⟩) x.property
  simpa [interpolationOnInterval, polynomialOnInterval, eval_extremaInterpolant,
    Polynomial.eval_finsetSum, extremaGridNode_mem_Icc, (extremaGridNode_mem_Icc N _).1,
    (extremaGridNode_mem_Icc N _).2, x.property] using he

/-- An explicit logarithmic near-best factor against the best-error infimum. -/
theorem norm_sub_interpolationOnInterval_le_log_bestUniformError
    {N : ℕ} (hN : N ≠ 0) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    ‖f - interpolationOnInterval N f‖ ≤
      (2 * Real.pi + 3 + 2 * Real.log N) * bestUniformError N f := by
  apply (norm_sub_interpolationOnInterval_le_bestUniformError N f).trans
  apply mul_le_mul_of_nonneg_right _ (bestUniformError_nonneg N f)
  linarith [extremaLebesgueConstant_le_log hN]

end Polynomial.Chebyshev
