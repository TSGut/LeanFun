/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Existence of orthogonal polynomial sequences

Gram–Schmidt preserves the initial polynomial degree filtration, giving a
sequence of exact degrees for any measure satisfying the moment and positivity hypotheses.

References: DLMF 18.2(i), https://dlmf.nist.gov/18.2; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

public section

open MeasureTheory Submodule InnerProductSpace

namespace Polynomial

/-- Every measure with finite polynomial moments and positive squared integrals
admits an orthogonal polynomial sequence of exact degrees (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem exists_isOrthogonal (μ : Measure ℝ) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) : ∃ P : Sequence ℝ, P.IsOrthogonal μ := by
  let core : InnerProductSpace.Core ℝ ℝ[X] := integralInnerProductCore μ hμ hpos
  let : NormedAddCommGroup ℝ[X] := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ ℝ[X] :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ ℝ[X])
  let P : Sequence ℝ := ⟨fun n => X ^ n, fun n => by simp⟩
  have hdegree (n : ℕ) : (gramSchmidt ℝ P n).degree = n := by
    have hunit (i : ℕ) : IsUnit (P i).leadingCoeff :=
      P.isUnit_leadingCoeff i
    have hspan (k : ℕ) : span ℝ (P '' Set.Iio k) = degreeLT ℝ k :=
      P.span_degreeLT (fun i _ => hunit i)
    have hmem : gramSchmidt ℝ P n ∈ span ℝ (P '' Set.Iio (n + 1)) := by
      rw [← span_gramSchmidt_Iio ℝ (P : ℕ → ℝ[X]) (n + 1)]
      exact subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
    rw [hspan, mem_degreeLT] at hmem
    have hnot : ¬ (gramSchmidt ℝ P n).degree < n := by
      intro h
      have hm : gramSchmidt ℝ P n ∈ span ℝ (P '' Set.Iio n) := by
        rw [hspan, mem_degreeLT]; exact h
      rw [← span_gramSchmidt_Iio ℝ (P : ℕ → ℝ[X]) n] at hm
      exact (gramSchmidt_linearIndependent P.linearIndependent).notMem_span_image
        (by simp : n ∉ Set.Iio n) hm
    have hn := gramSchmidt_ne_zero n P.linearIndependent
    rw [degree_eq_natDegree hn] at hmem hnot ⊢
    norm_cast at hmem hnot ⊢
    omega
  let Q : Sequence ℝ := ⟨gramSchmidt ℝ P, hdegree⟩
  refine ⟨Q, ⟨fun m n => hμ.integrable_mul (Q m) (Q n), ?_⟩⟩
  intro m n hmn
  exact gramSchmidt_orthogonal ℝ P hmn

end Polynomial
