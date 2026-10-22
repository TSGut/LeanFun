/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.FiniteSpan
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.SeparatedModification
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Finite spans under unchanged inner lifts

Changing the outer orthogonal sequences preserves every separated finite span.
This is the finite-section compatibility behind generalised Type 1 conversion.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, Lemma 2.8.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')

/-- Every bounded-degree outer polynomial times a fixed lift lies in the separated span. -/
theorem outerPolynomial_mem_sectionSpan
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (ha0 : a ≠ 0) (ha : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ))
    (p : ℝ[X]) {N k : ℕ} (hp : p.natDegree+k ≤ N) :
    p.eval₂ C (X 0)*S.lift k ∈ S.sectionSpan N := by
  classical
  let hu (i : ℕ) : IsUnit (S.outer k i).leadingCoeff :=
    isUnit_iff_ne_zero.mpr (S.outer_leadingCoeff_pos k i).ne'
  have he := congrArg (fun p => (Polynomial.aeval (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)) p*S.lift k)
    ((S.outer_orthogonal k).sum_range_repr (hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype ha) k)
      (hpos.koornwinderOuterMeasure hμ a ha0 (ae_nonneg_eval_map_subtype ha) k) hu p (N-k+1) (by omega))
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc] at he
  change _ = p.eval₂ C (X 0)*S.lift k at he
  rw [← he]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  have hrn : r+k ≤ N := by have := Finset.mem_range.mp hr; omega
  let i : KoornwinderIndex N := ⟨⟨r+k,by omega⟩,⟨k,by change k < r+k+1; omega⟩⟩
  have hm : S.sectionFamily N i ∈ S.sectionSpan N := Submodule.subset_span (Set.mem_range_self i)
  change S.polynomial (r+k) k ∈ S.sectionSpan N at hm
  change (S.outer k r).eval₂ C (X 0)*S.lift k ∈ S.sectionSpan N
  simpa only [polynomial,Nat.add_sub_cancel] using hm

/-- Equal inner lifts make every source member lie in the target separated span. -/
theorem polynomial_mem_sectionSpan_of_lift_eq
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hpos' : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ'))
    (ha0 : a ≠ 0) (ha' : ∀ᵐ (x : D) ∂μ', 0 ≤ a.eval (x : ℝ)) (hL : S.lift=T.lift)
    {N n k : ℕ} (hn : n ≤ N) (hk : k ≤ n) : S.polynomial n k ∈ T.sectionSpan N := by
  classical
  let hu (i : ℕ) : IsUnit (T.outer k i).leadingCoeff :=
    isUnit_iff_ne_zero.mpr (T.outer_leadingCoeff_pos k i).ne'
  have he := (T.outer_orthogonal k).separated_expansion
    (hμ'.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype ha') k)
    (hpos'.koornwinderOuterMeasure hμ' a ha0 (ae_nonneg_eval_map_subtype ha') k) hu
    (Polynomial.aeval (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)) (T.lift k) (S.outer k) (n-k)
  change (S.outer k (n-k)).eval₂ C (X 0) * T.lift k = _ at he
  unfold polynomial
  rw [hL, he]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  have hrn : r+k ≤ N := by
    have := Finset.mem_range.mp hr
    omega
  let i : KoornwinderIndex N := ⟨⟨r+k, by omega⟩, ⟨k, by change k < r+k+1; omega⟩⟩
  have hmem : T.sectionFamily N i ∈ T.sectionSpan N :=
    Submodule.subset_span (Set.mem_range_self i)
  change T.polynomial (r+k) k ∈ T.sectionSpan N at hmem
  change (T.outer k r).eval₂ C (X 0) * T.lift k ∈ T.sectionSpan N
  simpa only [polynomial, Nat.add_sub_cancel] using hmem

/-- Every finite separated span is unchanged when only the outer sequences change. -/
theorem sectionSpan_eq_of_lift_eq
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hpos' : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ'))
    (ha0 : a ≠ 0) (ha : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ)) (ha' : ∀ᵐ (x : D) ∂μ', 0 ≤ a.eval (x : ℝ))
    (hL : S.lift=T.lift) (N : ℕ) : S.sectionSpan N = T.sectionSpan N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i,rfl⟩
    exact S.polynomial_mem_sectionSpan_of_lift_eq T hμ' hpos' ha0 ha' hL
      (by exact Nat.le_of_lt_succ i.1.isLt) (by exact Nat.le_of_lt_succ i.2.isLt)
  · apply Submodule.span_le.mpr
    rintro p ⟨i,rfl⟩
    exact T.polynomial_mem_sectionSpan_of_lift_eq S hμ hpos ha0 ha hL.symm
      (by exact Nat.le_of_lt_succ i.1.isLt) (by exact Nat.le_of_lt_succ i.2.isLt)

end MvPolynomial.KoornwinderSystem
