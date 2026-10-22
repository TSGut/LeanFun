/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.FiniteSpan
public import LeanFun.Mathlib.Algebra.MvPolynomial.SeparatedIndex
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ordinary Koornwinder spans are total-degree spaces

The explicit lift-degree hypothesis is what distinguishes ordinary from
unrestricted-scale families. Reference: Dunkl–Xu, §2.6.1.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} (S : KoornwinderSystem a ρ μ ν)

/-- Degree-compatible lifts identify separated finite spans with total-degree spaces. -/
theorem sectionSpan_eq_restrictTotalDegree
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ))
    (hlift : ∀ k, (S.lift k).totalDegree ≤ k) (N : ℕ) :
    S.sectionSpan N = restrictTotalDegree (Fin 2) ℝ N := by
  have hle : S.sectionSpan N ≤ restrictTotalDegree (Fin 2) ℝ N := by
    apply Submodule.span_le.mpr
    rintro p ⟨i,rfl⟩
    apply (mem_restrictTotalDegree (Fin 2) N _).mpr
    exact (S.totalDegree_polynomial_le hlift (by exact Nat.le_of_lt_succ i.2.isLt)).trans
      (Nat.le_of_lt_succ i.1.isLt)
  let b : Basis (KoornwinderIndex N) ℝ (restrictTotalDegree (Fin 2) ℝ N) :=
    (basisRestrictSupport ℝ _).reindex (separatedIndexEquiv N).symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [Module.finrank_eq_card_basis (S.sectionBasis hμ hν hρ ha N),
    Module.finrank_eq_card_basis b]

end MvPolynomial.KoornwinderSystem
