/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.OrdinarySpan
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.MultiplicationCases

/-!
# Exact coordinate action in ordinary Koornwinder bases

One degree of padding represents coordinate multiplication exactly. The entry
support theorems therefore describe actual operators on finite expansions.
Reference: Dunkl–Xu, multivariate three-term recurrence; Olver–Townsend (2013).
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} (S : KoornwinderSystem a ρ μ ν)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (hlift : ∀ k, (S.lift k).totalDegree ≤ k)
include hμ hν hρ ha hlift

/-- Ordinary coordinate multiplication lands in the section with one extra degree. -/
theorem coordinate_mul_mem_sectionSpan (coord : Fin 2) (N : ℕ) (i : KoornwinderIndex N) :
    X coord*S.polynomial i.1 i.2 ∈ S.sectionSpan (N+1) := by
  rw [S.sectionSpan_eq_restrictTotalDegree hμ hν hρ ha hlift]
  apply (mem_restrictTotalDegree (Fin 2) (N+1) _).mpr
  have hp := S.totalDegree_polynomial_le hlift (Nat.le_of_lt_succ i.2.isLt)
  have hm := totalDegree_mul (X coord : MvPolynomial (Fin 2) ℝ) (S.polynomial i.1 i.2)
  rw [totalDegree_X] at hm
  have := i.1.isLt
  omega

/-- The finite expansion has the integral multiplication entries as its coefficients. -/
theorem coordinate_mul_eq_sum (coord : Fin 2) (N : ℕ) (i : KoornwinderIndex N) :
    X coord*S.polynomial i.1 i.2 = ∑ j : KoornwinderIndex (N+1),
      S.multiplicationEntry coord i.1 i.2 j.1 j.2 • S.polynomial j.1 j.2 := by
  classical
  let p : S.sectionSpan (N+1) :=
    ⟨X coord*S.polynomial i.1 i.2,S.coordinate_mul_mem_sectionSpan hμ hν hρ ha hlift coord N i⟩
  have he := congrArg (fun q : S.sectionSpan (N+1) => (q : MvPolynomial (Fin 2) ℝ))
    ((S.sectionBasis hμ hν hρ ha (N+1)).sum_repr p)
  simp only [Submodule.coe_sum, Submodule.coe_smul, sectionBasis_apply,
    S.sectionBasis_repr hμ hν hρ ha] at he
  have input : KoornwinderMeasureInput ρ μ ν := .ofMoments hν hρ
  have hM := S.hasFiniteMoments hρ ha
  have hc (j : KoornwinderIndex (N+1)) :
      integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial j.1 j.2) p (h := hM.integrable_mul _ _)) =
        S.multiplicationEntry coord i.1 i.2 j.1 j.2 (hi := hM.integrable_mul _ _) := integralInner_comm _ _ _
  simp_rw [hc] at he
  exact he.symm

end MvPolynomial.KoornwinderSystem
