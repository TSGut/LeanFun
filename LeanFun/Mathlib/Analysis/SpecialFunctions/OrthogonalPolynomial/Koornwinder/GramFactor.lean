/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.OrdinarySpan
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Connection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramBilinear

/-!
# Gram factors on separated finite spans

Matching finite spans identify the mixed pairings with actual conversion
coefficients. Reference: Gutleb–Olver–Slevinsky, Lemma 2.8.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}

/-- A mixed pairing is the actual finite-span coordinate whenever the source lies in that span. -/
theorem connectionEntry_eq_sectionBasis_repr
    {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hρ : Continuous ρ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (N n k : ℕ) (hp : S.polynomial n k ∈ T.sectionSpan N) (i : KoornwinderIndex N) :
    S.connectionEntry T n k i.1 i.2 =
      (T.sectionBasis hμ' hν' hρ ha N).repr ⟨S.polynomial n k,hp⟩ i := by
  rw [T.sectionBasis_repr hμ' hν' hρ ha]
  exact integralInner_comm _ _ _

/-- Mixed pairings factor the source Gram section when the target span contains it. -/
theorem connectionEntry_gram
    {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hρ : Continuous ρ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ)) (N : ℕ)
    (hspan : ∀ i : KoornwinderIndex N, S.polynomial i.1 i.2 ∈ T.sectionSpan N) :
    integralGram (koornwinderMeasure ρ μ' ν') (S.sectionFamily N) =
      (Matrix.of (fun i j : KoornwinderIndex N =>
        S.connectionEntry T j.1 j.2 i.1 i.2)).transpose *
      Matrix.of (fun i j : KoornwinderIndex N => S.connectionEntry T j.1 j.2 i.1 i.2) := by
  classical
  let v (i : KoornwinderIndex N) : T.sectionSpan N := ⟨S.polynomial i.1 i.2,hspan i⟩
  have he := integralGram_eq_transpose_coordinates_mul _
    (hasFiniteMoments_koornwinderMeasure hμ' hν' hρ a ha)
    (T.sectionBasis hμ' hν' hρ ha N) (T.integralGram_sectionBasis hμ' hν' hρ ha N) v
  have hc : (T.sectionBasis hμ' hν' hρ ha N).toMatrix v =
      Matrix.of (fun i j : KoornwinderIndex N => S.connectionEntry T j.1 j.2 i.1 i.2) := by
    ext i j
    rw [Basis.toMatrix_apply, T.sectionBasis_repr hμ' hν' hρ ha]
    exact integralInner_comm _ _ _
  rw [hc] at he
  exact he

/-- Ordinary source and target systems automatically have matching degree sections. -/
theorem connectionEntry_gram_of_ordinary
    {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hρ : Continuous ρ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (hS : ∀ k, (S.lift k).totalDegree ≤ k) (hT : ∀ k, (T.lift k).totalDegree ≤ k) (N : ℕ) :
    integralGram (koornwinderMeasure ρ μ' ν') (S.sectionFamily N) =
      (Matrix.of (fun i j : KoornwinderIndex N =>
        S.connectionEntry T j.1 j.2 i.1 i.2)).transpose *
      Matrix.of (fun i j : KoornwinderIndex N => S.connectionEntry T j.1 j.2 i.1 i.2) := by
  apply S.connectionEntry_gram T hμ' hν' hρ ha N
  intro i
  rw [T.sectionSpan_eq_restrictTotalDegree hμ' hν' hρ ha hT N]
  apply (mem_restrictTotalDegree (Fin 2) N _).mpr
  exact (S.totalDegree_polynomial_le hS (Nat.le_of_lt_succ i.2.isLt)).trans
    (Nat.le_of_lt_succ i.1.isLt)

end MvPolynomial.KoornwinderSystem
