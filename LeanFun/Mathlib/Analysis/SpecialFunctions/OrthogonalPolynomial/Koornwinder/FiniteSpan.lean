/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Moments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Finite separated spans

The cutoff is on outer degree plus inner degree. Generalised families retain
this filtration even when it differs from total degree. Reference: Dunkl–Xu,
§2.6.1; Gutleb–Olver–Slevinsky, finite Gram conversion.
-/

@[expose] public section
open MeasureTheory Polynomial Module
namespace MvPolynomial
variable {D : Set ℝ}

/-- Valid separated labels through n=N; n is not assumed to be total degree. -/
abbrev KoornwinderIndex (N : ℕ) := (n : Fin (N+1)) × Fin (n.val+1)

namespace KoornwinderSystem
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} (S : KoornwinderSystem a ρ μ ν)

/-- The family on a complete finite separated section. -/
noncomputable def sectionFamily (N : ℕ) (i : KoornwinderIndex N) :
    MvPolynomial (Fin 2) ℝ := S.polynomial i.1 i.2

/-- The finite span used for generalised Koornwinder sections. -/
noncomputable def sectionSpan (N : ℕ) : Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  Submodule.span ℝ (Set.range (S.sectionFamily N))

variable (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hρ : Continuous ρ) (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ))
include hμ hν hρ ha

/-- Every finite separated family is linearly independent. -/
theorem linearIndependent_sectionFamily (N : ℕ) :
    LinearIndependent ℝ (S.sectionFamily N) := by
  let := hμ.isFiniteMeasure_subtype
  let := hν.isFiniteMeasure
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (koornwinderMeasure ρ μ ν)
      (hasFiniteMoments_koornwinderMeasure hμ hν hρ a ha))
  · intro i j hij
    apply S.integralInner_polynomial_eq_zero hρ ha (by omega) (by omega)
    intro he
    apply hij
    have hn : i.1=j.1 := Fin.ext (congrArg Prod.fst he)
    rcases i with ⟨n,k⟩
    rcases j with ⟨m,l⟩
    dsimp at hn
    subst m
    congr 1
    exact Fin.ext (congrArg Prod.snd he)
  · intro i
    change integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) _ _) ≠ 0
    simpa only [sectionFamily] using (S.integralInner_polynomial_self hρ ha i.1 i.2).trans_ne one_ne_zero


/-- The explicit separated family is a basis of its finite span. -/
noncomputable def sectionBasis (N : ℕ) : Basis (KoornwinderIndex N) ℝ (S.sectionSpan N) :=
  Basis.span (S.linearIndependent_sectionFamily hμ hν hρ ha N)

/-- The span basis consists of the original separated polynomials. -/
@[simp] theorem sectionBasis_apply (N : ℕ) (i : KoornwinderIndex N) :
    (S.sectionBasis hμ hν hρ ha N i : MvPolynomial (Fin 2) ℝ) = S.polynomial i.1 i.2 := by
  exact Basis.coe_span_apply _ i

/-- Each finite separated basis has identity Gram matrix. -/
theorem integralGram_sectionBasis (N : ℕ) :
    integralGram (koornwinderMeasure ρ μ ν)
      (fun i => (S.sectionBasis hμ hν hρ ha N i : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  let := hμ.isFiniteMeasure_subtype
  let := hν.isFiniteMeasure
  ext i j
  simp only [integralGram, sectionBasis_apply, Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    rw [S.integralInner_polynomial_self hρ ha, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    apply S.integralInner_polynomial_eq_zero hρ ha (by omega) (by omega)
    intro he
    apply hij
    have hn : i.1=j.1 := Fin.ext (congrArg Prod.fst he)
    rcases i with ⟨n,k⟩
    rcases j with ⟨m,l⟩
    dsimp at hn
    subst m
    congr 1
    exact Fin.ext (congrArg Prod.snd he)

/-- Coordinates in the finite span are integral pairings. -/
theorem sectionBasis_repr (N : ℕ) (p : S.sectionSpan N) (i : KoornwinderIndex N) :
    (S.sectionBasis hμ hν hρ ha N).repr p i =
      integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial i.1 i.2) p) := by
  rw [basis_repr_eq_integralInner _ (hasFiniteMoments_koornwinderMeasure hμ hν hρ a ha)
    _ (S.integralGram_sectionBasis hμ hν hρ ha N)]
  simp only [integralInner, sectionBasis_apply]

end KoornwinderSystem
end MvPolynomial
