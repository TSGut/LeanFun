/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.GramFactor
public import LeanFun.Mathlib.LinearAlgebra.Matrix.OffsetSupport

/-!
# Composition through a separated intermediate family

Exact expansion in the intermediate finite span gives exact multiplication of
connection sections. Compatible support sets then add without further fill-in.
Reference: Gutleb–Olver–Slevinsky, polynomial measure conversion.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}

/-- Separated connection sections compose exactly through an intermediate span. -/
theorem connectionEntry_comp
    {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ} {μ'' : Measure D} {ν'' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    (U : KoornwinderSystem a ρ μ'' ν'')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hμ'' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ'')) (hν'' : Polynomial.HasFiniteMoments ν'')
    (hρ : Continuous ρ) (ha' : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (ha'' : ∀ᵐ x ∂μ'', ρ x^2 = a.eval (x : ℝ)) (N : ℕ)
    (hspan : ∀ i : KoornwinderIndex N, S.polynomial i.1 i.2 ∈ T.sectionSpan N) :
    Matrix.of (fun i j : KoornwinderIndex N => S.connectionEntry U j.1 j.2 i.1 i.2) =
      Matrix.of (fun i j : KoornwinderIndex N => T.connectionEntry U j.1 j.2 i.1 i.2) *
        Matrix.of (fun i j : KoornwinderIndex N => S.connectionEntry T j.1 j.2 i.1 i.2) := by
  classical
  ext i j
  let v : T.sectionSpan N := ⟨S.polynomial j.1 j.2,hspan j⟩
  let L := ((integralBilinForm (koornwinderMeasure ρ μ'' ν'')
    (hasFiniteMoments_koornwinderMeasure hμ'' hν'' hρ a ha''))
    (U.polynomial i.1 i.2)).comp (T.sectionSpan N).subtype
  have he := congrArg L ((T.sectionBasis hμ' hν' hρ ha' N).sum_repr v)
  simp only [map_sum,map_smul,smul_eq_mul] at he
  have hc (k : KoornwinderIndex N) :
      (T.sectionBasis hμ' hν' hρ ha' N).repr v k =
        S.connectionEntry T j.1 j.2 k.1 k.2 :=
    (S.connectionEntry_eq_sectionBasis_repr T hμ' hν' hρ ha' N _ _ (hspan j) k).symm
  have ht (k : KoornwinderIndex N) : L (T.sectionBasis hμ' hν' hρ ha' N k) =
      T.connectionEntry U k.1 k.2 i.1 i.2 := by
    change integralInner (koornwinderMeasure ρ μ'' ν'') (IntegrablePair.of (koornwinderMeasure ρ μ'' ν'') (U.polynomial i.1 i.2) (T.sectionBasis hμ' hν' hρ ha' N k)) = _
    rw [T.sectionBasis_apply]
    exact integralInner_comm _ _ _
  have hv : L v = S.connectionEntry U j.1 j.2 i.1 i.2 := integralInner_comm _ _ _
  simp_rw [hc,ht,hv] at he
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact he.symm.trans (Finset.sum_congr rfl (fun k _ => mul_comm _ _))

end MvPolynomial.KoornwinderSystem
