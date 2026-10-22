/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Moments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Complete tensor-product polynomial degree bases
Product orthogonality and the monomial degree count give bases on every complete
total-degree section in any finite dimension. Reference: Dunkl--Xu, product bases.
-/

@[expose] public section
open MeasureTheory Polynomial Module
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- The tensor family belongs to the expected total-degree section. -/
noncomputable def tensorProductDegreeFamily (P : σ → Polynomial.Sequence ℝ) (N : ℕ)
    (d : {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) : restrictTotalDegree σ ℝ N :=
  ⟨tensorProductPolynomial (fun i ↦ P i (d.1 i)), (mem_restrictTotalDegree σ N _).mpr
    ((totalDegree_tensorProductPolynomial_le _).trans (by
      simpa [Polynomial.Sequence.natDegree_eq, Finsupp.sum_fintype] using d.2))⟩

/-- Positive tensor norms make the full product family linearly independent. -/
theorem tensorProductPolynomial_linearIndependent (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n))) :
    LinearIndependent ℝ (fun d : σ →₀ ℕ ↦ tensorProductPolynomial (fun i ↦ P i (d i))) := by
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ (hμ i).isFiniteMeasure
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (Measure.pi μ) (hasFiniteMoments_pi μ hμ))
  · intro d e hde
    apply integralInner_tensorProductPolynomial_eq_zero μ P hP d e
    intro h
    exact hde (Finsupp.ext (fun i ↦ congrFun h i))
  · intro d
    change integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) _ _) ≠ 0
    rw [integralInner_tensorProductPolynomial μ _ _ (fun i => (hμ i).integrable_mul _ _)]
    exact (Finset.prod_pos (fun i _ ↦ hn i (d i))).ne'

/-- Product orthogonal polynomials form a basis of each complete degree space. -/
noncomputable def tensorProductDegreeBasis (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n))) (N : ℕ) :
    Basis {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ (restrictTotalDegree σ ℝ N) := by
  classical
  let b : Basis {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree σ ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  have hi : LinearIndependent ℝ (tensorProductDegreeFamily P N) := by
    have h := (tensorProductPolynomial_linearIndependent μ P hμ hP hn).comp
      (fun d : {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦ d.1) Subtype.val_injective
    exact LinearIndependent.of_comp (restrictTotalDegree σ ℝ N).subtype h
  exact basisOfLinearIndependentOfCardEqFinrank' (tensorProductDegreeFamily P N)
    hi (Module.finrank_eq_card_basis b).symm

/-- The finite basis consists of the explicit coordinate products. -/
@[simp] theorem tensorProductDegreeBasis_apply (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n))) (N : ℕ)
    (d : {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (tensorProductDegreeBasis μ P hμ hP hn N d : MvPolynomial σ ℝ) =
      tensorProductPolynomial (fun i ↦ P i (d.1 i)) := by
  simp [tensorProductDegreeBasis, tensorProductDegreeFamily]

end MvPolynomial
