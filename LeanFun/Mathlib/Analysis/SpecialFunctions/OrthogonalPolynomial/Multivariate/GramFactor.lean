/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import LeanFun.Mathlib.LinearAlgebra.Matrix.OffsetSupport

/-!
# The canonical finite polynomial Gram factor

This factor is defined for an arbitrary positive polynomial pairing. No separated
target basis is assumed, which is essential when investigating necessity of
separation for uniform sparsity.
Reference: Gutleb–Olver–Slevinsky, measure modifications, Lemma 2.8.
-/

@[expose] public section
open MeasureTheory Module Matrix
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] {n : ℕ}
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis (Fin n) ℝ V)

/-- The unique positive upper triangular factor for an ordered polynomial basis. -/
noncomputable def integralGramFactor : Matrix (Fin n) (Fin n) ℝ :=
  (existsUnique_pos_upperTriangular_integralGram_factor μ hμ hpos b).choose

/-- The chosen factor is upper triangular, has positive diagonal, and factors the Gram matrix. -/
theorem integralGramFactor_spec :
    (integralGramFactor μ hμ hpos b).IsUpperTriangular ∧
      (∀ i, 0 < integralGramFactor μ hμ hpos b i i) ∧
      integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) =
        (integralGramFactor μ hμ hpos b).transpose * integralGramFactor μ hμ hpos b :=
  (existsUnique_pos_upperTriangular_integralGram_factor μ hμ hpos b).choose_spec.1

/-- Any concrete positive upper triangular factor identifies the canonical factor. -/
theorem integralGramFactor_eq (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsUpperTriangular) (hp : ∀ i, 0 < R i i)
    (hg : integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) = R.transpose*R) :
    integralGramFactor μ hμ hpos b = R :=
  ((existsUnique_pos_upperTriangular_integralGram_factor μ hμ hpos b).choose_spec.2
    R ⟨hR,hp,hg⟩).symm

/-- Support of the canonical factor can be verified by any positive triangular Gram factor. -/
theorem integralGramFactor_hasOffsetSupport_iff {G : Type*} [AddCommGroup G]
    (label : Fin n → G) (S : Finset G) :
    (integralGramFactor μ hμ hpos b).HasOffsetSupport label label S ↔
      ∃ R : Matrix (Fin n) (Fin n) ℝ, R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) = R.transpose*R ∧
        R.HasOffsetSupport label label S := by
  constructor
  · intro h
    have hs := integralGramFactor_spec μ hμ hpos b
    exact ⟨_,hs.1,hs.2.1,hs.2.2,h⟩
  · rintro ⟨R,hR,hp,hg,hs⟩
    rw [integralGramFactor_eq μ hμ hpos b R hR hp hg]
    exact hs

end MvPolynomial
