/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor

/-!
# Finite multivariate polynomial Gram factors

The construction takes an ordered basis of any finite polynomial subspace.
It imposes no connected-support or rectangular-domain restriction. Basis ordering
is an input, including the ordering within each total degree.

Reference: Gutleb–Olver–Slevinsky, measure modifications, Lemma 2.8;
Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Module Matrix
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] {n : ℕ}

/-- The integral Gram matrix, without installing a measure-dependent global
inner product instance on polynomials. -/
noncomputable def integralGram {ι : Type*} (μ : Measure (σ → ℝ)) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i j, Integrable (fun x => eval x (P i) * eval x (P j)) μ := by
      intro i j
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    Matrix ι ι ℝ := fun i j => integralInner μ (IntegrablePair.of μ (P i) (P j))

/-- An ordered basis of any finite multivariate polynomial subspace has a unique
positive-diagonal upper triangular Gram factor for the supplied measure. -/
theorem existsUnique_pos_upperTriangular_integralGram_factor
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis (Fin n) ℝ V) :
    ∃! R : Matrix (Fin n) (Fin n) ℝ,
      R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) = R.transpose * R := by
  let core := integralInnerProductCore μ hμ hpos
  let : NormedAddCommGroup (MvPolynomial σ ℝ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (MvPolynomial σ ℝ) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (MvPolynomial σ ℝ))
  obtain ⟨R, hR, hp, hg⟩ := InnerProductSpace.exists_pos_upperTriangular_gram_factor b
  refine ⟨R, ⟨hR, hp, hg⟩, ?_⟩
  rintro S ⟨hS, hSp, hSg⟩
  exact Matrix.eq_of_pos_upperTriangular_gram_eq hS hR hSp hp (hSg.symm.trans hg)

/-- Every ordered finite polynomial basis admits orthonormalization with an
upper triangular, positive-diagonal connection matrix. -/
theorem exists_orthonormal_pos_upperTriangular_basis
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis (Fin n) ℝ V) :
    ∃ q : Basis (Fin n) ℝ V,
      integralGram μ (fun i => (q i : MvPolynomial σ ℝ)) = 1 ∧
        (q.toMatrix b).IsUpperTriangular ∧ (∀ i, 0 < q.toMatrix b i i) := by
  let core := integralInnerProductCore μ hμ hpos
  let : NormedAddCommGroup (MvPolynomial σ ℝ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (MvPolynomial σ ℝ) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (MvPolynomial σ ℝ))
  obtain ⟨q, ht, hp⟩ := InnerProductSpace.exists_orthonormalBasis_pos_upperTriangular b
  exact ⟨q.toBasis, Matrix.gram_eq_one_iff_orthonormal.mpr q.orthonormal, ht, hp⟩

/-- The change of basis to any orthonormal polynomial basis factors the
modified-measure Gram matrix, in any finite number of variables. -/
theorem integralGram_eq_transpose_toMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (q b : Basis ι ℝ V)
    (hq : integralGram μ (fun i => (q i : MvPolynomial σ ℝ)) = 1) :
    integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) =
      (q.toMatrix b).transpose * q.toMatrix b := by
  let core := integralInnerProductCore μ hμ hpos
  let : NormedAddCommGroup (MvPolynomial σ ℝ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (MvPolynomial σ ℝ) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (MvPolynomial σ ℝ))
  have ho : Orthonormal ℝ q := Matrix.gram_eq_one_iff_orthonormal.mp hq
  change Matrix.gram ℝ b = _
  simpa only [Basis.toBasis_toOrthonormalBasis] using
    InnerProductSpace.gram_eq_transpose_toMatrix_mul (q.toOrthonormalBasis ho) b

/-- Coordinates in an orthonormal polynomial basis are integral pairings. -/
theorem basis_repr_eq_integralInner {ι : Type*} [DecidableEq ι]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (q : Basis ι ℝ V)
    (hq : integralGram μ (fun i => (q i : MvPolynomial σ ℝ)) = 1)
    (v : V) (i : ι) : q.repr v i = integralInner μ (IntegrablePair.of μ (q i) v) := by
  have hL : q.coord i = (integralBilinForm μ hμ).restrict V (q i) := by
    apply q.ext
    intro j
    change q.repr (q j) i = integralInner μ (IntegrablePair.of μ (q i) (q j))
    have hh : integralInner μ (IntegrablePair.of μ (q i) (q j)) = if i = j then 1 else 0 := by
      simpa only [integralGram, Matrix.one_apply] using congrArg (fun M => M i j) hq
    rw [Basis.repr_self, hh]
    simp [Finsupp.single_apply, eq_comm]
  exact congrArg (fun L => L v) hL

end MvPolynomial
