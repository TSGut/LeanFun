/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Gram conversion using only the finite target space

Orthonormality on the finite subspace suffices; global positivity is unnecessary.
Reference: Gutleb–Olver–Slevinsky, Lemma 2.8.
-/

public section
open MeasureTheory Module
namespace MvPolynomial

/-- A finite orthonormal target basis factors Gram matrices using only finite moments. -/
theorem integralGram_eq_transpose_toMatrix_mul_of_gram_eq_one
    {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (q b : Basis ι ℝ V)
    (hq : integralGram μ (fun i => (q i : MvPolynomial σ ℝ)) = 1) :
    integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) =
      (q.toMatrix b).transpose * q.toMatrix b := by
  let B := (integralBilinForm μ hμ).restrict V
  have he := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix q b B
  have ht (c : Basis ι ℝ V) : LinearMap.BilinForm.toMatrix c B =
      integralGram μ (fun i => (c i : MvPolynomial σ ℝ)) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hq' : LinearMap.BilinForm.toMatrix q B = 1 := (ht q).trans hq
  rw [hq', Matrix.mul_one] at he
  rw [ht b] at he
  exact he.symm

/-- Gram factorization for any finite family lying in an orthonormal target space. -/
theorem integralGram_eq_transpose_coordinates_mul
    {σ ι κ : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (q : Basis ι ℝ V)
    (hq : integralGram μ (fun i => (q i : MvPolynomial σ ℝ)) = 1) (v : κ → V) :
    integralGram μ (fun i => (v i : MvPolynomial σ ℝ)) =
      (q.toMatrix v).transpose * q.toMatrix v := by
  let B := (integralBilinForm μ hμ).restrict V
  have ht : LinearMap.BilinForm.toMatrix q B = 1 := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change integralInner μ (IntegrablePair.of μ (q i) (q j)) = _
    exact congrArg (fun M => M i j) hq
  ext i j
  have he := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec q B (v i) (v j)
  rw [ht, Matrix.one_mulVec] at he
  change integralInner μ (IntegrablePair.of μ (v i) (v j)) = _ at he
  simpa only [integralGram, Matrix.mul_apply, Matrix.transpose_apply,
    Basis.toMatrix_apply, dotProduct, Basis.equivFun_apply] using he

end MvPolynomial
