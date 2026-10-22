/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram

/-!
# Finite polynomial integral projections

An orthonormal basis of a finite polynomial subspace defines a symmetric
projection on the entire polynomial algebra. This supplies exact degree
truncations for padded multiplication identities.
Reference: Dunkl–Xu, orthogonal polynomial projections.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial
variable {σ ι : Type*} [Fintype σ] [Fintype ι]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    {V : Submodule ℝ (MvPolynomial σ ℝ)} (b : Basis ι ℝ V)

/-- Finite integral projection, defined on all polynomials. -/
noncomputable def integralProjection : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun p := ∑ i, (integralBilinForm μ hμ (b i) p) • (b i : MvPolynomial σ ℝ)
  map_add' p q := by simp only [map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c p := by simp only [map_smul,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

/-- The projection is symmetric for the integral pairing. -/
theorem integralProjection_symmetric (p q : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ (integralProjection μ hμ b p) q) =
      integralInner μ (IntegrablePair.of μ p (integralProjection μ hμ b q)) := by
  change integralBilinForm μ hμ (∑ i, integralBilinForm μ hμ (b i) p • (b i : MvPolynomial σ ℝ)) q =
    integralBilinForm μ hμ p (∑ i, integralBilinForm μ hμ (b i) q • (b i : MvPolynomial σ ℝ))
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change integralInner μ (IntegrablePair.of μ (b i) p) * integralInner μ (IntegrablePair.of μ (b i) q) =
    integralInner μ (IntegrablePair.of μ (b i) q) * integralInner μ (IntegrablePair.of μ p (b i))
  rw [integralInner_comm μ p]
  ring

/-- An orthonormal basis makes the integral projection fix its subspace pointwise. -/
theorem integralProjection_eq_self [DecidableEq ι]
    (hb : integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) = 1) (p : V) :
    integralProjection μ hμ b p = p := by
  have he := congrArg (fun v : V => (v : MvPolynomial σ ℝ)) (b.sum_repr p)
  simp only [Submodule.coe_sum,Submodule.coe_smul] at he
  change (∑ i, integralInner μ (IntegrablePair.of μ (b i) p) • (b i : MvPolynomial σ ℝ)) = p
  simpa only [basis_repr_eq_integralInner μ hμ b hb] using he

/-- A degree-space projection fixes every polynomial within its cutoff. -/
theorem integralProjection_eq_self_of_totalDegree_le [DecidableEq ι] (N : ℕ)
    (b : Basis ι ℝ (restrictTotalDegree σ ℝ N))
    (hb : integralGram μ (fun i => (b i : MvPolynomial σ ℝ)) = 1)
    (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ N) :
    integralProjection μ hμ b p = p :=
  integralProjection_eq_self μ hμ b hb ⟨p,(mem_restrictTotalDegree σ N p).mpr hp⟩

end MvPolynomial
