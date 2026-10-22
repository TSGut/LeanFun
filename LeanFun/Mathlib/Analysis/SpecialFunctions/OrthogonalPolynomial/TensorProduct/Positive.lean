/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Basis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Existence
public import LeanFun.Mathlib.LinearAlgebra.BilinearForm.PositiveBasis

/-! # Strict positivity of product polynomial pairings
Finite orthogonal tensor bases prove nondegeneracy of a product measure from
nondegeneracy of each factor. Reference: Dunkl--Xu, product measures.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- Positive orthogonal coordinate norms give a positive product polynomial pairing. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_pi_of_sequences (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n))) :
    HasPositiveDefiniteIntegral (Measure.pi μ) := by
  classical
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ (hμ i).isFiniteMeasure
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  let N := p.totalDegree
  let V := restrictTotalDegree σ ℝ N
  let b := tensorProductDegreeBasis μ P hμ hP hn N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  let B := (integralBilinForm (Measure.pi μ) (hasFiniteMoments_pi μ hμ)).restrict V
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 := by
    intro i j hij
    change integralInner (Measure.pi μ) ((hasFiniteMoments_pi μ hμ).pair (b i) (b j)) = 0
    have he : (fun t => i.1 t) ≠ (fun t => j.1 t) := by
      intro h
      exact hij (Subtype.ext (Finsupp.ext (fun t => congrFun h t)))
    have hz := integralInner_tensorProductPolynomial_eq_zero μ P hP
      (fun t => i.1 t) (fun t => j.1 t) he
    simpa only [integralInner, b, tensorProductDegreeBasis_apply] using hz
  have hn' : ∀ i, 0 < B (b i) (b i) := by
    intro i
    change 0 < integralInner (Measure.pi μ) ((hasFiniteMoments_pi μ hμ).pair (b i) (b i))
    have he := integralInner_tensorProductPolynomial μ
      (fun t => P t (i.1 t)) (fun t => P t (i.1 t))
      (fun t => (hμ t).integrable_mul _ _)
    have hp := Finset.prod_pos (fun t (_ : t ∈ Finset.univ) => hn t (i.1 t))
    rw [← he] at hp
    simpa only [integralInner, b, tensorProductDegreeBasis_apply] using hp
  have hm : p ∈ V := (mem_restrictTotalDegree σ N p).mpr (le_refl _)
  have hp' : (⟨p, hm⟩ : V) ≠ 0 := fun h ↦ hp (congrArg Subtype.val h)
  have h := B.apply_self_pos_of_orthogonal_basis b ho hn' hp'
  change 0 < integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) p p) at h
  rwa [integralInner_self] at h

/-- Products preserve finite-moment polynomial positivity, without support assumptions. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_pi (μ : σ → Measure ℝ)
    (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hpμ : ∀ i, Polynomial.HasPositiveDefiniteIntegral (μ i)) :
    HasPositiveDefiniteIntegral (Measure.pi μ) := by
  classical
  choose P hP using fun i ↦ Polynomial.exists_isOrthogonal (μ i) (hμ i) (hpμ i)
  apply hasPositiveDefiniteIntegral_pi_of_sequences μ P hμ hP
  intro i n
  rw [Polynomial.integralInner_self]
  exact hpμ i (P i n) ((P i).ne_zero n)

end MvPolynomial
