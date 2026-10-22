/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Basis
public import LeanFun.Mathlib.LinearAlgebra.BilinearForm.PositiveBasis

/-!
# Strict positivity of Cartesian disk pairings

Finite orthonormal degree bases establish positivity for all nonzero polynomials.
Reference: Dunkl–Xu, Chapter 3.
-/

public section
open MeasureTheory Set Module
namespace MvPolynomial.CartesianDiskSystem

/-- An orthonormal Cartesian system makes its disk measure nondegenerate. -/
theorem hasPositiveDefiniteIntegral {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1) :
    HasPositiveDefiniteIntegral (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  classical
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  let N := p.totalDegree
  let V := restrictTotalDegree (Fin 2) ℝ N
  let b := S.degreeBasis hx hz N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  let B := (integralBilinForm (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))
    (hasFiniteMoments_cartesianDiskMeasure hx hz)).restrict V
  have he (i j) : B (b i) (b j) = if i=j then 1 else 0 := by
    exact congrArg (fun M => M i j) (S.integralGram_degreeBasis hx hz N)
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 := by
    intro i j hij
    rw [he,ite_eq_right hij]
  have hn : ∀ i, 0 < B (b i) (b i) := by
    intro i
    rw [he,ite_eq_left rfl]
    exact zero_lt_one
  have hm : p ∈ V := (mem_restrictTotalDegree (Fin 2) N p).mpr (le_refl _)
  have hp' : (⟨p,hm⟩ : V) ≠ 0 := by
    intro h
    exact hp (congrArg Subtype.val h)
  have hh := B.apply_self_pos_of_orthogonal_basis b ho hn hp'
  change 0 < integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) p p) at hh
  rwa [integralInner_self] at hh

end MvPolynomial.CartesianDiskSystem
