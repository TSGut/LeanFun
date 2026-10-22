/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Basis
public import LeanFun.Mathlib.LinearAlgebra.BilinearForm.PositiveBasis

/-!
# Positive definiteness of the disk polynomial integral

The orthogonal basis of each degree space transfers its positive norms to every
nonzero polynomial. Reference: Dunkl–Xu, Chapter 3.
-/

public section
open Module
namespace MvPolynomial

/-- Distinct exponent indices give orthogonal members of the finite disk basis. -/
theorem integralInner_dunklXuDegreeBasis_eq_zero {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) (hij : i ≠ j) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (dunklXuDegreeBasis hβ N i) (dunklXuDegreeBasis hβ N j)) = 0 := by
  simp only [integralInner, dunklXuDegreeBasis_apply]
  apply integral_mul_dunklXuDisk_eq_zero hβ (by omega) (by omega)
  intro h
  apply hij
  apply Subtype.ext
  have hn := congrArg Prod.fst h
  have hk := congrArg Prod.snd h
  ext a
  fin_cases a <;> dsimp at hn hk ⊢ <;> omega

/-- The disk measure is strictly positive definite on the full polynomial algebra. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_dunklXuDiskMeasure {β : ℝ} (hβ : -1 < β) :
    HasPositiveDefiniteIntegral (dunklXuDiskMeasure β) := by
  classical
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  let N := p.totalDegree
  let V := restrictTotalDegree (Fin 2) ℝ N
  let b := dunklXuDegreeBasis hβ N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  let B := (integralBilinForm (dunklXuDiskMeasure β)
    (hasFiniteMoments_dunklXuDiskMeasure hβ)).restrict V
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 := by
    intro i j hij
    exact integralInner_dunklXuDegreeBasis_eq_zero hβ N i j hij
  have hn : ∀ i, 0 < B (b i) (b i) := by
    intro i
    change 0 < integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (dunklXuDegreeBasis hβ N i) (dunklXuDegreeBasis hβ N i))
    rw [integralInner_self, dunklXuDegreeBasis_apply]
    exact integral_sq_dunklXuDisk_pos hβ _ _
  have hm : p ∈ V := (mem_restrictTotalDegree (Fin 2) N p).mpr (le_refl _)
  have hp' : (⟨p, hm⟩ : V) ≠ 0 := by
    intro h
    exact hp (congrArg Subtype.val h)
  have hh := B.apply_self_pos_of_orthogonal_basis b ho hn hp'
  change 0 < integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) p p) at hh
  rwa [integralInner_self] at hh

end MvPolynomial
