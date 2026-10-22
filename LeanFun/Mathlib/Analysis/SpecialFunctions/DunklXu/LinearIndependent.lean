/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Orthogonality
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Linear independence of Cartesian disk polynomials

Orthogonality and positive norms give independence without assuming a basis or
positive definiteness on the full polynomial space in advance.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- The degree blocks with increasing inner index form a linearly independent family. -/
theorem linearIndependent_dunklXuDisk {β : ℝ} (hβ : -1 < β) :
    LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n + 1) => dunklXuDisk β i.1 i.2) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (dunklXuDiskMeasure β) (hasFiniteMoments_dunklXuDiskMeasure hβ))
  · intro i j hij
    apply integral_mul_dunklXuDisk_eq_zero hβ (by omega) (by omega)
    intro h
    apply hij
    have hn := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    rcases i with ⟨n, k⟩
    rcases j with ⟨m, l⟩
    dsimp at hn hk
    subst m
    congr 1
    exact Fin.ext hk
  · intro i
    change integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) _ _) ≠ 0
    rw [integralInner_self]
    exact (integral_sq_dunklXuDisk_pos hβ i.1 i.2).ne'

end MvPolynomial
