/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Coordinates in a finite orthogonal basis
Integral projection divides by the diagonal norm unless the basis is normalized.
Reference: standard orthogonal expansion, DLMF 18.2.
-/

public section
namespace LinearMap.BilinForm
open Module
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Coordinates in an orthogonal basis for a real bilinear form. -/
theorem basis_repr_eq_div (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V)
    (ho : ∀ i j, i ≠ j → B (b i) (b j) = 0)
    (hn : ∀ i, B (b i) (b i) ≠ 0) (p : V) (i : ι) :
    b.repr p i = B p (b i) / B (b i) (b i) := by
  classical
  apply (eq_div_iff (hn i)).2
  have he := congrArg (fun v ↦ B v (b i)) (b.sum_repr p)
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at he
  rw [Finset.sum_eq_single i] at he
  · exact he
  · intro j _ hji
    rw [ho j i hji, mul_zero]
  · simp

end LinearMap.BilinForm
