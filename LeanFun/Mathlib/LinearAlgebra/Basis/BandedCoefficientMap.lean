/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded

/-!
# Composition of banded coefficient maps

Bandwidths add under composition, including for infinite bases. All sums are
over finite coefficient supports. Reference: Olver–Townsend (2013), §2;
Gutleb–Olver–Slevinsky, polynomial measure conversion.
-/

public section
namespace Module.Basis
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Composing banded polynomial operators adds their lower and upper bandwidths. -/
theorem toMatrix_comp_isBanded (b : Basis ℕ R M) (c : Basis ℕ R N)
    (d : Basis ℕ R P) (L : M →ₗ[R] N) (K : N →ₗ[R] P)
    {l u l' u' : ℕ}
    (hL : (c.toMatrix (fun j => L (b j))).IsBanded l u)
    (hK : (d.toMatrix (fun j => K (c j))).IsBanded l' u') :
    (d.toMatrix (fun j => K (L (b j)))).IsBanded (l+l') (u+u') := by
  classical
  intro i j hij
  have he := c.coefficientMap_apply d K (c.repr (L (b j))) i
  have hc : c.coefficientMap d K (c.repr (L (b j))) = d.repr (K (L (b j))) := by
    simp [coefficientMap]
  rw [hc] at he
  rw [toMatrix_apply, he]
  apply Finset.sum_eq_zero
  intro k hk
  dsimp only
  by_cases h : j+l < k ∨ k+u < j
  · have hz := hL k j h
    change c.repr (L (b j)) k = 0 at hz
    rw [hz, mul_zero]
  · rw [hK i k (by omega), zero_mul]

/-- Conversion intertwines the coordinate representations of every endomorphism. -/
theorem coefficientMap_id_intertwines (b c : Basis ℕ R M) (L : M →ₗ[R] M) :
    (b.coefficientMap c LinearMap.id).comp (b.coefficientMap b L) =
      (c.coefficientMap c L).comp (b.coefficientMap c LinearMap.id) := by
  rw [coefficientMap_comp, coefficientMap_comp]
  simp

end Module.Basis
