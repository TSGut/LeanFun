/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.BandedCoefficientMap

/-! # Exact finite sections of coefficient operators
Input support determines the required column count. Lower bandwidth determines
how many output rows retain the full result; a square truncation is not assumed
exact. Reference: Olver--Townsend (2013), Section 3.
-/

public section
namespace Module.Basis
variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- For input supported in the first `N` columns, every output coefficient is an
ordinary finite matrix sum. This also describes any chosen rectangular section. -/
theorem coefficientMap_apply_range (b : Basis ℕ R M) (c : Basis ℕ R P)
    (L : M →ₗ[R] P) (v : ℕ →₀ R) {N : ℕ}
    (hv : ∀ j ∈ v.support, j < N) (i : ℕ) :
    b.coefficientMap c L v i = ∑ j ∈ Finset.range N, c.toMatrix (fun j ↦ L (b j)) i j * v j := by
  classical
  rw [coefficientMap_apply, Finsupp.sum]
  apply Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hv j hj))
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj, mul_zero]

/-- With lower bandwidth `l`, the first `N+l` rows retain every output coefficient
of an input supported in the first `N` columns. No square-section assumption. -/
theorem coefficientMap_eq_zero_of_bandwidth (b : Basis ℕ R M) (c : Basis ℕ R P)
    (L : M →ₗ[R] P) {l u : ℕ}
    (hL : (c.toMatrix (fun j ↦ L (b j))).IsBanded l u)
    (v : ℕ →₀ R) {N : ℕ} (hv : ∀ j ∈ v.support, j < N)
    {i : ℕ} (hi : N + l ≤ i) : b.coefficientMap c L v i = 0 := by
  rw [coefficientMap_apply_range b c L v hv]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hL i j (Or.inl (by have := Finset.mem_range.mp hj; omega)), zero_mul]

end Module.Basis
