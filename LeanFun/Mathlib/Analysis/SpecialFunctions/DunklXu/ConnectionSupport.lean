/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Basis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Connection

/-!
# Exact support of the Cartesian disk connection matrix

The matrix is expressed through the existing polynomial bases, on finitely
supported coefficients. Reference: Dunkl–Xu, disk parameter raising.
-/

public section
namespace MvPolynomial

/-- Coordinates of a valid disk polynomial in its own basis. -/
theorem dunklXuBasis_repr_disk {β : ℝ} (hβ : -1 < β) (n k : ℕ) (hk : k ≤ n)
    (i : Σ n : ℕ, Fin (n + 1)) :
    (dunklXuBasis hβ).repr (dunklXuDisk β n k) i =
      if i = ⟨n, ⟨k, by omega⟩⟩ then 1 else 0 := by
  classical
  have h := congrArg (fun c => c i) ((dunklXuBasis hβ).repr_self ⟨n, ⟨k, by omega⟩⟩)
  simpa [Finsupp.single_apply, eq_comm] using h

/-- A coordinate outside the four allowed degree/inner-index positions is zero. -/
theorem dunklXuBasis_raise_repr_eq_zero {β : ℝ} (hβ : -1 < β)
    (i j : Σ n : ℕ, Fin (n + 1))
    (hout : ¬ ((i.1 = j.1 ∨ i.1 + 2 = j.1) ∧
      ((i.2 : ℕ) = j.2 ∨ (i.2 : ℕ) + 2 = j.2))) :
    (dunklXuBasis (show -1 < β + 1 by linarith)).repr
      (dunklXuDisk β j.1 j.2) i = 0 := by
  classical
  let hβ' : -1 < β + 1 := by linarith
  let L := (dunklXuBasis hβ').repr
  obtain ⟨a, b, c, d, _, he, hb, hcd⟩ := exists_dunklXuDisk_raise hβ j.1 j.2 (by omega)
  have hz (n k : ℕ) (hk : k ≤ n)
      (hn : n = j.1 ∨ n + 2 = j.1) (hk' : k = j.2 ∨ k + 2 = j.2) :
      L (dunklXuDisk (β + 1) n k) i = 0 := by
    rw [dunklXuBasis_repr_disk hβ' n k hk]
    apply ite_eq_right
    intro hi
    apply hout
    subst i
    exact ⟨hn, hk'⟩
  have h₀ := hz j.1 j.2 (by omega) (Or.inl rfl) (Or.inl rfl)
  have h₁ : b * L (dunklXuDisk (β + 1) (j.1 - 2) j.2) i = 0 := by
    by_cases hj : j.1 < (j.2 : ℕ) + 2
    · rw [hb hj, zero_mul]
    · rw [hz _ _ (by omega) (Or.inr (by omega)) (Or.inl rfl), mul_zero]
  have h₂ : c * L (dunklXuDisk (β + 1) j.1 (j.2 - 2)) i = 0 := by
    by_cases hk : (j.2 : ℕ) < 2
    · rw [(hcd hk).1, zero_mul]
    · rw [hz _ _ (by omega) (Or.inl rfl) (Or.inr (by omega)), mul_zero]
  have h₃ : d * L (dunklXuDisk (β + 1) (j.1 - 2) (j.2 - 2)) i = 0 := by
    by_cases hk : (j.2 : ℕ) < 2
    · rw [(hcd hk).2, zero_mul]
    · rw [hz _ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)), mul_zero]
  have h := congrArg (fun p => L p i) he
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
  rw [h₀, h₁, h₂, h₃, mul_zero, zero_add, zero_add, add_zero] at h
  exact h

/-- The diagonal coefficient of the disk raising matrix is positive. -/
theorem dunklXuBasis_raise_repr_self_pos {β : ℝ} (hβ : -1 < β)
    (j : Σ n : ℕ, Fin (n + 1)) :
    0 < (dunklXuBasis (show -1 < β + 1 by linarith)).repr
      (dunklXuDisk β j.1 j.2) j := by
  classical
  let hβ' : -1 < β + 1 := by linarith
  let L := (dunklXuBasis hβ').repr
  obtain ⟨a, b, c, d, ha, he, hb, hcd⟩ := exists_dunklXuDisk_raise hβ j.1 j.2 (by omega)
  have hz (n k : ℕ) (hk : k ≤ n) (hne : n ≠ j.1 ∨ k ≠ (j.2 : ℕ)) :
      L (dunklXuDisk (β + 1) n k) j = 0 := by
    rw [dunklXuBasis_repr_disk hβ' n k hk]
    apply ite_eq_right
    intro hi
    have hn := congrArg Sigma.fst hi
    have hk' := congrArg (fun i : Σ n : ℕ, Fin (n + 1) => (i.2 : ℕ)) hi
    rcases hne with h | h
    · exact h hn.symm
    · exact h hk'.symm
  have h₀ : L (dunklXuDisk (β + 1) j.1 j.2) j = 1 := by
    rw [dunklXuBasis_repr_disk hβ' _ _ (by omega)]
    simp
  have h₁ : b * L (dunklXuDisk (β + 1) (j.1 - 2) j.2) j = 0 := by
    by_cases hj : j.1 < (j.2 : ℕ) + 2
    · rw [hb hj, zero_mul]
    · rw [hz _ _ (by omega) (Or.inl (by omega)), mul_zero]
  have h₂ : c * L (dunklXuDisk (β + 1) j.1 (j.2 - 2)) j = 0 := by
    by_cases hk : (j.2 : ℕ) < 2
    · rw [(hcd hk).1, zero_mul]
    · rw [hz _ _ (by omega) (Or.inr (by omega)), mul_zero]
  have h₃ : d * L (dunklXuDisk (β + 1) (j.1 - 2) (j.2 - 2)) j = 0 := by
    by_cases hk : (j.2 : ℕ) < 2
    · rw [(hcd hk).2, zero_mul]
    · rw [hz _ _ (by omega) (Or.inl (by omega)), mul_zero]
  have h := congrArg (fun p => L p j) he
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
  rw [h₀, h₁, h₂, h₃, mul_one, add_zero, add_zero, add_zero] at h
  change 0 < L (dunklXuDisk β j.1 j.2) j
  rw [h]
  exact ha

end MvPolynomial
