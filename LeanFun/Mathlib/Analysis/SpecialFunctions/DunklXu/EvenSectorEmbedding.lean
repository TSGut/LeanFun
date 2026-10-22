/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPencilSection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.OrderedBasis

/-! # Complete even-sector embedding in the ordered disk basis
The even-even section includes every even pair through degree 2r, with all
lower degrees preceding the boundary block. Reference: Cartesian disk ordering.
-/

@[expose] public section
namespace MvPolynomial

/-- The half-degree coordinates stay within the complete section. -/
theorem dunklXuEvenBlockCoordinates_le (r : ℕ) (i : DunklXuEvenInterior r ⊕ Fin (r + 1)) :
    (dunklXuEvenBlockCoordinates r i).1 + (dunklXuEvenBlockCoordinates r i).2 ≤ r := by
  cases i with
  | inl i => exact Nat.le_of_lt i.2
  | inr i => dsimp [dunklXuEvenBlockCoordinates]; omega

/-- Embed the complete even sector into the full finite ordering. -/
noncomputable def dunklXuEvenSectorEmbedding (r : ℕ)
    (i : DunklXuEvenInterior r ⊕ Fin (r + 1)) : Fin (Fintype.card (DiskDegreeIndex (2 * r))) :=
  (diskDegreeOrder (2 * r)).symm (diskDegreeIndex (2 * r)
    (2 * (dunklXuEvenBlockCoordinates r i).1) (2 * (dunklXuEvenBlockCoordinates r i).2)
    (by have := dunklXuEvenBlockCoordinates_le r i; omega))

@[simp] theorem diskDegreeOrder_evenSectorEmbedding (r : ℕ)
    (i : DunklXuEvenInterior r ⊕ Fin (r + 1)) :
    ((diskDegreeOrder (2 * r)) (dunklXuEvenSectorEmbedding r i)).1 =
      Finsupp.single 0 (2 * (dunklXuEvenBlockCoordinates r i).1) +
      Finsupp.single 1 (2 * (dunklXuEvenBlockCoordinates r i).2) := by
  simp [dunklXuEvenSectorEmbedding, diskDegreeIndex]

/-- Distinct even-sector indices remain distinct in the full ordering. -/
theorem dunklXuEvenSectorEmbedding_injective (r : ℕ) :
    Function.Injective (dunklXuEvenSectorEmbedding r) := by
  intro i j h
  have h0 := congrArg (fun t ↦ ((diskDegreeOrder (2 * r)) t).1 0) h
  have h1 := congrArg (fun t ↦ ((diskDegreeOrder (2 * r)) t).1 1) h
  simp only [diskDegreeOrder_evenSectorEmbedding, Finsupp.add_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add] at h0 h1
  apply dunklXuEvenBlockCoordinates_injective r
  exact Prod.ext (by omega) (by omega)

/-- Every even-even index occurs in this sector enumeration. -/
theorem dunklXuEvenSectorEmbedding_covers (r : ℕ)
    (i : Fin (Fintype.card (DiskDegreeIndex (2 * r))))
    (h0 : ((diskDegreeOrder (2 * r) i).1 0) % 2 = 0)
    (h1 : ((diskDegreeOrder (2 * r) i).1 1) % 2 = 0) :
    i ∈ Set.range (dunklXuEvenSectorEmbedding r) := by
  let d := diskDegreeOrder (2 * r) i
  have hd : d.1 0 + d.1 1 ≤ 2 * r := by
    simpa only [sum_exponents_fin_two] using d.2
  have h0' : d.1 0 % 2 = 0 := h0
  have h1' : d.1 1 % 2 = 0 := h1
  have ha : 2 * (d.1 0 / 2) = d.1 0 := by omega
  have hb : 2 * (d.1 1 / 2) = d.1 1 := by omega
  have hs : d.1 0 / 2 + d.1 1 / 2 ≤ r := by omega
  suffices ∃ j, dunklXuEvenBlockCoordinates r j = (d.1 0 / 2, d.1 1 / 2) by
    obtain ⟨j, hj⟩ := this
    refine ⟨j, (diskDegreeOrder (2 * r)).injective ?_⟩
    apply DiskDegreeIndex.ext
    rw [diskDegreeOrder_evenSectorEmbedding, hj]
    ext t
    fin_cases t
    · simpa [d] using ha
    · simpa [d] using hb
  by_cases he : d.1 0 / 2 + d.1 1 / 2 < r
  · exact ⟨Sum.inl ⟨(⟨d.1 0 / 2, by omega⟩, ⟨d.1 1 / 2, by omega⟩), he⟩, rfl⟩
  · refine ⟨Sum.inr ⟨d.1 1 / 2, by omega⟩, ?_⟩
    dsimp [dunklXuEvenBlockCoordinates]
    congr 1
    omega

/-- All interior indices precede every top-degree even index. -/
theorem dunklXuEvenSectorEmbedding_before (r : ℕ) (i : DunklXuEvenInterior r) (j : Fin (r + 1)) :
    dunklXuEvenSectorEmbedding r (Sum.inl i) < dunklXuEvenSectorEmbedding r (Sum.inr j) := by
  apply (diskDegreeOrder (2 * r)).lt_iff_lt.mp
  rw [diskDegreeIndex_lt_iff]
  left
  simp only [diskDegreeOrder_evenSectorEmbedding, Finsupp.add_apply]
  simp only [dunklXuEvenBlockCoordinates, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add]
  have := i.2
  omega

/-- The top block is ordered by increasing inner index. -/
theorem dunklXuEvenSectorEmbedding_strictMono (r : ℕ) :
    StrictMono (dunklXuEvenSectorEmbedding r ∘ Sum.inr) := by
  intro i j hij
  apply (diskDegreeOrder (2 * r)).lt_iff_lt.mp
  rw [diskDegreeIndex_lt_iff]
  right
  simp only [Function.comp_apply, diskDegreeOrder_evenSectorEmbedding, Finsupp.add_apply]
  simp only [dunklXuEvenBlockCoordinates, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add]
  constructor <;> omega

end MvPolynomial
