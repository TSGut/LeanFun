/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.LinearIndependent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex

/-!
# Finite total-degree Dunkl–Xu bases

A dimension argument upgrades the orthogonal family to a basis of every
polynomial degree space. Exponent indices `(a,b)` represent disk indices
`(n,k)=(a+b,b)`; thus no monomial coefficient calculation is needed.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open Module
namespace MvPolynomial

/-- The disk family restricted to a finite degree space. -/
noncomputable def dunklXuDegreeFamily (β : ℝ) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    restrictTotalDegree (Fin 2) ℝ N :=
  ⟨dunklXuDisk β (d.1 0 + d.1 1) (d.1 1),
    (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((totalDegree_dunklXuDisk_le β _ _ (by omega)).trans
        (by simpa only [sum_exponents_fin_two] using d.2))⟩

/-- Independence remains valid in each finite degree subspace. -/
theorem linearIndependent_dunklXuDegreeFamily {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    LinearIndependent ℝ (dunklXuDegreeFamily β N) := by
  have h := ((linearIndependent_dunklXuDisk hβ).comp _ diskIndex_injective).comp
    (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} => d.1) Subtype.val_injective
  exact LinearIndependent.of_comp (restrictTotalDegree (Fin 2) ℝ N).subtype h

/-- The Cartesian disk polynomials form a basis of the entire finite degree space. -/
noncomputable def dunklXuDegreeBasis {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := by
  classical
  let b : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  exact basisOfLinearIndependentOfCardEqFinrank' (dunklXuDegreeFamily β N)
    (linearIndependent_dunklXuDegreeFamily hβ N)
    (Module.finrank_eq_card_basis b).symm

/-- The finite degree basis consists of the explicitly defined disk polynomials. -/
@[simp] theorem dunklXuDegreeBasis_apply {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    (dunklXuDegreeBasis hβ N d : MvPolynomial (Fin 2) ℝ) =
      dunklXuDisk β (d.1 0 + d.1 1) (d.1 1) := by
  simp [dunklXuDegreeBasis, dunklXuDegreeFamily]

/-- The full degree-indexed disk family spans all bivariate polynomials. -/
theorem span_dunklXuDisk {β : ℝ} (hβ : -1 < β) :
    Submodule.span ℝ (Set.range
      (fun i : Σ n : ℕ, Fin (n + 1) => dunklXuDisk β i.1 i.2)) = ⊤ := by
  classical
  apply top_unique
  intro p _
  let N := p.totalDegree
  let b := dunklXuDegreeBasis hβ N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  let u : restrictTotalDegree (Fin 2) ℝ N :=
    ⟨p, (mem_restrictTotalDegree (Fin 2) N p).mpr (le_refl _)⟩
  have he := congrArg (fun q : restrictTotalDegree (Fin 2) ℝ N =>
    (q : MvPolynomial (Fin 2) ℝ)) (b.sum_repr u)
  simp only [Submodule.coe_sum, Submodule.coe_smul, b, dunklXuDegreeBasis_apply] at he
  change (u : MvPolynomial (Fin 2) ℝ) ∈ _
  rw [← he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i.1 0 + i.1 1, ⟨i.1 1, by omega⟩⟩, rfl⟩

/-- The full Cartesian disk basis, indexed by degree and then inner index. -/
noncomputable def dunklXuBasis {β : ℝ} (hβ : -1 < β) :
    Basis (Σ n : ℕ, Fin (n + 1)) ℝ (MvPolynomial (Fin 2) ℝ) :=
  Basis.mk (linearIndependent_dunklXuDisk hβ) (span_dunklXuDisk hβ).ge

/-- Members of the full basis are the original Jacobi-normalized polynomials. -/
@[simp] theorem dunklXuBasis_apply {β : ℝ} (hβ : -1 < β) (i : Σ n : ℕ, Fin (n + 1)) :
    dunklXuBasis hβ i = dunklXuDisk β i.1 i.2 := by
  simp [dunklXuBasis]

end MvPolynomial
