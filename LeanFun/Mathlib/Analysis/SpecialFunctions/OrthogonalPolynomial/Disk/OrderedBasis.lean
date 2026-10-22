/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Basis
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FinCases

/-! # Cartesian disk bases in degree and inner-index order
The complete degree space is enumerated by increasing total degree, then by
increasing inner index. Reference: Dunkl--Xu, Cartesian disk polynomials.
-/

@[expose] public section
open MeasureTheory Set Module
namespace MvPolynomial

/-- Exponents in the complete bivariate degree space. -/
@[ext] structure DiskDegreeIndex (N : ℕ) where
  /-- Outer and inner exponents. -/
  val : Fin 2 →₀ ℕ
  /-- The total degree belongs to the finite section. -/
  property : val.sum (fun _ e ↦ e) ≤ N

/-- Forget only the ordering wrapper around a bounded exponent pair. -/
def diskDegreeIndexEquiv (N : ℕ) :
    DiskDegreeIndex N ≃ {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} where
  toFun d := ⟨d.1, d.2⟩
  invFun d := ⟨d.1, d.2⟩

noncomputable instance (N : ℕ) : Fintype (DiskDegreeIndex N) := by
  let b : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ (restrictTotalDegree (Fin 2) ℝ N) :=
    basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  exact Fintype.ofEquiv _ (diskDegreeIndexEquiv N).symm

instance diskDegreeLinearOrder (N : ℕ) : LinearOrder (DiskDegreeIndex N) :=
  LinearOrder.lift' (fun d ↦ toLex (d.1 0 + d.1 1, d.1 1)) (by
    intro d e h
    have hn := congrArg (fun p ↦ (ofLex p).1) h
    have hk := congrArg (fun p ↦ (ofLex p).2) h
    apply DiskDegreeIndex.ext
    ext i
    fin_cases i <;> dsimp at hn hk ⊢ <;> omega)

/-- Increasing enumeration of the complete degree/inner ordering. -/
noncomputable def diskDegreeOrder (N : ℕ) :
    Fin (Fintype.card (DiskDegreeIndex N)) ≃o DiskDegreeIndex N :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- Build a degree index from outer and inner exponents. -/
noncomputable def diskDegreeIndex (N a b : ℕ) (h : a + b ≤ N) : DiskDegreeIndex N :=
  ⟨Finsupp.single 0 a + Finsupp.single 1 b, by
    simpa [sum_exponents_fin_two] using h⟩

@[simp] theorem diskDegreeIndex_zero (N a b : ℕ) (h : a + b ≤ N) :
    (diskDegreeIndex N a b h).1 0 = a := by simp [diskDegreeIndex]

@[simp] theorem diskDegreeIndex_one (N a b : ℕ) (h : a + b ≤ N) :
    (diskDegreeIndex N a b h).1 1 = b := by simp [diskDegreeIndex]

/-- Strict ordering is total degree first and inner degree second. -/
theorem diskDegreeIndex_lt_iff {N : ℕ} (d e : DiskDegreeIndex N) :
    d < e ↔ d.1 0 + d.1 1 < e.1 0 + e.1 1 ∨
      d.1 0 + d.1 1 = e.1 0 + e.1 1 ∧ d.1 1 < e.1 1 := by
  exact Prod.Lex.lt_iff

namespace CartesianDiskSystem
variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)

/-- The existing complete degree basis, reindexed in degree/inner order. -/
noncomputable def orderedDegreeBasis (N : ℕ) :
    Basis (Fin (Fintype.card (DiskDegreeIndex N))) ℝ (restrictTotalDegree (Fin 2) ℝ N) :=
  (S.degreeBasis hx hz N).reindex
    ((diskDegreeIndexEquiv N).symm.trans (diskDegreeOrder N).symm.toEquiv)

@[simp] theorem orderedDegreeBasis_apply (N : ℕ)
    (i : Fin (Fintype.card (DiskDegreeIndex N))) :
    (S.orderedDegreeBasis hx hz N i : MvPolynomial (Fin 2) ℝ) =
      S.polynomial ((diskDegreeOrder N i).1 0 + (diskDegreeOrder N i).1 1)
        ((diskDegreeOrder N i).1 1) := by
  simp [orderedDegreeBasis, diskDegreeIndexEquiv]

end CartesianDiskSystem
end MvPolynomial
