/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Normalization
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ParameterShiftSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ParameterPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.OrderedBasis

/-! # Ordered normalized Proriol connections
Use increasing total degree, then increasing inner degree, in complete finite
sections. Reference: DLMF 18.37 and Cholesky measure conversion.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- A normalized connection is a positive diagonal rescaling of the raw connection. -/
theorem normalizedProriolDegreeBasis_connection {α β γ α' β' γ' : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    (hα' : -1 < α') (hβ' : -1 < β') (hγ' : -1 < γ') (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (normalizedProriolDegreeBasis hα' hβ' hγ' N).repr
      (normalizedProriolDegreeBasis hα hβ hγ N i) j =
      proriolNorm α' β' γ' ⟨((j.1 0+j.1 1), (j.1 1)), by exact hasFiniteMoments_proriolMeasure (by linarith) (by linarith) (by linarith) _⟩ *
        (proriolNorm α β γ ⟨((i.1 0+i.1 1), (i.1 1)), by exact hasFiniteMoments_proriolMeasure (by linarith) (by linarith) (by linarith) _⟩)⁻¹ *
        (proriolDegreeBasis hα' hβ' hγ' N).repr (proriolDegreeBasis hα hβ hγ N i) j := by
  rw [normalizedProriolDegreeBasis_repr, normalizedProriolDegreeBasis, Basis.isUnitSMul_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

/-- The normalized complete degree basis in degree/inner order. -/
noncomputable def orderedProriolBasis {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ) :
    Basis (Fin (Fintype.card (DiskDegreeIndex N))) ℝ (restrictTotalDegree (Fin 2) ℝ N) :=
  (normalizedProriolDegreeBasis hα hβ hγ N).reindex
    ((diskDegreeIndexEquiv N).symm.trans (diskDegreeOrder N).symm.toEquiv)

/-- Ordered positive normalization remains orthonormal. -/
theorem integralGram_orderedProriolBasis {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ) :
    integralGram (proriolMeasure α β γ)
      (fun i ↦ (orderedProriolBasis hα hβ hγ N i : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  let e := (diskDegreeIndexEquiv N).symm.trans (diskDegreeOrder N).symm.toEquiv
  have he := congrArg (Matrix.reindex e e) (integralGram_normalizedProriolDegreeBasis hα hβ hγ N)
  ext i j
  have hij := congrArg (fun M ↦ M i j) he
  simpa [orderedProriolBasis, Matrix.reindex_apply, Matrix.one_apply, Function.comp_apply, integralGram, e] using hij

/-- Integer parameter raising is upper triangular in the fixed scalar ordering. -/
theorem orderedProriolBasis_connection_upperTriangular {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c N : ℕ)
    (hαa : -1 < α+a) (hβb : -1 < β+b) (hγc : -1 < γ+c) :
    ((orderedProriolBasis hαa hβb hγc N).toMatrix
      (orderedProriolBasis hα hβ hγ N)).IsUpperTriangular := by
  intro i j hij
  simp only [orderedProriolBasis, Basis.toMatrix_apply, Basis.reindex_apply,
    Basis.repr_reindex_apply]
  rw [normalizedProriolDegreeBasis_connection]
  have hz := proriol_connection_eq_zero hα hβ hγ a b c N hαa hβb hγc
    ((diskDegreeIndexEquiv N) (diskDegreeOrder N j))
    ((diskDegreeIndexEquiv N) (diskDegreeOrder N i))
  have hord := (diskDegreeOrder N).strictMono hij
  rw [diskDegreeIndex_lt_iff] at hord
  have hg : ((diskDegreeOrder N j).1 1 < (diskDegreeOrder N i).1 1 ∨
      (diskDegreeOrder N i).1 1+(b+c) < (diskDegreeOrder N j).1 1) ∨
      ((diskDegreeOrder N j).1 0+(diskDegreeOrder N j).1 1 <
        (diskDegreeOrder N i).1 0+(diskDegreeOrder N i).1 1 ∨
        (diskDegreeOrder N i).1 0+(diskDegreeOrder N i).1 1+(a+b+c) <
          (diskDegreeOrder N j).1 0+(diskDegreeOrder N j).1 1) := by
    rcases hord with h | ⟨_,h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
  apply mul_eq_zero_of_right
  simpa using hz hg

/-- The ordered normalized connection has positive diagonal for arbitrary admissible target parameters. -/
theorem orderedProriolBasis_connection_diag_pos {α β γ α' β' γ' : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    (hα' : -1 < α') (hβ' : -1 < β') (hγ' : -1 < γ') (N : ℕ)
    (i : Fin (Fintype.card (DiskDegreeIndex N))) :
    0 < (orderedProriolBasis hα' hβ' hγ' N).toMatrix (orderedProriolBasis hα hβ hγ N) i i := by
  simp only [orderedProriolBasis, Basis.toMatrix_apply, Basis.reindex_apply,
    Basis.repr_reindex_apply]
  rw [normalizedProriolDegreeBasis_connection, proriolDegreeBasis_repr]
  simp only [proriolDegreeBasis_apply]
  exact mul_pos (mul_pos (proriolNorm_pos hα' hβ' hγ' _ _)
    (inv_pos.mpr (proriolNorm_pos hα hβ hγ _ _)))
    (div_pos (integralInner_proriol_diag_pos hα hβ hγ hα' hβ' hγ' _ _)
      (integral_sq_proriolMeasure_pos hα' hβ' hγ' _ _))

end MvPolynomial
