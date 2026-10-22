/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.OrderedConnection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Positive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramBilinear

/-! # Canonical Cholesky factors for Proriol parameter shifts
The actual normalized connection factors the modified Gram matrix and is
positive upper triangular in degree/inner order. Reference: Gutleb–Olver–Slevinsky,
measure modification and Cholesky conversion, specialized to DLMF 18.37.8.
-/

public section
open MeasureTheory Module
namespace MvPolynomial

/-- Normalized Proriol connections factor the target-measure Gram matrix exactly. -/
theorem integralGram_proriol_connection {α β γ α' β' γ' : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    (hα' : -1 < α') (hβ' : -1 < β') (hγ' : -1 < γ') (N : ℕ) :
    integralGram (proriolMeasure α' β' γ')
      (fun i ↦ (orderedProriolBasis hα hβ hγ N i : MvPolynomial (Fin 2) ℝ)) =
      ((orderedProriolBasis hα' hβ' hγ' N).toMatrix (orderedProriolBasis hα hβ hγ N)).transpose *
        (orderedProriolBasis hα' hβ' hγ' N).toMatrix (orderedProriolBasis hα hβ hγ N) :=
  integralGram_eq_transpose_toMatrix_mul_of_gram_eq_one _
    (hasFiniteMoments_proriolMeasure hα' hβ' hγ') _ _
    (integralGram_orderedProriolBasis hα' hβ' hγ' N)

/-- Integer parameter raising gives the canonical Cholesky factor, with no sign ambiguity. -/
theorem integralGramFactor_proriol_eq_connection {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c N : ℕ)
    (hαa : -1 < α+a) (hβb : -1 < β+b) (hγc : -1 < γ+c) :
    integralGramFactor (proriolMeasure (α+a) (β+b) (γ+c))
      (hasFiniteMoments_proriolMeasure hαa hβb hγc)
      (hasPositiveDefiniteIntegral_proriolMeasure hαa hβb hγc)
      (orderedProriolBasis hα hβ hγ N) =
      (orderedProriolBasis hαa hβb hγc N).toMatrix (orderedProriolBasis hα hβ hγ N) := by
  apply integralGramFactor_eq
  · exact orderedProriolBasis_connection_upperTriangular hα hβ hγ a b c N hαa hβb hγc
  · exact orderedProriolBasis_connection_diag_pos hα hβ hγ hαa hβb hγc N
  · exact integralGram_proriol_connection hα hβ hγ hαa hβb hγc N

/-- Both support bounds apply to the actual canonical Cholesky factor. -/
theorem integralGramFactor_proriol_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c N : ℕ)
    (hαa : -1 < α+a) (hβb : -1 < β+b) (hγc : -1 < γ+c)
    (i j : Fin (Fintype.card (DiskDegreeIndex N)))
    (hgap : ((diskDegreeOrder N j).1 1 < (diskDegreeOrder N i).1 1 ∨
      (diskDegreeOrder N i).1 1+(b+c) < (diskDegreeOrder N j).1 1) ∨
      ((diskDegreeOrder N j).1 0+(diskDegreeOrder N j).1 1 <
        (diskDegreeOrder N i).1 0+(diskDegreeOrder N i).1 1 ∨
        (diskDegreeOrder N i).1 0+(diskDegreeOrder N i).1 1+(a+b+c) <
          (diskDegreeOrder N j).1 0+(diskDegreeOrder N j).1 1)) :
    integralGramFactor (proriolMeasure (α+a) (β+b) (γ+c))
      (hasFiniteMoments_proriolMeasure hαa hβb hγc)
      (hasPositiveDefiniteIntegral_proriolMeasure hαa hβb hγc)
      (orderedProriolBasis hα hβ hγ N) i j = 0 := by
  rw [integralGramFactor_proriol_eq_connection]
  simp only [orderedProriolBasis, Basis.toMatrix_apply, Basis.reindex_apply,
    Basis.repr_reindex_apply]
  rw [normalizedProriolDegreeBasis_connection]
  apply mul_eq_zero_of_right
  have he := proriol_connection_eq_zero hα hβ hγ a b c N hαa hβb hγc
    ((diskDegreeIndexEquiv N) (diskDegreeOrder N j))
    ((diskDegreeIndexEquiv N) (diskDegreeOrder N i)) hgap
  simpa using he

end MvPolynomial
