/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! # Injectivity suffices for invertible compact perturbations

A direct consequence of Mathlib's Fredholm alternative, without index theory.
Reference: the Fredholm alternative, as used in Gutleb's thesis, §2.7.
-/

public noncomputable section
namespace ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- An injective identity-plus-compact operator is invertible. -/
theorem isUnit_one_add_of_injective_of_compact (K : E →L[𝕜] E)
    (hK : IsCompactOperator K) (hinj : Function.Injective (1+K : E →L[𝕜] E)) :
    IsUnit (1+K) := by
  have hn : IsCompactOperator (-K : E →L[𝕜] E) := hK.neg
  rcases hn.hasEigenvalue_or_mem_resolventSet (μ := (1 : 𝕜)) one_ne_zero with he | hr
  · obtain ⟨u, hu⟩ := he.exists_hasEigenvector
    have heq : -K u = u := by
      have h := hu.apply_eq_smul
      change -K u = (1 : 𝕜) • u at h
      simpa only [one_smul] using h
    have hz : (1+K : E →L[𝕜] E) u = (1+K : E →L[𝕜] E) 0 := by
      simp only [add_apply, one_apply_eq_self, map_zero]
      calc
        u + K u = -K u + K u := congrArg (fun v ↦ v + K u) heq.symm
        _ = 0 := neg_add_cancel _
    exact (hu.2 (hinj hz)).elim
  · rw [spectrum.mem_resolventSet_iff] at hr
    simpa only [map_one, sub_neg_eq_add] using hr

/-- Injectivity of a compact perturbation of an invertible operator implies invertibility. -/
theorem isUnit_add_of_injective_of_compact (A K : E →L[𝕜] E)
    (hA : IsUnit A) (hK : IsCompactOperator K)
    (hinj : Function.Injective (A+K)) : IsUnit (A+K) := by
  have he : A*(1+(Ring.inverse A).comp K) = A+K := by
    change A*(1+Ring.inverse A*K) = _
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
  have hi : Function.Injective (1+(Ring.inverse A).comp K : E →L[𝕜] E) := by
    intro u v huv
    apply hinj
    have h := congrArg A huv
    simpa only [← he, mul_apply_eq_comp] using h
  rw [← he]
  exact hA.mul (isUnit_one_add_of_injective_of_compact _ (hK.clm_comp _) hi)

end ContinuousLinearMap
