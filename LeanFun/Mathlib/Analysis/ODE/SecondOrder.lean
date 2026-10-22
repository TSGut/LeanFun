/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-! # Uniqueness for scalar second-order linear equations

A two-dimensional first-order system supplies the uniqueness principle needed
for hypergeometric changes of variable (DLMF 15.10.1).
-/

public section
open Set
open scoped NNReal

/-- Two solutions of a scalar linear second-order equation with continuous
coefficients agree when their values and first derivatives agree initially. -/
theorem eqOn_of_secondOrder_linear_ode {a b t₀ : ℝ} {A B f f₁ g g₁ : ℝ → ℝ}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b)) (hf₁ : ContinuousOn f₁ (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hg₁ : ContinuousOn g₁ (Icc a b))
    (hfd : ∀ t ∈ Ioo a b, HasDerivAt f (f₁ t) t)
    (hfd₁ : ∀ t ∈ Ioo a b, HasDerivAt f₁ (A t*f t+B t*f₁ t) t)
    (hgd : ∀ t ∈ Ioo a b, HasDerivAt g (g₁ t) t)
    (hgd₁ : ∀ t ∈ Ioo a b, HasDerivAt g₁ (A t*g t+B t*g₁ t) t)
    (he : f t₀ = g t₀) (he₁ : f₁ t₀ = g₁ t₀) : EqOn f g (Icc a b) := by
  let v : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun t ↦
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (A t • ContinuousLinearMap.fst ℝ ℝ ℝ + B t • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hv : ContinuousOn v (Icc a b) := by
    have he : v = fun t ↦
        (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ) +
        A t • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        B t • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
      funext t
      ext <;> simp [v]
    rw [he]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hLip (t : ℝ) (ht' : t ∈ Ioo a b) :
      LipschitzOnWith K (v t) (Set.univ : Set (ℝ × ℝ)) := by
    apply ((v t).lipschitzWith.weaken ?_).lipschitzOnWith
    exact_mod_cast (hC t (Ioo_subset_Icc_self ht')).trans (le_max_left C 0)
  have hu := ODE_solution_unique_of_mem_Icc hLip ht
    (hf.prodMk hf₁) (fun t ht' ↦ (hfd t ht').prodMk (hfd₁ t ht'))
    (fun _ _ ↦ Set.mem_univ _) (hg.prodMk hg₁)
    (fun t ht' ↦ (hgd t ht').prodMk (hgd₁ t ht'))
    (fun _ _ ↦ Set.mem_univ _) (Prod.ext he he₁)
  intro t ht'
  exact congrArg Prod.fst (hu ht')
