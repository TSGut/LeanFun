/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Order.Filter.Cofinite

/-! # A common real parameter outside countably many finite exceptional sets
Every nonempty open real interval is uncountable. Thus a countable family of
properties, each with finitely many exceptions, holds at some common parameter.
-/

public section
open Set Filter
namespace Real

/-- Countably many cofinite conditions admit a common point in any open interval. -/
theorem exists_Ioo_forall_of_eventually_cofinite {ι : Type*} [Countable ι]
    (P : ι → ℝ → Prop) (hP : ∀ i, ∀ᶠ t in Filter.cofinite, P i t)
    {a b : ℝ} (hab : a < b) : ∃ t ∈ Ioo a b, ∀ i, P i t := by
  classical
  let E : Set ℝ := ⋃ i, {t | ¬ P i t}
  have hc : E.Countable := Set.countable_iUnion fun i ↦
    (Filter.mem_cofinite.mp (hP i)).countable
  have hn : ¬ Ioo a b ⊆ E := fun h ↦
    (not_le_of_gt hab) (Cardinal.Real.Ioo_countable_iff.mp (hc.mono h))
  obtain ⟨t, ht, hte⟩ := Set.not_subset.mp hn
  refine ⟨t, ht, fun i ↦ ?_⟩
  by_contra hi
  exact hte (Set.mem_iUnion.mpr ⟨i, hi⟩)

end Real
