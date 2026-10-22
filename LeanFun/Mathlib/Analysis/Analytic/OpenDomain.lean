/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.Sets.Opens

/-! # Analytic functions on an open scalar domain
Analyticity is a local property of functions defined only on their open domain.
Reference: ATAP, Chapter 8; the local power-series definition of analyticity.
-/

@[expose] public section
open Set Filter
open scoped Topology
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Analyticity of a function with an open domain in its point type. -/
def AnalyticOnOpen (U : TopologicalSpace.Opens 𝕜) (f : U → 𝕜) : Prop :=
  ∀ x : U, ∃ g : 𝕜 → 𝕜, (∀ y : U, g y = f y) ∧ AnalyticAt 𝕜 g x

/-- Analyticity does not depend on how values are assigned outside the open domain. -/
theorem analyticOnOpen_iff (U : TopologicalSpace.Opens 𝕜) (f : U → 𝕜)
    (g : 𝕜 → 𝕜) (hg : ∀ y : U, g y = f y) :
    AnalyticOnOpen U f ↔ AnalyticOnNhd 𝕜 g U := by
  constructor
  · intro h x hx
    obtain ⟨F, hF, hA⟩ := h ⟨x, hx⟩
    apply hA.congr
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact (hF ⟨y, hy⟩).trans (hg ⟨y, hy⟩).symm
  · intro h x
    exact ⟨g, hg, h x x.property⟩
