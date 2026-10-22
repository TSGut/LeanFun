/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Sets.Opens
/-! # Derivatives on an open scalar domain

The point type carries the domain. Existence of a differentiable extension
states a local derivative without assigning function values outside that domain.
The characterisation theorem proves independence of the extension.
Reference: the ordinary local definition of differentiation; DLMF 18.8.1.
-/

@[expose] public section
open Set Filter
open scoped Topology
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Differentiation of a function whose point type is an open scalar domain. -/
def HasDerivAtOnOpen (U : TopologicalSpace.Opens 𝕜) (f : U → 𝕜)
    (d : 𝕜) (x : U) : Prop :=
  ∃ g : 𝕜 → 𝕜, (∀ y : U, g y = f y) ∧ HasDerivAt g d x

/-- A derivative is independent of the chosen extension off the open domain. -/
theorem hasDerivAtOnOpen_iff (U : TopologicalSpace.Opens 𝕜) (f : U → 𝕜)
    (d : 𝕜) (x : U) (g : 𝕜 → 𝕜) (hg : ∀ y : U, g y = f y) :
    HasDerivAtOnOpen U f d x ↔ HasDerivAt g d x := by
  constructor
  · rintro ⟨h, hh, hd⟩
    apply hd.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact (hg ⟨y, hy⟩).trans (hh ⟨y, hy⟩).symm
  · intro hd
    exact ⟨g, hg, hd⟩

/-- The value of a derivative on the open domain is unique. -/
theorem HasDerivAtOnOpen.unique {U : TopologicalSpace.Opens 𝕜} {f : U → 𝕜}
    {d e : 𝕜} {x : U} (hd : HasDerivAtOnOpen U f d x)
    (he : HasDerivAtOnOpen U f e x) : d = e := by
  rcases hd with ⟨g, hg, hd⟩
  exact hd.unique ((hasDerivAtOnOpen_iff U f e x g hg).mp he)

/-- The product rule on the open domain. -/
theorem HasDerivAtOnOpen.mul {U : TopologicalSpace.Opens 𝕜} {f g : U → 𝕜}
    {d e : 𝕜} {x : U} (hd : HasDerivAtOnOpen U f d x)
    (he : HasDerivAtOnOpen U g e x) :
    HasDerivAtOnOpen U (fun y ↦ f y * g y) (d * g x + f x * e) x := by
  rcases hd with ⟨F, hF, hd⟩
  rcases he with ⟨G, hG, he⟩
  refine ⟨fun y ↦ F y * G y, fun y ↦ by dsimp; rw [hF y, hG y], ?_⟩
  convert hd.mul he using 1
  simp only [hF x, hG x]

/-- Scalar multiplication preserves the derivative on the open domain. -/
theorem HasDerivAtOnOpen.const_mul {U : TopologicalSpace.Opens 𝕜} {f : U → 𝕜}
    {d : 𝕜} {x : U} (h : HasDerivAtOnOpen U f d x) (c : 𝕜) :
    HasDerivAtOnOpen U (fun y ↦ c * f y) (c * d) x := by
  rcases h with ⟨F, hF, hd⟩
  refine ⟨fun y ↦ c * F y, fun y ↦ by dsimp; rw [hF y], hd.const_mul c⟩

/-- Iterated derivatives through a chain of genuine derivatives on an open domain. -/
def HasIteratedDerivOnOpen (U : TopologicalSpace.Opens 𝕜) :
    ℕ → (U → 𝕜) → (U → 𝕜) → Prop
  | 0, f, g => f = g
  | n + 1, f, g => ∃ h, HasIteratedDerivOnOpen U n f h ∧
      ∀ x, HasDerivAtOnOpen U h (g x) x

/-- Order zero is equality of functions. -/
theorem hasIteratedDerivOnOpen_zero (U : TopologicalSpace.Opens 𝕜) (f g : U → 𝕜) :
    HasIteratedDerivOnOpen U 0 f g ↔ f = g := Iff.rfl

/-- Each successor adds one actual derivative, at every point of the domain. -/
theorem hasIteratedDerivOnOpen_succ (U : TopologicalSpace.Opens 𝕜)
    (n : ℕ) (f g : U → 𝕜) :
    HasIteratedDerivOnOpen U (n + 1) f g ↔
      ∃ h, HasIteratedDerivOnOpen U n f h ∧ ∀ x, HasDerivAtOnOpen U h (g x) x := Iff.rfl

/-- A derivative chain determines its final function uniquely. -/
theorem HasIteratedDerivOnOpen.unique {U : TopologicalSpace.Opens 𝕜} {n : ℕ}
    {f g h : U → 𝕜} (hg : HasIteratedDerivOnOpen U n f g)
    (hh : HasIteratedDerivOnOpen U n f h) : g = h := by
  induction n generalizing f g h with
  | zero => exact hg.symm.trans hh
  | succ n ih =>
    rcases hg with ⟨g', hg', dg⟩
    rcases hh with ⟨h', hh', dh⟩
    have he := ih hg' hh'
    subst h'
    funext x
    exact (dg x).unique (dh x)
