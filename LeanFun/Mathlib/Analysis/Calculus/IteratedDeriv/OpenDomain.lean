/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import LeanFun.Mathlib.Analysis.Analytic.OpenDomain
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Classical iterated derivatives on open domains
The input certifies a derivative chain of the requested order. No derivative
value is assigned where the chain does not exist. Reference: ordinary iterated
differentiation; ATAP, Chapter 21.
-/

@[expose] public noncomputable section
open Set
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Functions possessing a derivative chain of the specified order. -/
abbrev IteratedDerivInput (U : TopologicalSpace.Opens 𝕜) (n : ℕ) :=
  {f : U → 𝕜 // ∃ g, HasIteratedDerivOnOpen U n f g}

/-- The unique final function of the certified derivative chain. -/
def iteratedDerivOnOpen {U : TopologicalSpace.Opens 𝕜} {n : ℕ}
    (f : IteratedDerivInput U n) : U → 𝕜 := f.property.choose

/-- The classical value belongs to an actual derivative chain. -/
theorem iteratedDerivOnOpen_spec {U : TopologicalSpace.Opens 𝕜} {n : ℕ}
    (f : IteratedDerivInput U n) :
    HasIteratedDerivOnOpen U n f.val (iteratedDerivOnOpen f) := f.property.choose_spec

/-- Every certified chain gives the same classical derivative value. -/
theorem iteratedDerivOnOpen_eq_iff {U : TopologicalSpace.Opens 𝕜} {n : ℕ}
    (f : IteratedDerivInput U n) (g : U → 𝕜) :
    iteratedDerivOnOpen f = g ↔ HasIteratedDerivOnOpen U n f.val g := by
  constructor
  · intro h
    rw [← h]
    exact iteratedDerivOnOpen_spec f
  · exact (iteratedDerivOnOpen_spec f).unique

/-- Order zero gives the original function. -/
theorem iteratedDerivOnOpen_zero {U : TopologicalSpace.Opens 𝕜}
    (f : IteratedDerivInput U 0) : iteratedDerivOnOpen f = f.val :=
  (iteratedDerivOnOpen_spec f).symm

variable [CompleteSpace 𝕜]

/-- Analyticity supplies every derivative chain on the open domain. -/
theorem hasIteratedDerivOnOpen_of_analytic_extension
    (U : TopologicalSpace.Opens 𝕜) (F : 𝕜 → 𝕜)
    (hF : AnalyticOnNhd 𝕜 F U) (n : ℕ) :
    HasIteratedDerivOnOpen U n (fun x ↦ F x) (fun x ↦ iteratedDeriv n F x) := by
  induction n with
  | zero => simp only [hasIteratedDerivOnOpen_zero, iteratedDeriv_zero]
  | succ n ih =>
    refine ⟨_, ih, fun x ↦ ?_⟩
    refine ⟨iteratedDeriv n F, fun _ ↦ rfl, ?_⟩
    rw [iteratedDeriv_succ]
    have ha : AnalyticAt 𝕜 (iteratedDeriv n F) x := by
      simpa only [iteratedDeriv_eq_iterate] using (hF.iterated_deriv n) x x.property
    exact ha.differentiableAt.hasDerivAt

/-- An analytic function on a typed open domain has derivatives of every order. -/
theorem AnalyticOnOpen.exists_iteratedDeriv {U : TopologicalSpace.Opens 𝕜}
    {f : U → 𝕜} (hf : AnalyticOnOpen U f) (n : ℕ) :
    ∃ g, HasIteratedDerivOnOpen U n f g := by
  classical
  by_cases hU : Nonempty U
  · obtain ⟨x⟩ := hU
    obtain ⟨F, hF, _⟩ := hf x
    have ha := (analyticOnOpen_iff U f F hF).mp hf
    have hd := hasIteratedDerivOnOpen_of_analytic_extension U F ha n
    have he : (fun x : U ↦ F x) = f := funext hF
    rw [he] at hd
    exact ⟨_, hd⟩
  · have : IsEmpty U := ⟨fun x ↦ hU ⟨x⟩⟩
    refine ⟨f, ?_⟩
    induction n with
    | zero => rfl
    | succ n ih => exact ⟨f, ih, fun x ↦ isEmptyElim x⟩

/-- Analyticity constructs an input for every classical derivative order. -/
def IteratedDerivInput.ofAnalytic {U : TopologicalSpace.Opens 𝕜}
    (f : U → 𝕜) (hf : AnalyticOnOpen U f) (n : ℕ) : IteratedDerivInput U n :=
  ⟨f, hf.exists_iteratedDeriv n⟩

/-- Internal bridge to imported differentiation, only at points of its analytic domain. -/
theorem iteratedDerivOnOpen_eq_iteratedDeriv {U : TopologicalSpace.Opens 𝕜}
    {n : ℕ} (f : IteratedDerivInput U n) (F : 𝕜 → 𝕜)
    (hF : AnalyticOnNhd 𝕜 F U) (he : ∀ x : U, F x = f.val x) :
    iteratedDerivOnOpen f = fun x : U ↦ iteratedDeriv n F x := by
  apply (iteratedDerivOnOpen_eq_iff f _).2
  have h := hasIteratedDerivOnOpen_of_analytic_extension U F hF n
  have he' : (fun x : U ↦ F x) = f.val := funext he
  rwa [he'] at h
