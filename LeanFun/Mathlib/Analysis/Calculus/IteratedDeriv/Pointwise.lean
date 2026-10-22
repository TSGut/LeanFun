/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Calculus.IteratedDeriv.OpenDomain

/-! # Classical derivative values at individual points
Reference: ATAP, Chapters 3 and 21; Olver--Townsend (2013), Sections 2--4.
-/

@[expose] public noncomputable section
open Set
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {U : TopologicalSpace.Opens 𝕜}

 theorem HasIteratedDerivOnOpen.exists_lower {n k : ℕ} {f g : U → 𝕜}
    (h : HasIteratedDerivOnOpen U n f g) (hk : k ≤ n) :
    ∃ v, HasIteratedDerivOnOpen U k f v := by
  induction n generalizing k g with
  | zero =>
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact ⟨f, rfl⟩
  | succ n ih =>
    rcases eq_or_lt_of_le hk with he | hl
    · subst k
      exact ⟨g, h⟩
    · obtain ⟨v, hv, _⟩ := h
      exact ih hv (Nat.le_of_lt_succ hl)

noncomputable def IteratedDerivInput.truncate {n k : ℕ}
    (f : IteratedDerivInput U n) (hk : k ≤ n) : IteratedDerivInput U k :=
  ⟨f.val, (iteratedDerivOnOpen_spec f).exists_lower hk⟩

@[simp] theorem IteratedDerivInput.truncate_val {n k : ℕ}
    (f : IteratedDerivInput U n) (hk : k ≤ n) :
    (f.truncate hk).val = f.val := rfl

open Set
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

 theorem HasDerivAtOnOpen.restrict {U V : TopologicalSpace.Opens 𝕜}
    (hVU : V ≤ U) {f : U → 𝕜} {d : 𝕜} (x : V)
    (h : HasDerivAtOnOpen U f d ⟨x.val, hVU x.property⟩) :
    HasDerivAtOnOpen V (fun y ↦ f ⟨y.val, hVU y.property⟩) d x := by
  obtain ⟨F, hF, hd⟩ := h
  exact ⟨F, fun y ↦ hF ⟨y.val, hVU y.property⟩, hd⟩

 theorem HasIteratedDerivOnOpen.restrict {U V : TopologicalSpace.Opens 𝕜}
    (hVU : V ≤ U) {n : ℕ} {f g : U → 𝕜}
    (h : HasIteratedDerivOnOpen U n f g) :
    HasIteratedDerivOnOpen V n
      (fun y ↦ f ⟨y.val, hVU y.property⟩) (fun y ↦ g ⟨y.val, hVU y.property⟩) := by
  induction n generalizing g with
  | zero => rw [hasIteratedDerivOnOpen_zero] at h ⊢; rw [h]
  | succ n ih =>
    obtain ⟨v, hv, hd⟩ := h
    exact ⟨_, ih hv, fun y ↦ (hd ⟨y.val, hVU y.property⟩).restrict hVU y⟩

/-- An order-n derivative exists at the specified point, with lower derivatives
existing on a neighbourhood. The highest derivative need only exist at the point. -/
def HasIteratedDerivAtOnOpen (U : TopologicalSpace.Opens 𝕜)
    (n : ℕ) (f : U → 𝕜) (d : 𝕜) (x : U) : Prop :=
  match n with
  | 0 => d = f x
  | k + 1 => ∃ (V : TopologicalSpace.Opens 𝕜) (hx : x.val ∈ V) (hVU : V ≤ U)
      (g : V → 𝕜),
      HasIteratedDerivOnOpen V k (fun y ↦ f ⟨y.val, hVU y.property⟩) g ∧
      HasDerivAtOnOpen V g d ⟨x.val, hx⟩

 theorem HasIteratedDerivAtOnOpen.unique {U : TopologicalSpace.Opens 𝕜}
    {n : ℕ} {f : U → 𝕜} {d e : 𝕜} {x : U}
    (hd : HasIteratedDerivAtOnOpen U n f d x)
    (he : HasIteratedDerivAtOnOpen U n f e x) : d = e := by
  cases n with
  | zero => exact hd.trans he.symm
  | succ n =>
    obtain ⟨V, hxV, hVU, g, hg, hd⟩ := hd
    obtain ⟨W, hxW, hWU, h, hh, he⟩ := he
    let Z := V ⊓ W
    have hZV : Z ≤ V := inf_le_left
    have hZW : Z ≤ W := inf_le_right
    have hgv := hg.restrict hZV
    have hhw := hh.restrict hZW
    have heq : (fun y : Z ↦ g ⟨y.val, hZV y.property⟩) =
        (fun y : Z ↦ h ⟨y.val, hZW y.property⟩) := hgv.unique hhw
    let y : Z := ⟨x.val, hxV, hxW⟩
    have hd' := hd.restrict hZV y
    have he' := he.restrict hZW y
    rw [heq] at hd'
    exact hd'.unique he'

 theorem HasIteratedDerivOnOpen.hasAt {U : TopologicalSpace.Opens 𝕜}
    {n : ℕ} {f g : U → 𝕜} (h : HasIteratedDerivOnOpen U n f g) (x : U) :
    HasIteratedDerivAtOnOpen U n f (g x) x := by
  cases n with
  | zero => exact congrFun h.symm x
  | succ n =>
    obtain ⟨v, hv, hd⟩ := h
    exact ⟨U, x.property, le_rfl, v, hv, hd x⟩

/-- The evaluation point certifies every derivative used by a finite differential expression. -/
abbrev DerivativeJetPoint (U : TopologicalSpace.Opens 𝕜) (m : ℕ) (f : U → 𝕜) :=
  {x : U // ∀ k : Fin (m + 1), ∃ d, HasIteratedDerivAtOnOpen U k.val f d x}

noncomputable def derivativeJet {U : TopologicalSpace.Opens 𝕜} {m : ℕ} {f : U → 𝕜}
    (x : DerivativeJetPoint U m f) (k : Fin (m + 1)) : 𝕜 := (x.property k).choose

theorem derivativeJet_spec {U : TopologicalSpace.Opens 𝕜} {m : ℕ} {f : U → 𝕜}
    (x : DerivativeJetPoint U m f) (k : Fin (m + 1)) :
    HasIteratedDerivAtOnOpen U k.val f (derivativeJet x k) x.val :=
  (x.property k).choose_spec

theorem derivativeJet_eq_iff {U : TopologicalSpace.Opens 𝕜} {m : ℕ} {f : U → 𝕜}
    (x : DerivativeJetPoint U m f) (k : Fin (m + 1)) (d : 𝕜) :
    derivativeJet x k = d ↔ HasIteratedDerivAtOnOpen U k.val f d x.val := by
  constructor
  · intro h; rw [← h]; exact derivativeJet_spec x k
  · exact (derivativeJet_spec x k).unique

noncomputable def DerivativeJetPoint.ofIterated {U : TopologicalSpace.Opens 𝕜} {m : ℕ}
    (f : IteratedDerivInput U m) (x : U) : DerivativeJetPoint U m f.val :=
  ⟨x, fun k ↦ ⟨_, (iteratedDerivOnOpen_spec
    (f.truncate (Nat.le_of_lt_succ k.isLt))).hasAt x⟩⟩

 theorem derivativeJet_ofIterated {U : TopologicalSpace.Opens 𝕜} {m : ℕ}
    (f : IteratedDerivInput U m) (x : U) (k : Fin (m + 1)) :
    derivativeJet (DerivativeJetPoint.ofIterated f x) k =
      iteratedDerivOnOpen (f.truncate (Nat.le_of_lt_succ k.isLt)) x := by
  apply (derivativeJet_eq_iff _ _ _).2
  exact (iteratedDerivOnOpen_spec (f.truncate (Nat.le_of_lt_succ k.isLt))).hasAt x
