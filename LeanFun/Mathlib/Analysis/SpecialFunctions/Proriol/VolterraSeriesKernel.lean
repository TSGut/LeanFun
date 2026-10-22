/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSeriesTerm
public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraApproximation
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.TietzeExtension

/-! # Classical domains for Volterra series kernels

The pointwise input certifies convergence before assigning a series value.
A joint coefficient majorant gives continuity on a closed rectangle. Genuine
continuous extensions are separate objects and are never identified with the
series outside that rectangle. Reference: Gutleb's thesis, §2.7, the Weierstrass
test, and the Tietze extension theorem.
-/

@[expose] public noncomputable section
open Polynomial Set
namespace MvPolynomial

def VolterraSeriesKernelInput (i j : ℕ → ℕ) (z : Fin 2 → ℝ) :=
  {c : ℕ → ℝ // Summable (fun n ↦ c n * z 0 ^ i n * z 1 ^ j n)}

def volterraSeriesKernel (i j : ℕ → ℕ) {z : Fin 2 → ℝ} (d : VolterraSeriesKernelInput i j z) : ℝ :=
  ∑' n, d.val n * z 0 ^ i n * z 1 ^ j n

theorem hasSum_volterraSeriesKernel (i j : ℕ → ℕ) {z : Fin 2 → ℝ} (d : VolterraSeriesKernelInput i j z) :
    HasSum (fun n ↦ d.val n * z 0 ^ i n * z 1 ^ j n) (volterraSeriesKernel i j d) :=
  d.property.hasSum

def volterraSeriesBox (R S : ℝ) : Set (Fin 2 → ℝ) :=
  {z | |z 0| ≤ R ∧ |z 1| ≤ S}

theorem isClosed_volterraSeriesBox (R S : ℝ) : IsClosed (volterraSeriesBox R S) := by
  exact (isClosed_le (show Continuous (fun z : Fin 2 → ℝ ↦ |z 0|) by fun_prop)
    continuous_const).inter
      (isClosed_le (show Continuous (fun z : Fin 2 → ℝ ↦ |z 1|) by fun_prop) continuous_const)

def VolterraSeriesKernelInput.ofWeight (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))
    (z : volterraSeriesBox R S) : VolterraSeriesKernelInput i j z :=
  ⟨c, hw.of_norm_bounded (fun n ↦ by
    simpa only [eval_volterraSeriesTerm] using
      norm_eval_volterraSeriesTerm_le hR hS (i n) (j n) (c n) z
        z.property.1 z.property.2)⟩

/-- The physical triangle supplies pointwise inputs from a joint coefficient majorant. -/
def VolterraSeriesKernelInput.ofTriangle (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))
    (z : Real.volterraTriangle) : VolterraSeriesKernelInput i j z :=
  VolterraSeriesKernelInput.ofWeight i j c (zero_le_one.trans hR) (zero_le_one.trans hS) hw
    ⟨z, by
      constructor
      · rw [abs_of_nonneg z.property.1.1]
        exact z.property.1.2.trans hR
      · rw [abs_of_nonneg z.property.2.1]
        exact (z.property.2.2.trans z.property.1.2).trans hS⟩

theorem continuous_volterraSeriesKernel_box (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))) :
    Continuous (fun z : volterraSeriesBox R S ↦ volterraSeriesKernel i j (VolterraSeriesKernelInput.ofWeight i j c hR hS hw z)) := by
  simp only [volterraSeriesKernel, VolterraSeriesKernelInput.ofWeight]
  refine continuous_tsum (fun n ↦ ?_) hw (fun n z ↦ ?_)
  · have h0 : Continuous (fun z : volterraSeriesBox R S ↦ (z : Fin 2 → ℝ) 0) :=
      (continuous_apply 0).comp continuous_subtype_val
    have h1 : Continuous (fun z : volterraSeriesBox R S ↦ (z : Fin 2 → ℝ) 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    exact ((h0.pow (i n)).const_mul (c n)).mul (h1.pow (j n))
  · simpa only [eval_volterraSeriesTerm] using
      norm_eval_volterraSeriesTerm_le hR hS (i n) (j n) (c n) z
        z.property.1 z.property.2

theorem exists_continuous_volterraSeriesKernel_extension (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))) :
    ∃ K : C((Fin 2 → ℝ), ℝ), ∀ z : volterraSeriesBox R S,
      K z = volterraSeriesKernel i j (VolterraSeriesKernelInput.ofWeight i j c hR hS hw z) := by
  obtain ⟨K,hK⟩ := (⟨_,continuous_volterraSeriesKernel_box i j c hR hS hw⟩ : C(volterraSeriesBox R S, ℝ)).exists_restrict_eq
    (isClosed_volterraSeriesBox R S)
  exact ⟨K, fun z ↦ congrArg (fun F : C(volterraSeriesBox R S, ℝ) ↦ F z) hK⟩

/-- A genuine continuous extension of the series on its closed convergence volterraSeriesBox. -/
def VolterraSeriesKernelExtension (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))) :=
  {K : C((Fin 2 → ℝ), ℝ) // ∀ z : volterraSeriesBox R S,
    K z = volterraSeriesKernel i j (VolterraSeriesKernelInput.ofWeight i j c hR hS hw z)}

theorem nonempty_volterraSeriesKernelExtension (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))) :
    Nonempty (VolterraSeriesKernelExtension i j c hR hS hw) := by
  obtain ⟨K,hK⟩ := exists_continuous_volterraSeriesKernel_extension i j c hR hS hw
  exact ⟨⟨K,hK⟩⟩

end MvPolynomial
