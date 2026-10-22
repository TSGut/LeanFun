/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSeriesApproximation
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Slice regularity from the joint coefficient criterion

Termwise differentiation on a box larger than the physical triangle supplies
absolute continuity and the derivative bound needed for first-kind uniqueness.
Reference: Gutleb's thesis, §2.7; the Weierstrass differentiation theorem.
-/
@[expose] public noncomputable section
open Polynomial Set Filter
open scoped Topology NNReal
namespace MvPolynomial
variable (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ} (hR : 1 ≤ R) (hS : 1 < S)
  (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))
  (E : VolterraSeriesKernelExtension i j c (zero_le_one.trans hR) (zero_le_one.trans hS.le) hw)

/-- Any continuous extension has the genuine series derivative in the open volterraSeriesBox. -/
private theorem hasDerivAt_volterraSeriesKernel_extension {x y : ℝ} (hx : |x| ≤ R) (hy : |y| < S) :
    HasDerivAt (fun t ↦ E.val ![x,t])
      (∑' n, c n*x^(i n)*((j n : ℝ)*y^(j n-1))) y := by
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ Ioo (-S) S) :
      ‖c n*x^(i n)*((j n : ℝ)*t^(j n-1))‖ ≤
        volterraSeriesWeight R S (i n) (j n) (c n) :=
    norm_volterraSeriesTerm_derivative_le (zero_le_one.trans hR) hS.le _ _ _ _ _ hx
      (abs_le.mpr ⟨ht.1.le,ht.2.le⟩)
  have h0 : Summable (fun n ↦ c n*x^(i n)*(0 : ℝ)^(j n)) := by
    apply hw.of_norm_bounded
    intro n
    simpa only [eval_volterraSeriesTerm,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using
      norm_eval_volterraSeriesTerm_le (zero_le_one.trans hR) (zero_le_one.trans hS.le)
        (i n) (j n) (c n) ![x,0] hx (by simpa using zero_le_one.trans hS.le)
  have hd := hasDerivAt_tsum_of_isPreconnected hw isOpen_Ioo (convex_Ioo (-S) S).isPreconnected
    (fun n t _ ↦ (hasDerivAt_pow (j n) t).const_mul (c n*x^(i n))) hb
    (show (0 : ℝ) ∈ Ioo (-S) S by constructor <;> linarith) h0 (abs_lt.mp hy)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with t ht
  simpa only [volterraSeriesKernel, VolterraSeriesKernelInput.ofWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using
    E.property ⟨![x,t], hx, abs_le.mpr ⟨ht.1.le,ht.2.le⟩⟩

/-- The series derivative exists intrinsically on its open inner domain. -/
theorem hasDerivAt_volterraSeriesKernel (x : {x : ℝ // |x| ≤ R}) (y : Ioo (-S) S) :
    HasDerivAtOnOpen ⟨Ioo (-S) S, isOpen_Ioo⟩
      (fun t ↦ volterraSeriesKernel i j (VolterraSeriesKernelInput.ofWeight i j c
        (zero_le_one.trans hR) (zero_le_one.trans hS.le) hw
        ⟨![(x : ℝ),(t : ℝ)], x.property, abs_le.mpr ⟨t.property.1.le,t.property.2.le⟩⟩))
      (∑' n, c n*(x : ℝ)^(i n)*((j n : ℝ)*(y : ℝ)^(j n-1))) y := by
  obtain ⟨F⟩ := nonempty_volterraSeriesKernelExtension i j c
    (zero_le_one.trans hR) (zero_le_one.trans hS.le) hw
  refine ⟨fun t ↦ F.val ![(x : ℝ),t], ?_,
    hasDerivAt_volterraSeriesKernel_extension i j c hR hS hw F x.property
      (abs_lt.mpr y.property)⟩
  intro t
  exact F.property ⟨![(x : ℝ),(t : ℝ)], x.property,
    abs_le.mpr ⟨t.property.1.le,t.property.2.le⟩⟩

/-- The joint coefficient sum bounds the derivative of every classical extension on the triangle. -/
theorem norm_deriv_volterraSeriesKernel_le (x : Icc (0 : ℝ) 1)
    (y : Icc (0 : ℝ) (x : ℝ)) :
    ‖deriv (fun t ↦ E.val ![(x : ℝ),t]) (y : ℝ)‖ ≤
      ∑' n, volterraSeriesWeight R S (i n) (j n) (c n) := by
  have hx := x.property
  have hy := y.property
  have hxR : |(x : ℝ)| ≤ R := by rw [abs_of_nonneg hx.1]; exact hx.2.trans hR
  have hyS : |(y : ℝ)| < S := by
    rw [abs_of_nonneg hy.1]
    exact (hy.2.trans hx.2).trans_lt hS
  rw [(hasDerivAt_volterraSeriesKernel_extension i j c hR hS hw E hxR hyS).deriv]
  exact tsum_of_norm_bounded hw.hasSum (fun n ↦
    norm_volterraSeriesTerm_derivative_le (zero_le_one.trans hR) hS.le _ _ _ _ _ hxR hyS.le)

/-- Every classical extension has absolutely continuous physical rows. -/
theorem absolutelyContinuousOnInterval_volterraSeriesKernel (x : Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (fun t ↦ E.val ![(x : ℝ),t]) 0 (x : ℝ) := by
  have hx := x.property
  let D : ℝ≥0 := ⟨∑' n, volterraSeriesWeight R S (i n) (j n) (c n),
    tsum_nonneg (fun n ↦ volterraSeriesWeight_nonneg (zero_le_one.trans hR)
      (zero_le_one.trans hS.le) _ _ _)⟩
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
  rw [uIcc_of_le hx.1]
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le _ _ (convex_Icc _ _)
  · intro y hy
    exact (hasDerivAt_volterraSeriesKernel_extension i j c hR hS hw E
      (by rw [abs_of_nonneg hx.1]; exact hx.2.trans hR)
      (by rw [abs_of_nonneg hy.1]; exact (hy.2.trans hx.2).trans_lt hS)).differentiableAt
  · intro y hy
    exact_mod_cast norm_deriv_volterraSeriesKernel_le i j c hR hS hw E x ⟨y,hy⟩

/-- A nonzero diagonal gives a uniform relative derivative bound for every classical extension. -/
theorem exists_volterraSeriesKernel_relative_derivative_bound
    (hd : ∀ x : Icc (0 : ℝ) 1, E.val ![(x : ℝ),(x : ℝ)] ≠ 0) :
    ∃ C : ℝ, ∀ x : Icc (0 : ℝ) 1, ∀ y : Icc (0 : ℝ) (x : ℝ),
      ‖deriv (fun t ↦ E.val ![(x : ℝ),t]) (y : ℝ)‖ ≤
        C*|E.val ![(x : ℝ),(x : ℝ)]| := by
  have hc : ContinuousOn (fun x : ℝ ↦ |E.val ![x,x]|) (Icc 0 1) :=
    (E.val.continuous.comp (by fun_prop)).abs.continuousOn
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) hc
  let a := |E.val ![t,t]|
  have ha : 0 < a := abs_pos.mpr (hd ⟨t,ht⟩)
  let D := ∑' n, volterraSeriesWeight R S (i n) (j n) (c n)
  have hD : 0 ≤ D := tsum_nonneg (fun n ↦ volterraSeriesWeight_nonneg
    (zero_le_one.trans hR) (zero_le_one.trans hS.le) _ _ _)
  refine ⟨D/a,fun x y ↦ ?_⟩
  calc
    _ ≤ D := norm_deriv_volterraSeriesKernel_le i j c hR hS hw E x y
    _ = (D/a)*a := (div_mul_cancel₀ D ha.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm x.property) (div_nonneg hD ha.le)

end MvPolynomial
