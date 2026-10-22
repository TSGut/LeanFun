/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/

module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSeriesKernel
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraContinuousSolve
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # One coefficient condition for both Volterra approximations

Monomials may be enumerated in any order, allowing any bivariate power series.
Absolute weighted summability controls both physical and operator tails.
Reference: Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
open Polynomial Set Filter
open scoped Topology
namespace MvPolynomial
variable (i j : ℕ → ℕ) (c : ℕ → ℝ)

/-- Polynomial truncation of an enumerated kernel series. -/
def volterraSeriesPartial (N : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ n ∈ Finset.range N, volterraSeriesTerm (i n) (j n) (c n)

/-- Coefficients for which the ordered Volterra operator series converges. -/
def VolterraSeriesOperatorInput :=
  {c : ℕ → ℝ // Summable (fun n ↦
    volterraPreconditionedL2 (volterraSeriesTerm (i n) (j n) (c n)))}

/-- A summable joint coefficient majorant supplies a convergent operator input. -/
def VolterraSeriesOperatorInput.ofWeight {R S : ℝ}
    (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))
    (hRH : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hSJ : ‖shiftedJacobiOneZeroL2‖ ≤ S) :
    VolterraSeriesOperatorInput i j :=
  ⟨c, hw.of_norm_bounded (fun n ↦
    norm_volterraPreconditionedL2_seriesTerm_le hRH hSJ (i n) (j n) (c n))⟩

/-- The convergent ordered operator series associated to the kernel expansion. -/
def volterraSeriesOperator (d : VolterraSeriesOperatorInput i j) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  ∑' n, volterraPreconditionedL2 (volterraSeriesTerm (i n) (j n) (d.val n))

/-- The ordered operator series has the specified classical sum. -/
theorem hasSum_volterraSeriesOperator (d : VolterraSeriesOperatorInput i j) :
    HasSum (fun n ↦ volterraPreconditionedL2 (volterraSeriesTerm (i n) (j n) (d.val n)))
      (volterraSeriesOperator i j d) :=
  d.property.hasSum

/-- Coefficients whose joint Volterra majorant is summable. -/
def VolterraSeriesTailInput (R S : ℝ) :=
  {c : ℕ → ℝ // Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))}

/-- The shared tail input has a summable tail at each finite cutoff. -/
theorem VolterraSeriesTailInput.summable_tail {R S : ℝ}
    (d : VolterraSeriesTailInput i j R S) (N : ℕ) :
    Summable (fun n ↦ volterraSeriesWeight R S (i (n+N)) (j (n+N)) (d.val (n+N))) :=
  (summable_nat_add_iff N).mpr d.property

/-- A convergent coefficient majorant tail shared by physical and operator errors. -/
def volterraSeriesTail {R S : ℝ} (d : VolterraSeriesTailInput i j R S) (N : ℕ) : ℝ :=
  ∑' n, volterraSeriesWeight R S (i (n+N)) (j (n+N)) (d.val (n+N))

/-- The coefficient tail is the sum of its defining convergent series. -/
theorem hasSum_volterraSeriesTail {R S : ℝ} (d : VolterraSeriesTailInput i j R S) (N : ℕ) :
    HasSum (fun n ↦ volterraSeriesWeight R S (i (n+N)) (j (n+N)) (d.val (n+N)))
      (volterraSeriesTail i j d N) :=
  (VolterraSeriesTailInput.summable_tail i j d N).hasSum

private theorem series_tail_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) {w : ℕ → ℝ} (hw : Summable w) (hb : ∀ n, ‖f n‖ ≤ w n) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, f n) - ∑' n, f n‖ ≤ ∑' n, w (n+N) := by
  have hf := hw.of_norm_bounded hb
  have he := hf.sum_add_tsum_nat_add N
  rw [← he,sub_add_cancel_left,norm_neg]
  exact tsum_of_norm_bounded ((summable_nat_add_iff N).mpr hw).hasSum (fun n ↦ hb (n+N))

variable {R S : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S)
  (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))

include hR hS hw in
/-- The shared tail is nonnegative. -/
theorem volterraSeriesTail_nonneg (N : ℕ) : 0 ≤ volterraSeriesTail i j ⟨c, hw⟩ N :=
  tsum_nonneg (fun _n ↦ volterraSeriesWeight_nonneg (zero_le_one.trans hR)
    (zero_le_one.trans hS) _ _ _)

/-- Summable coefficient weights have vanishing tails. -/
theorem tendsto_volterraSeriesTail : Tendsto (volterraSeriesTail i j ⟨c, hw⟩) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n))

include hR hS hw in
/-- Uniform physical truncation error is bounded by the coefficient tail. -/
theorem norm_volterraSeriesPartial_sub_kernel_le (N : ℕ)
    (z : Real.volterraTriangle) :
    ‖eval (z : Fin 2 → ℝ) (volterraSeriesPartial i j c N) -
      volterraSeriesKernel i j (VolterraSeriesKernelInput.ofTriangle i j c hR hS hw z)‖ ≤
      volterraSeriesTail i j ⟨c, hw⟩ N := by
  have hz := z.property
  have hb (n : ℕ) : ‖eval (z : Fin 2 → ℝ) (volterraSeriesTerm (i n) (j n) (c n))‖ ≤
      volterraSeriesWeight R S (i n) (j n) (c n) :=
    norm_eval_volterraSeriesTerm_le (zero_le_one.trans hR) (zero_le_one.trans hS) _ _ _ _
      (by rw [abs_of_nonneg hz.1.1]; exact hz.1.2.trans hR)
      (by rw [abs_of_nonneg hz.2.1]; exact (hz.2.2.trans hz.1.2).trans hS)
  simpa only [volterraSeriesPartial, map_sum, eval_volterraSeriesTerm, volterraSeriesKernel,
    VolterraSeriesKernelInput.ofTriangle, VolterraSeriesKernelInput.ofWeight,
    volterraSeriesTail] using series_tail_bound _ hw hb N

/-- The physical series defines a continuous function on the triangle domain. -/
theorem continuous_volterraSeriesKernel :
    Continuous (fun z : Real.volterraTriangle ↦ volterraSeriesKernel i j
      (VolterraSeriesKernelInput.ofTriangle i j c hR hS hw z)) := by
  simp only [volterraSeriesKernel, VolterraSeriesKernelInput.ofTriangle,
    VolterraSeriesKernelInput.ofWeight]
  refine continuous_tsum (fun n ↦ ?_) hw (fun n z ↦ ?_)
  · simpa only [eval_volterraSeriesTerm, Function.comp_def] using
      (volterraSeriesTerm (i n) (j n) (c n)).continuous_eval.comp continuous_subtype_val
  · simpa only [eval_volterraSeriesTerm] using
      norm_eval_volterraSeriesTerm_le (zero_le_one.trans hR) (zero_le_one.trans hS)
        (i n) (j n) (c n) (z : Fin 2 → ℝ)
        (by rw [abs_of_nonneg z.property.1.1]; exact z.property.1.2.trans hR)
        (by rw [abs_of_nonneg z.property.2.1];
            exact (z.property.2.2.trans z.property.1.2).trans hS)

include hw in
/-- The same coefficient tail bounds preconditioned operator error. -/
theorem norm_volterraSeriesPartial_sub_operator_le
    (hRH : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hSJ : ‖shiftedJacobiOneZeroL2‖ ≤ S) (N : ℕ) :
    ‖volterraPreconditionedL2 (volterraSeriesPartial i j c N)-volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)‖ ≤
      volterraSeriesTail i j ⟨c, hw⟩ N := by
  have he : volterraPreconditionedL2 (volterraSeriesPartial i j c N) =
      ∑ n ∈ Finset.range N, volterraPreconditionedL2 (volterraSeriesTerm (i n) (j n) (c n)) :=
    map_sum volterraPreconditionedLinear _ _
  rw [he]
  exact series_tail_bound _ hw (fun n ↦ norm_volterraPreconditionedL2_seriesTerm_le hRH hSJ _ _ _) N

include hw in
/-- The joint coefficient criterion implies preconditioned operator-norm convergence. -/
theorem tendsto_volterraSeriesPartial_operator
    (hRH : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hSJ : ‖shiftedJacobiOneZeroL2‖ ≤ S) :
    Tendsto (fun N ↦ volterraPreconditionedL2 (volterraSeriesPartial i j c N))
      atTop (𝓝 (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (norm_volterraSeriesPartial_sub_operator_le i j c hw hRH hSJ)
    (tendsto_volterraSeriesTail i j c hw)
end MvPolynomial
