/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraNorm
public import LeanFun.Mathlib.Analysis.IntegralEq.L2Dominated

/-! # Continuous L² rows of a Volterra kernel

The moving triangular cutoff is continuous in L², although it need not be
continuous pointwise on the diagonal. Reference: dominated convergence and
the compact-kernel argument for Volterra integral equations.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped ENNReal Topology InnerProductSpace
namespace Real
local instance : IsFiniteMeasure (unitJacobiMeasure 0 0) :=
  isFiniteMeasure_unitJacobiMeasure (by norm_num) (by norm_num)
local instance : NullSingletonClass (unitJacobiMeasure 0 0) := by
  constructor
  intro x
  rw [unitJacobiMeasure_zero_zero]
  simp

variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M)

include hK hM hb in
/-- Every zero-extended Volterra row belongs to the physical L² space. -/
theorem memLp_volterraL2Kernel_row (x : ℝ) :
    MemLp (fun y ↦ volterraL2Kernel K (x,y)) 2 (unitJacobiMeasure 0 0) :=
  MemLp.of_bound ((measurable_volterraL2Kernel hK).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
    (Eventually.of_forall (fun y ↦ norm_volterraL2Kernel_le hM hb (x,y)))

/-- The L² class of a zero-extended Volterra row. -/
def volterraL2Row (x : ℝ) : Lp ℝ 2 (unitJacobiMeasure 0 0) :=
  (memLp_volterraL2Kernel_row hK hM hb x).toLp _

/-- Volterra rows have the expected almost-everywhere representative. -/
theorem volterraL2Row_ae (x : ℝ) :
    volterraL2Row hK hM hb x =ᵐ[unitJacobiMeasure 0 0]
      fun y ↦ volterraL2Kernel K (x,y) :=
  (memLp_volterraL2Kernel_row hK hM hb x).coeFn_toLp

/-- The row inner product is the ordinary kernel integral. -/
theorem inner_volterraL2Row (x : ℝ) (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    ⟪volterraL2Row hK hM hb x, f⟫_ℝ =
      ∫ y, volterraL2Kernel K (x,y) * f y ∂unitJacobiMeasure 0 0 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [volterraL2Row_ae hK hM hb x] with y hy
  simp only [Real.inner_apply, hy]

/-- A uniform bound for all row norms. -/
theorem norm_volterraL2Row_le (x : ℝ) :
    ‖volterraL2Row hK hM hb x‖ ≤
      (measureUnivNNReal (unitJacobiMeasure 0 0) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M := by
  apply Lp.norm_le_of_ae_bound hM
  filter_upwards [volterraL2Row_ae hK hM hb x] with y hy
  rw [hy]
  exact norm_volterraL2Kernel_le hM hb (x,y)

/-- Pairing a row with fixed L² data again gives an L² function of the row parameter. -/
theorem memLp_inner_volterraL2Row (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    MemLp (fun x ↦ ⟪volterraL2Row hK hM hb x, f⟫_ℝ) 2 (unitJacobiMeasure 0 0) := by
  have hf := (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := unitJacobiMeasure 0 0)
      (ν := unitJacobiMeasure 0 0))
  have hm := ((measurable_volterraL2Kernel hK).aestronglyMeasurable.mul hf).integral_prod_right'
  simp only [Function.comp_def, Pi.mul_apply] at hm
  simp_rw [← inner_volterraL2Row hK hM hb] at hm
  apply MemLp.of_bound hm
    (((measureUnivNNReal (unitJacobiMeasure 0 0) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M) * ‖f‖)
  apply Eventually.of_forall
  intro x
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_volterraL2Row_le hK hM hb x) (norm_nonneg _))

/-- The physical L² operator is represented by half the row inner product. -/
theorem volterraL2Operator_ae_inner_row (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    volterraL2Operator hK hM hb f =ᵐ[unitJacobiMeasure 0 0]
      fun x ↦ (1/2 : ℝ) * ⟪volterraL2Row hK hM hb x, f⟫_ℝ := by
  let hg := (memLp_inner_volterraL2Row hK hM hb f).const_mul (1/2 : ℝ)
  have he : volterraL2Operator hK hM hb f = hg.toLp _ := by
    apply ext_inner_left ℝ
    intro g
    rw [inner_volterraL2Operator,
      integral_prod _ (integrable_volterraL2_pair hK hM hb f g),
      ← integral_const_mul, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [Real.inner_apply, hx, inner_volterraL2Row]
    simp_rw [show ∀ y, volterraL2Kernel K (x,y)*(g x*f y) =
      g x*(volterraL2Kernel K (x,y)*f y) by intro y; ring]
    rw [integral_const_mul]
    ring
  rw [he]
  exact hg.coeFn_toLp

include hK in
private theorem continuousAt_volterra_row_off_diagonal
    (x : Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hne : y ≠ x) :
    ContinuousAt (fun s : Icc (0 : ℝ) 1 ↦ volterraL2Kernel K (s,y)) x := by
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · have he : ∀ᶠ s : Icc (0 : ℝ) 1 in 𝓝 x, y < (s : ℝ) :=
      continuous_subtype_val.continuousAt.eventually (lt_mem_nhds hyx)
    have ht : Tendsto (fun s : Icc (0 : ℝ) 1 ↦ (![s,y] : Fin 2 → ℝ))
        (𝓝 x) (𝓝[volterraTriangle] ![x,y]) :=
      tendsto_nhdsWithin_iff.mpr ⟨(by fun_prop : Continuous (fun s : Icc (0 : ℝ) 1 ↦ (![s,y] : Fin 2 → ℝ))).continuousAt, he.mono (fun s hs ↦ ⟨s.property, hy.1, hs.le⟩)⟩
    have hk := (hK ![x,y] ⟨x.property, hy.1, hyx.le⟩).tendsto.comp ht
    change Tendsto _ _ (𝓝 (volterraL2Kernel K (x,y)))
    rw [show volterraL2Kernel K (x,y) = K ![x,y] by
      simp [volterraL2Kernel, x.property, hy.1, hyx.le]]
    apply hk.congr'
    filter_upwards [he] with s hs
    simp only [volterraL2Kernel, s.property, show y ∈ Icc 0 (s : ℝ) from ⟨hy.1, hs.le⟩,
      and_self, ite_true, Function.comp_apply]
  · have he : ∀ᶠ s : Icc (0 : ℝ) 1 in 𝓝 x, (s : ℝ) < y :=
      continuous_subtype_val.continuousAt.eventually (gt_mem_nhds hxy)
    have hz : volterraL2Kernel K (x,y) = 0 := by
      simp [volterraL2Kernel, not_le.mpr hxy]
    rw [ContinuousAt, hz]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with s hs
    simp [volterraL2Kernel, not_le.mpr hs]

/-- A continuous triangle kernel has continuous rows in L², including at the endpoints. -/
theorem continuousOn_volterraL2Row : ContinuousOn (volterraL2Row hK hM hb) (Icc 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro x
  apply tendsto_L2_of_dominated
    (fun s : Icc (0 : ℝ) 1 ↦ fun y ↦ volterraL2Kernel K (s,y))
    (fun y ↦ volterraL2Kernel K (x,y))
    (fun s ↦ memLp_volterraL2Kernel_row hK hM hb s)
    (memLp_volterraL2Kernel_row hK hM hb x) (fun _ ↦ 2*M)
    (integrable_const _)
  · intro s
    apply Eventually.of_forall
    intro y
    exact (abs_sub _ _).trans (add_le_add (norm_volterraL2Kernel_le hM hb (s,y))
      (norm_volterraL2Kernel_le hM hb (x,y))) |>.trans_eq (by ring)
  · filter_upwards [ae_mem_Icc_unitJacobiMeasure 0 0, (unitJacobiMeasure 0 0).ae_ne (x : ℝ)]
      with y hy hne
    exact continuousAt_volterra_row_off_diagonal hK x hy hne

end Real
