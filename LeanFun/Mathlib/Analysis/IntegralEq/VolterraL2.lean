/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.BoundedKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousVolterraPrimitive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCompleteness
public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisOperator
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Bounded Volterra operators and normalized coefficient sections

The affine Legendre measure is twice Lebesgue measure on [0,1]. A factor 1/2
in the kernel realization gives the physical Volterra integral. Coordinates
use normalized shifted Legendre polynomials. Reference: Gutleb–Olver,
arXiv:1906.03907, Sections 3.1–3.2, and the bounded-kernel Schur test.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The affine Legendre measure includes the factor two from its original mass. -/
theorem unitJacobiMeasure_zero_zero : unitJacobiMeasure 0 0 =
    (2 : ℝ≥0∞) • volume.restrict (Icc (0 : ℝ) 1) := by
  let := isFiniteMeasure_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0)
  let : IsFiniteMeasure ((2 : ℝ≥0∞) • volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : IntegrableInput (unitJacobiMeasure 0 0) := ⟨f, by
      rw [unitJacobiMeasure, integrable_map_measure f.continuous.aestronglyMeasurable (by fun_prop)]
      exact integrable_jacobiMeasure (by norm_num) (by norm_num)
        (f.continuous.comp (by fun_prop)).continuousOn⟩
  have hg : Measurable g.val := by dsimp [g]; fun_prop
  have hd : (∫ x, g.val x ∂unitJacobiMeasure 0 0) = 2 *
      ∫ x in (0 : ℝ)..1, g.val x := by
    rw [integral_unitJacobiMeasure_subtype 0 0 g hg]
    simp only [unitJacobiWeight_apply, zero_add, Real.rpow_one, Real.rpow_zero,
      mul_one]
    rw [integral_const_mul, integral_subtype measurableSet_Ioo g.val,
      restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  dsimp only [g] at hd
  rw [hd, integral_smul_measure]
  norm_num
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← restrict_Ioc_eq_restrict_Icc]

end Polynomial
namespace Real

/-- Volterra kernel, extended by zero off its physical triangle. -/
def volterraL2Kernel (K : (Fin 2 → ℝ) → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc 0 z.1 then K ![z.1,z.2] else 0

/-- Continuity on the triangle suffices for measurability of the zero extension. -/
theorem measurable_volterraL2Kernel {K : (Fin 2 → ℝ) → ℝ}
    (hK : ContinuousOn K volterraTriangle) : Measurable (volterraL2Kernel K) := by
  apply ContinuousOn.measurable_piecewise
    (f := fun z : ℝ × ℝ ↦ K ![z.1,z.2]) (g := fun _ ↦ (0 : ℝ))
    (s := {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc 0 z.1})
  · exact hK.comp (by fun_prop) (fun z hz ↦ hz)
  · fun_prop
  · exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))

/-- A triangle bound is a global bound for the zero-extended kernel. -/
theorem norm_volterraL2Kernel_le {K : (Fin 2 → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M) (z : ℝ × ℝ) :
    ‖volterraL2Kernel K z‖ ≤ M := by
  unfold volterraL2Kernel
  split_ifs with hz
  · exact hb _ hz
  · simpa using hM

local instance : IsFiniteMeasure (unitJacobiMeasure 0 0) :=
  isFiniteMeasure_unitJacobiMeasure (by norm_num) (by norm_num)

variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M)

/-- The physical Volterra operator on L² of the affine Legendre measure. -/
def volterraL2Operator :
    Lp ℝ 2 (unitJacobiMeasure 0 0) →L[ℝ] Lp ℝ 2 (unitJacobiMeasure 0 0) :=
  (1/2 : ℝ) • boundedKernelL2Operator _ _ (volterraL2Kernel K)
    (measurable_volterraL2Kernel hK).aestronglyMeasurable hM
    (Filter.Eventually.of_forall (norm_volterraL2Kernel_le hM hb))

/-- The kernel supremum bounds the physical Volterra operator norm. -/
theorem norm_volterraL2Operator_le : ‖volterraL2Operator hK hM hb‖ ≤ M := by
  have hm : (unitJacobiMeasure 0 0) univ = 2 := by
    rw [unitJacobiMeasure_zero_zero]
    simp
  rw [volterraL2Operator, norm_smul]
  have hh := norm_boundedKernelL2Operator_le (unitJacobiMeasure 0 0)
    (unitJacobiMeasure 0 0) (volterraL2Kernel K)
    (measurable_volterraL2Kernel hK).aestronglyMeasurable hM
    (Filter.Eventually.of_forall (norm_volterraL2Kernel_le hM hb))
  rw [hm] at hh
  norm_num only [ENNReal.toReal_ofNat] at hh
  have hs : sqrt 2 * (M * sqrt 2) = 2*M := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs] at hh
  norm_num only [norm_div, norm_one, norm_ofNat]
  linarith

/-- Weak pairing for every pair of L² functions. -/
theorem inner_volterraL2Operator (f g : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    ⟪g, volterraL2Operator hK hM hb f⟫_ℝ =
      (1/2 : ℝ) * ∫ z, volterraL2Kernel K z * (g z.1*f z.2)
        ∂(unitJacobiMeasure 0 0).prod (unitJacobiMeasure 0 0) := by
  rw [volterraL2Operator, smul_apply, inner_smul_right,
    inner_boundedKernelL2Operator]

include hK hM hb in
/-- The original weak kernel pairing is absolutely integrable on the square. -/
theorem integrable_volterraL2_pair (f g : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    Integrable (fun z ↦ volterraL2Kernel K z * (g z.1*f z.2))
      ((unitJacobiMeasure 0 0).prod (unitJacobiMeasure 0 0)) :=
  integrable_boundedKernelL2_pair _ _ _ (measurable_volterraL2Kernel hK).aestronglyMeasurable
    hM (Filter.Eventually.of_forall (norm_volterraL2Kernel_le hM hb)) f g

/-- L² data for the affine Legendre measure are integrable on the physical interval. -/
theorem integrableOn_coe_unitLegendreLp (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    IntegrableOn (fun y ↦ f y) (Icc (0 : ℝ) 1) := by
  have hi := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  conv at hi => arg 2; rw [unitJacobiMeasure_zero_zero]
  exact (integrable_smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hi

/-- Every L² input supplies an integrable continuous-kernel row on the physical interval. -/
def VolterraIntegralInput.ofUnitLegendreLp
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) (x : Icc (0 : ℝ) 1) :
    VolterraIntegralInput (x : ℝ) :=
  .ofContinuousKernel hK (f := fun y ↦ f y) x (by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le x.property.1]
    exact (integrableOn_coe_unitLegendreLp f).mono_set
      (fun y hy ↦ ⟨hy.1.le, hy.2.trans x.property.2⟩))

/-- The zero-extended kernel row is twice the physical integral, matching the affine measure. -/
private theorem integral_volterraL2Kernel_bridge (K : (Fin 2 → ℝ) → ℝ) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (_hi : IntervalIntegrable (fun y ↦ K ![x,y]*f y) volume 0 x) :
    (∫ y, volterraL2Kernel K (x,y)*f y ∂unitJacobiMeasure 0 0) =
      2*(∫ y in (0 : ℝ)..x, K ![x,y]*f y) := by
  rw [unitJacobiMeasure_zero_zero, integral_smul_measure]
  norm_num only [ENNReal.toReal_ofNat, smul_eq_mul]
  simp only [volterraL2Kernel, hx, true_and, ite_mul, zero_mul]
  have he : (fun y ↦ if y ∈ Icc 0 x then K ![x,y]*f y else 0) =
      (Icc 0 x).indicator (fun y ↦ K ![x,y]*f y) := by
    funext y
    simp only [Set.indicator_apply]
  rw [he]
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc le_rfl hx.2),
    intervalIntegral.integral_of_le hx.1, ← restrict_Ioc_eq_restrict_Icc]

/-- An existing physical row integral has the affine Legendre normalization factor two. -/
theorem integral_volterraL2Kernel (K : (Fin 2 → ℝ) → ℝ) (f : ℝ → ℝ)
    (x : Icc (0 : ℝ) 1)
    (hi : IntervalIntegrable (fun y ↦ K ![(x : ℝ),y]*f y) volume 0 (x : ℝ)) :
    (∫ y, volterraL2Kernel K ((x : ℝ),y)*f y ∂unitJacobiMeasure 0 0) =
      2*volterraIntegral (.ofKernel K f hi) := by
  rw [volterraIntegral_ofKernel]
  exact integral_volterraL2Kernel_bridge K f x.property hi

/-- Fubini identifies the L² realization with classical integrals on the physical interval. -/
theorem inner_volterraL2Operator_eq_integral (f g : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    ⟪g, volterraL2Operator hK hM hb f⟫_ℝ =
      ∫ x : Icc (0 : ℝ) 1, g x * volterraIntegral (.ofUnitLegendreLp hK f x)
        ∂(unitJacobiMeasure 0 0).comap Subtype.val := by
  simp only [VolterraIntegralInput.ofUnitLegendreLp,
    VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel]
  rw [integral_subtype_comap (μ := unitJacobiMeasure 0 0) measurableSet_Icc
    (fun x : ℝ ↦ g x * ∫ y in (0 : ℝ)..x, K ![x,y]*f y),
    Measure.restrict_eq_self_of_ae_mem (ae_mem_Icc_unitJacobiMeasure 0 0)]
  rw [inner_volterraL2Operator, integral_prod _ (integrable_volterraL2_pair hK hM hb f g),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_mem_Icc_unitJacobiMeasure 0 0] with x hx
  simp_rw [show ∀ y, volterraL2Kernel K (x,y)*(g x*f y) =
    g x*(volterraL2Kernel K (x,y)*f y) by intro y; ring]
  rw [integral_const_mul, integral_volterraL2Kernel_bridge K f hx
    (intervalIntegrable_continuousVolterra_mul_row hK ⟨x,hx⟩ (by
      apply intervalIntegrable_iff.mpr
      rw [uIoc_of_le hx.1]
      exact (integrableOn_coe_unitLegendreLp f).mono_set
        (fun y hy ↦ ⟨hy.1.le, hy.2.trans hx.2⟩)))]
  ring

/-- The Volterra operator in normalized shifted Legendre coordinates. -/
def volterraL2CoefficientOperator :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0) (by norm_num)).coefficientOperator
    (volterraL2Operator hK hM hb)

/-- Coordinate transport preserves the physical Volterra norm bound. -/
theorem norm_volterraL2CoefficientOperator_le : ‖volterraL2CoefficientOperator hK hM hb‖ ≤ M := by
  rw [volterraL2CoefficientOperator, HilbertBasis.norm_coefficientOperator]
  exact norm_volterraL2Operator_le hK hM hb

/-- Normalized coordinates represent the Volterra action exactly. -/
theorem volterraL2CoefficientOperator_repr (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    let b := hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0)
    volterraL2CoefficientOperator hK hM hb (b.repr f) =
      b.repr (volterraL2Operator hK hM hb f) :=
  (hilbertBasisShiftedJacobi (by norm_num) (by norm_num)).coefficientOperator_repr _ f

/-- Leading normalized sections converge strongly for all square-summable inputs. -/
theorem tendsto_volterraL2CoefficientOperator_finiteSections (c : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun n ↦ lp.initialL2Projection n
      (volterraL2CoefficientOperator hK hM hb (lp.initialL2Projection n c)))
      atTop (𝓝 (volterraL2CoefficientOperator hK hM hb c)) := by
  simpa only [lp.initialL2Projection_apply] using
    lp.tendsto_initialL2Sections (volterraL2CoefficientOperator hK hM hb) c

end Real
