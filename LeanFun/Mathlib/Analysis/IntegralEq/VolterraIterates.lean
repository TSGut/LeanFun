/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraRows
public import LeanFun.Mathlib.Analysis.Normed.Operator.FactorialInverse
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Factorial bounds for Volterra iterates

Successive integration on the triangle yields a factorial denominator. This
proves second-kind invertibility with no smallness assumption on the kernel.
Reference: the classical successive-approximation argument for Volterra equations.
-/

public noncomputable section
open MeasureTheory Polynomial Set Filter ContinuousLinearMap
open scoped ENNReal Topology InnerProductSpace
namespace Real
local instance : IsFiniteMeasure (unitJacobiMeasure 0 0) :=
  isFiniteMeasure_unitJacobiMeasure (by norm_num) (by norm_num)

private theorem integral_unitJacobi_pow {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (∫ y in Icc 0 x, y ^ n ∂unitJacobiMeasure 0 0) =
      2 * (x ^ (n+1) / (n+1)) := by
  rw [unitJacobiMeasure_zero_zero, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc le_rfl hx.2), ← restrict_Ioc_eq_restrict_Icc,
    ← intervalIntegral.integral_of_le hx.1, integral_pow]
  norm_num

private theorem unitJacobi_mass_sqrt :
    (measureUnivNNReal (unitJacobiMeasure 0 0) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ = sqrt 2 := by
  norm_num [measureUnivNNReal, unitJacobiMeasure_zero_zero, sqrt_eq_rpow]
  change (2 : ℝ≥0∞).toReal ^ (1 / 2 : ℝ) = 2 ^ (1 / 2 : ℝ)
  norm_num

variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M)

/-- One Volterra application integrates a power majorant, gaining its next denominator. -/
theorem volterraL2Operator_ae_bound_of_power
    (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) {C : ℝ} (_hC : 0 ≤ C) (n : ℕ)
    (hf : ∀ᵐ y ∂unitJacobiMeasure 0 0, |f y| ≤ C * y ^ n) :
    ∀ᵐ x ∂unitJacobiMeasure 0 0,
      |volterraL2Operator hK hM hb f x| ≤ M * C * x ^ (n+1) / (n+1) := by
  filter_upwards [volterraL2Operator_ae_inner_row hK hM hb f,
    ae_mem_Icc_unitJacobiMeasure 0 0] with x hx hs
  rw [hx, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2), inner_volterraL2Row]
  have he : (fun y ↦ volterraL2Kernel K (x,y) * f y) =
      (Icc 0 x).indicator (fun y ↦ K ![x,y] * f y) := by
    funext y
    simp [volterraL2Kernel, hs, Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Icc]
  have hi : IntegrableOn (fun y : ℝ ↦ M * C * y ^ n) (Icc 0 x) (unitJacobiMeasure 0 0) :=
    (by fun_prop : Continuous (fun y : ℝ ↦ M * C * y ^ n)).continuousOn.integrableOn_compact
      isCompact_Icc
  have ha : ∀ᵐ y ∂(unitJacobiMeasure 0 0).restrict (Icc 0 x),
      ‖K ![x,y] * f y‖ ≤ M * C * y ^ n := by
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem measurableSet_Icc] with y hy hyx
    rw [norm_mul]
    exact (mul_le_mul (hb _ ⟨hs, hyx⟩) hy (abs_nonneg _) hM).trans_eq (by ring)
  have hm : AEStronglyMeasurable (fun y ↦ K ![x,y] * f y)
      ((unitJacobiMeasure 0 0).restrict (Icc 0 x)) := by
    apply AEStronglyMeasurable.mul
    · exact (hK.comp (by fun_prop) (fun y hy ↦ ⟨hs, hy⟩)).aestronglyMeasurable measurableSet_Icc
    · exact (Lp.memLp f).aestronglyMeasurable.restrict
  have hi' := hi.mono' hm ha
  have hn := (norm_integral_le_integral_norm (fun y ↦ K ![x,y] * f y)
    (μ := (unitJacobiMeasure 0 0).restrict (Icc 0 x))).trans
      (integral_mono_ae hi'.norm hi ha)
  rw [integral_const_mul, integral_unitJacobi_pow hs n] at hn
  have hh := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 1/2)
  convert hh using 1
  ring

/-- The pointwise majorant for successive Volterra iterates gains a factorial. -/
theorem volterraL2Operator_pow_succ_ae_le
    (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) (n : ℕ) :
    ∀ᵐ x ∂unitJacobiMeasure 0 0,
      |((volterraL2Operator hK hM hb) ^ (n+1)) f x| ≤
        (sqrt 2 / 2 * ‖f‖) * M ^ (n+1) * x ^ n / n.factorial := by
  induction n with
  | zero =>
    filter_upwards [volterraL2Operator_ae_inner_row hK hM hb f] with x hx
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [hx, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    have hr := norm_volterraL2Row_le hK hM hb x
    rw [unitJacobi_mass_sqrt] at hr
    have hn := (norm_inner_le_norm (𝕜 := ℝ) (volterraL2Row hK hM hb x) f).trans
      (mul_le_mul_of_nonneg_right hr (norm_nonneg f))
    rw [Real.norm_eq_abs] at hn
    nlinarith
  | succ n ih =>
    have hh := volterraL2Operator_ae_bound_of_power hK hM hb
      (((volterraL2Operator hK hM hb) ^ (n+1)) f)
      (C := (sqrt 2 / 2 * ‖f‖) * M ^ (n+1) / n.factorial)
      (by positivity) n (ih.mono (fun x hx ↦ by convert hx using 1; ring))
    filter_upwards [hh] with x hx
    simpa only [pow_succ', mul_apply_eq_comp, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] using hx.trans_eq (by
        field_simp
        ring)

/-- A factorial bound for powers of the physical operator, with no small-kernel assumption. -/
theorem norm_volterraL2Operator_pow_succ_le (n : ℕ) :
    ‖(volterraL2Operator hK hM hb) ^ (n+1)‖ ≤ M ^ (n+1) / n.factorial := by
  apply opNorm_le_bound _ (by positivity)
  intro f
  have ha : ∀ᵐ x ∂unitJacobiMeasure 0 0,
      ‖(((volterraL2Operator hK hM hb) ^ (n+1)) f) x‖ ≤
        (sqrt 2 / 2 * ‖f‖) * M ^ (n+1) / n.factorial := by
    filter_upwards [volterraL2Operator_pow_succ_ae_le hK hM hb f n,
      ae_mem_Icc_unitJacobiMeasure 0 0] with x hx hs
    apply hx.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hs.1 hs.2)
  have hh := Lp.norm_le_of_ae_bound (by positivity) ha
  rw [unitJacobi_mass_sqrt] at hh
  convert hh using 1
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  linear_combination -(M ^ (n+1) * ‖f‖) * hs

/-- The Volterra Neumann series converges in operator norm for every continuous kernel. -/
theorem summable_pow_volterraL2Operator :
    Summable (fun n : ℕ ↦ (volterraL2Operator hK hM hb) ^ n) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial M).mul_left M)
  intro n
  exact (norm_volterraL2Operator_pow_succ_le hK hM hb n).trans_eq (by rw [pow_succ']; ring)

/-- Every continuous-kernel Volterra equation of the second kind is invertible on L². -/
theorem isUnit_one_sub_volterraL2Operator : IsUnit (1 - volterraL2Operator hK hM hb) :=
  isUnit_one_sub_of_summable_pow _ (summable_pow_volterraL2Operator hK hM hb)

/-- Each L² right-hand side has exactly one second-kind Volterra solution. -/
theorem existsUnique_volterraL2_solution (f : Lp ℝ 2 (unitJacobiMeasure 0 0)) :
    ∃! u, u - volterraL2Operator hK hM hb u = f :=
  existsUnique_sub_apply_eq_of_summable_pow _ (summable_pow_volterraL2Operator hK hM hb) f

end Real
