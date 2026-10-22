/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Semiclassical Jacobi weight shifts and Pearson identity

Parameter raising is polynomial measure multiplication. Simultaneous unit
raising gives the cubic Pearson multiplier `x(1-x)(t-x)` and a quadratic
Pearson coefficient, with the third singularity outside the orthogonality interval.

Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.
-/

public section
open Set Real MeasureTheory Filter
open scoped Topology NNReal
namespace Polynomial

/-- Nonnegative integer parameter shifts multiply the weight by a polynomial. -/
private theorem semiclassicalJacobiWeight_add_nat_rpow (t α β γ : ℝ) (ht : 1 < t)
    (k l m : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    ((x : ℝ) ^ ((α + k)) * (1 - (x : ℝ)) ^ ((β + l)) * ((t : ℝ) - (x : ℝ)) ^ ((γ + m))) =
      (x ^ k * (1 - x) ^ l * (t - x) ^ m) * ((x : ℝ) ^ (α) * (1 - (x : ℝ)) ^ (β) * ((t : ℝ) - (x : ℝ)) ^ (γ)) := by
  rw [rpow_add hx.1, rpow_add (by linarith [hx.2] : 0 < 1 - x),
    rpow_add (by linarith [hx.2] : 0 < t - x)]
  simp only [rpow_natCast]
  ring

/-- The simultaneous unit shift is the cubic Pearson multiplier. -/
private theorem semiclassicalJacobiWeight_add_one_rpow (t α β γ : ℝ) (ht : 1 < t)
    {x : ℝ} (hx : x ∈ Ioo 0 1) :
    ((x : ℝ) ^ ((α + 1)) * (1 - (x : ℝ)) ^ ((β + 1)) * ((t : ℝ) - (x : ℝ)) ^ ((γ + 1))) =
      x * (1 - x) * (t - x) * ((x : ℝ) ^ (α) * (1 - (x : ℝ)) ^ (β) * ((t : ℝ) - (x : ℝ)) ^ (γ)) := by
  simpa using semiclassicalJacobiWeight_add_nat_rpow t α β γ ht 1 1 1 hx

/-- The shifted weight satisfies the cubic/quadratic Pearson derivative identity. -/
private theorem hasDerivAt_semiclassicalJacobiWeight_add_one_rpow (t α β γ : ℝ) (ht : 1 < t)
    {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt ((fun weightPoint : ℝ ↦ ((weightPoint : ℝ) ^ ((α + 1)) * (1 - (weightPoint : ℝ)) ^ ((β + 1)) * ((t : ℝ) - (weightPoint : ℝ)) ^ ((γ + 1)))))
      (((α + 1) * (1 - x) * (t - x) - (β + 1) * x * (t - x) -
        (γ + 1) * x * (1 - x)) * ((x : ℝ) ^ (α) * (1 - (x : ℝ)) ^ (β) * ((t : ℝ) - (x : ℝ)) ^ (γ))) x := by
  have ha := (hasDerivAt_id x).rpow_const (p := α + 1) (Or.inl (ne_of_gt hx.1))
  have hb := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).rpow_const
    (p := β + 1) (Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
  have hc := ((hasDerivAt_const x t).sub (hasDerivAt_id x)).rpow_const
    (p := γ + 1) (Or.inl (by change t - x ≠ 0; linarith [hx.2]))
  convert (ha.mul hb).mul hc using 1
  · rfl
  · dsimp []
    simp only [add_sub_cancel_right, zero_sub]
    rw [rpow_add hx.1, rpow_add (by linarith [hx.2] : 0 < 1 - x),
      rpow_add (by linarith [hx.2] : 0 < t - x)]
    simp only [rpow_one]
    ring

/-- Integer weight shifts on the classical open domain. -/
theorem semiclassicalJacobiWeight_add_nat (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (k l m : ℕ) (x : Ioo (0 : ℝ) 1) :
    (semiclassicalJacobiWeight t (α + k) (β + l) (γ + m) x : ℝ) =
      ((x : ℝ) ^ k * (1 - (x : ℝ)) ^ l * ((t : ℝ) - x) ^ m) *
        (semiclassicalJacobiWeight t α β γ x : ℝ) := by
  simp only [semiclassicalJacobiWeight_apply]
  exact semiclassicalJacobiWeight_add_nat_rpow t α β γ t.property k l m x.property

/-- Integer parameter raising is multiplication of classical domain-typed weights. -/
theorem semiclassicalJacobiMeasure_add_nat (t α β γ : ℝ) (ht : 1 < t)
    (k l m : ℕ) :
    semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α + k) (β + l) (γ + m) =
      openIntervalWeightMeasure 0 1
        (semiclassicalJacobiWeight ⟨t, ht⟩ α β γ *
          semiclassicalJacobiWeight ⟨t, ht⟩ k l m) := by
  change openIntervalWeightMeasure 0 1 _ = _
  congr 1
  ext x
  rw [ContinuousMap.mul_apply, NNReal.coe_mul, semiclassicalJacobiWeight_add_nat]
  simp only [semiclassicalJacobiWeight_apply, Real.rpow_natCast]
  ring

/-- The simultaneous unit shift on the classical domain. -/
theorem semiclassicalJacobiWeight_add_one (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (x : Ioo (0 : ℝ) 1) :
    (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) x : ℝ) =
      (x : ℝ) * (1 - (x : ℝ)) * ((t : ℝ) - x) *
        (semiclassicalJacobiWeight t α β γ x : ℝ) := by
  simp only [semiclassicalJacobiWeight_apply]
  exact semiclassicalJacobiWeight_add_one_rpow t α β γ t.property x.property

/-- Pearson differentiation asserted on the actual open domain. -/
theorem hasDerivAt_semiclassicalJacobiWeight_add_one (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (x : Ioo (0 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) y : ℝ))
      (((α + 1) * (1 - (x : ℝ)) * ((t : ℝ) - x) -
        (β + 1) * (x : ℝ) * ((t : ℝ) - x) - (γ + 1) * (x : ℝ) * (1 - (x : ℝ))) *
        (semiclassicalJacobiWeight t α β γ x : ℝ)) x := by
  classical
  let F : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (0 : ℝ) 1 then
    (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) ⟨y, h⟩ : ℝ) else 0
  refine ⟨F, fun y ↦ by
    have hy : (y : ℝ) ∈ Ioo (0 : ℝ) 1 := y.property
    simp only [F, dite_eq_left hy]
    rfl, ?_⟩
  have hev : F =ᶠ[𝓝 (x : ℝ)]
      (fun y ↦ y ^ (α + 1) * (1 - y) ^ (β + 1) * ((t : ℝ) - y) ^ (γ + 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds x.property] with y hy
    simp only [F, dite_eq_left hy, semiclassicalJacobiWeight_apply]
  exact (hasDerivAt_semiclassicalJacobiWeight_add_one_rpow t α β γ t.property
    x.property).congr_of_eventuallyEq hev

/-- The left endpoint is a limit; no restriction on the opposite exponent is needed. -/
theorem tendsto_semiclassicalJacobiWeight_add_one_zero (t : Ioi (1 : ℝ)) (β γ : ℝ)
    {α : ℝ} (hα : -1 < α) :
    Tendsto (fun x : Ioo (0 : ℝ) 1 ↦
      (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) x : ℝ))
      (Filter.comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hval : Tendsto (Subtype.val : Ioo (0 : ℝ) 1 → ℝ)
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 0) := Filter.tendsto_comap
  let u : Ioo (0 : ℝ) 1 → ℝ≥0 := fun x ↦ ⟨x, x.property.1.le⟩
  have hu : Tendsto u (Filter.comap Subtype.val (𝓝 0)) (𝓝 0) :=
    NNReal.tendsto_coe.mp hval
  have h1 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ (x : ℝ) ^ (α + 1))
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 0) := by
    have h := ((NNReal.continuous_rpow_const (by linarith : (0 : ℝ) ≤ α + 1)).tendsto 0).comp hu
    rw [NNReal.zero_rpow (by linarith : α + 1 ≠ 0)] at h
    exact NNReal.tendsto_coe.mpr h
  have h2 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ (1 - (x : ℝ)) ^ (β + 1))
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 ((1 - 0 : ℝ) ^ (β + 1))) :=
    ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))).tendsto.comp hval
  have h3 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) - x) ^ (γ + 1))
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 (((t : ℝ) - 0) ^ (γ + 1))) :=
    ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (by have ht : 1 < (t : ℝ) := t.property; dsimp; linarith))).tendsto.comp hval
  simpa only [semiclassicalJacobiWeight_apply, zero_mul] using (h1.mul h2).mul h3

/-- The right endpoint is a limit; the left exponent can be arbitrary. -/
theorem tendsto_semiclassicalJacobiWeight_add_one_one (t : Ioi (1 : ℝ)) (α γ : ℝ)
    {β : ℝ} (hβ : -1 < β) :
    Tendsto (fun x : Ioo (0 : ℝ) 1 ↦
      (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) x : ℝ))
      (Filter.comap Subtype.val (𝓝 (1 : ℝ))) (𝓝 0) := by
  have hval : Tendsto (Subtype.val : Ioo (0 : ℝ) 1 → ℝ)
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 1) := Filter.tendsto_comap
  let u : Ioo (0 : ℝ) 1 → ℝ≥0 := fun x ↦ ⟨1 - (x : ℝ), by linarith [x.property.2]⟩
  have hu : Tendsto u (Filter.comap Subtype.val (𝓝 1)) (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hval
    rw [sub_self] at h
    exact h
  have h1 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ (x : ℝ) ^ (α + 1))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 ((1 : ℝ) ^ (α + 1))) :=
    (continuousAt_id.rpow_const (Or.inl (by norm_num))).tendsto.comp hval
  have h2 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ (1 - (x : ℝ)) ^ (β + 1))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 0) := by
    have h := ((NNReal.continuous_rpow_const (by linarith : (0 : ℝ) ≤ β + 1)).tendsto 0).comp hu
    rw [NNReal.zero_rpow (by linarith : β + 1 ≠ 0)] at h
    exact NNReal.tendsto_coe.mpr h
  have h3 : Tendsto (fun x : Ioo (0 : ℝ) 1 ↦ ((t : ℝ) - x) ^ (γ + 1))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 (((t : ℝ) - 1) ^ (γ + 1))) :=
    ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (by have ht : 1 < (t : ℝ) := t.property; dsimp; linarith))).tendsto.comp hval
  simpa only [semiclassicalJacobiWeight_apply, mul_zero, zero_mul] using (h1.mul h2).mul h3

/-- In the integrable endpoint range the shifted weight has a continuous
closed-interval extension with both endpoint values zero. -/
theorem exists_continuous_semiclassicalJacobiWeight_add_one (t : Ioi (1 : ℝ))
    {α β γ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∃ F : C(Icc (0 : ℝ) 1, ℝ),
      (∀ x : Ioo (0 : ℝ) 1, F ⟨x, x.property.1.le, x.property.2.le⟩ =
        (semiclassicalJacobiWeight t (α + 1) (β + 1) (γ + 1) x : ℝ)) ∧
      F ⟨0, by constructor <;> norm_num⟩ = 0 ∧ F ⟨1, by constructor <;> norm_num⟩ = 0 := by
  let F : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun x ↦
    (x : ℝ) ^ (α + 1) * (1 - (x : ℝ)) ^ (β + 1) * ((t : ℝ) - x) ^ (γ + 1),
    ((continuous_subtype_val.rpow_const (fun _ ↦ Or.inr (by linarith : 0 ≤ α + 1))).mul
      ((continuous_const.sub continuous_subtype_val).rpow_const
        (fun _ ↦ Or.inr (by linarith : 0 ≤ β + 1)))).mul
      ((continuous_const.sub continuous_subtype_val).rpow_const
        (fun x ↦ Or.inl (by change (t : ℝ) - x ≠ 0; have ht : 1 < (t : ℝ) := t.property; linarith [x.property.2])))⟩
  refine ⟨F, fun _ ↦ rfl, ?_, ?_⟩
  · change (0 : ℝ)^(α+1) * (1-0)^(β+1) * ((t : ℝ)-0)^(γ+1) = 0
    simp [Real.zero_rpow (by linarith : α+1 ≠ 0)]
  · change (1 : ℝ)^(α+1) * (1-1)^(β+1) * ((t : ℝ)-1)^(γ+1) = 0
    simp [Real.zero_rpow (by linarith : β+1 ≠ 0)]

end Polynomial
