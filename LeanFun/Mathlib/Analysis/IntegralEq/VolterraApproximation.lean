/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Stability and approximation of Volterra integrals

Integrability is carried by pairs of rows on the open interval between zero
and the endpoint. This gives classical oriented integrals without assigning
values to divergent rows or evaluating either factor at an excluded endpoint.
Separate kernel and input errors on the physical triangle `0 ≤ y ≤ x ≤ 1`.
Reference: Gutleb–Olver, arXiv:1906.03907, Sections 3.1–3.2.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Real

/-- A pair of classical rows with an integrable product on the open integration interval. -/
structure VolterraIntegralInput (x : ℝ) where
  kernel : Ioo (min 0 x) (max 0 x) → ℝ
  input : Ioo (min 0 x) (max 0 x) → ℝ
  integrable : Integrable (fun y ↦ kernel y * input y)
    ((volume : Measure ℝ).comap Subtype.val)

/-- Restriction of a globally given row whose oriented integral exists. -/
def VolterraIntegralInput.ofKernel (K : (Fin 2 → ℝ) → ℝ) (f : ℝ → ℝ)
    {x : ℝ} (h : IntervalIntegrable (fun y ↦ K ![x,y] * f y) volume 0 x) :
    VolterraIntegralInput x where
  kernel y := K ![x,(y : ℝ)]
  input y := f y
  integrable := by
    have hi := intervalIntegrable_iff.mp h
    rw [uIoc, integrableOn_Ioc_iff_integrableOn_Ioo] at hi
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hi

/-- The classical oriented integral of an integrable kernel-input row pair. -/
def volterraIntegral {x : ℝ} (d : VolterraIntegralInput x) : ℝ :=
  if 0 ≤ x then ∫ y, d.kernel y * d.input y ∂(volume : Measure ℝ).comap Subtype.val else -(∫ y, d.kernel y * d.input y ∂(volume : Measure ℝ).comap Subtype.val)

/-- Nonnegative endpoints give the integral over the open row interval. -/
theorem volterraIntegral_of_nonneg {x : ℝ} (hx : 0 ≤ x) (d : VolterraIntegralInput x) :
    volterraIntegral d =
      ∫ y, d.kernel y * d.input y ∂(volume : Measure ℝ).comap Subtype.val :=
  ite_eq_left hx

/-- Negative endpoints reverse orientation. -/
theorem volterraIntegral_of_neg {x : ℝ} (hx : x < 0) (d : VolterraIntegralInput x) :
    volterraIntegral d =
      -(∫ y, d.kernel y * d.input y ∂(volume : Measure ℝ).comap Subtype.val) :=
  ite_eq_right (not_le.mpr hx)

/-- A zero-length row has value zero, without evaluating either factor. -/
theorem volterraIntegral_zero (d : VolterraIntegralInput 0) : volterraIntegral d = 0 := by
  have : IsEmpty (Ioo (min (0 : ℝ) 0) (max 0 0)) :=
    ⟨fun y ↦ (lt_irrefl (0 : ℝ)) (by
      simpa only [min_self, max_self] using lt_trans y.property.1 y.property.2)⟩
  rw [volterraIntegral_of_nonneg (le_refl 0)]
  exact integral_of_isEmpty

/-- Agreement with the oriented integral for globally defined, integrable rows. -/
theorem volterraIntegral_ofKernel (K : (Fin 2 → ℝ) → ℝ) (f : ℝ → ℝ)
    {x : ℝ} (h : IntervalIntegrable (fun y ↦ K ![x,y] * f y) volume 0 x) :
    volterraIntegral (VolterraIntegralInput.ofKernel K f h) =
      ∫ y in (0 : ℝ)..x, K ![x,y] * f y := by
  unfold volterraIntegral
  split_ifs with hx
  · change (∫ y : Ioo (min 0 x) (max 0 x), K ![x,(y : ℝ)] * f y ∂(volume : Measure ℝ).comap Subtype.val) = _
    rw [integral_subtype_comap (μ := volume)
      (s := Ioo (min 0 x) (max 0 x)) measurableSet_Ioo (fun y : ℝ ↦ K ![x,y] * f y), min_eq_left hx, max_eq_right hx,
      ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hx]
  · change -(∫ y : Ioo (min 0 x) (max 0 x), K ![x,(y : ℝ)] * f y ∂(volume : Measure ℝ).comap Subtype.val) = _
    have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [integral_subtype_comap (μ := volume)
      (s := Ioo (min 0 x) (max 0 x)) measurableSet_Ioo (fun y : ℝ ↦ K ![x,y] * f y), min_eq_right hx', max_eq_left hx',
      ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_ge hx']

/-- The physical triangle for Volterra integration on the unit interval. -/
def volterraTriangle : Set (Fin 2 → ℝ) :=
  {z | z 0 ∈ Icc 0 1 ∧ z 1 ∈ Icc 0 (z 0)}

/-- Continuous triangle kernels and continuous inputs give integrable slices. -/
theorem intervalIntegrable_volterra {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hf : ContinuousOn f (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    IntervalIntegrable (fun y ↦ K ![x,y] * f y) volume 0 x := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by exact hx.1)
  apply ContinuousOn.mul
  · apply hK.comp (by fun_prop : ContinuousOn (fun y : ℝ ↦ ![x,y]) (Icc 0 x))
    intro y hy
    exact ⟨hx, hy⟩
  · exact hf.mono (Icc_subset_Icc le_rfl hx.2)

/-- Continuous triangle data supply each physical row pair. -/
def VolterraIntegralInput.ofContinuous
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hf : ContinuousOn f (Icc 0 1))
    (x : Icc (0 : ℝ) 1) : VolterraIntegralInput (x : ℝ) :=
  VolterraIntegralInput.ofKernel K f (intervalIntegrable_volterra hK hf x.property)

/-- Kernel and input errors contribute separately, including their cross term. -/
theorem abs_volterraIntegral_sub_le {K L : (Fin 2 → ℝ) → ℝ} {f g : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hL : ContinuousOn L volterraTriangle)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    {M F δ η : ℝ} (hM : 0 ≤ M) (_hF : 0 ≤ F) (hδ : 0 ≤ δ) (_hη : 0 ≤ η)
    (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)
    (bf : ∀ y ∈ Icc 0 1, |f y| ≤ F)
    (eK : ∀ z ∈ volterraTriangle, |L z-K z| ≤ δ)
    (ef : ∀ y ∈ Icc 0 1, |g y-f y| ≤ η)
    (x : Icc (0 : ℝ) 1) :
    |volterraIntegral (VolterraIntegralInput.ofContinuous hL hg x) -
      volterraIntegral (VolterraIntegralInput.ofContinuous hK hf x)| ≤
      (δ*F + (M+δ)*η)*x := by
  have hx := x.property
  simp only [VolterraIntegralInput.ofContinuous, volterraIntegral_ofKernel]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_volterra hL hg hx)
    (intervalIntegrable_volterra hK hf hx)]
  have hb : ∀ y ∈ uIoc (0 : ℝ) x,
      ‖L ![x,y]*g y-K ![x,y]*f y‖ ≤ δ*F+(M+δ)*η := by
    intro y hy
    rw [uIoc_of_le hx.1] at hy
    have hyx : y ∈ Icc (0 : ℝ) (x : ℝ) := Ioc_subset_Icc_self hy
    have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hyx.1, hyx.2.trans hx.2⟩
    have hz : (![x,y] : Fin 2 → ℝ) ∈ volterraTriangle := ⟨hx, hyx⟩
    have bL : |L ![x,y]| ≤ M+δ := by
      calc
        _ = |K ![x,y]+(L ![x,y]-K ![x,y])| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ M+δ := add_le_add (bK _ hz) (eK _ hz)
    rw [Real.norm_eq_abs]
    calc
      _ = |(L ![x,y]-K ![x,y])*f y + L ![x,y]*(g y-f y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ δ*F+(M+δ)*η := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (eK _ hz) (bf y hy1) (abs_nonneg _) hδ)
          (mul_le_mul bL (ef y hy1) (abs_nonneg _) (by positivity))
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Vanishing uniform kernel and input error bounds give uniform output convergence. -/
theorem tendstoUniformly_volterraIntegral_of_error_bounds
    {K : (Fin 2 → ℝ) → ℝ} {L : ℕ → (Fin 2 → ℝ) → ℝ}
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hL : ∀ n, ContinuousOn (L n) volterraTriangle)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ∀ n, ContinuousOn (g n) (Icc 0 1))
    {M F : ℝ} (hM : 0 ≤ M) (hF : 0 ≤ F)
    (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M) (bf : ∀ y ∈ Icc 0 1, |f y| ≤ F)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hη : ∀ n, 0 ≤ η n)
    (eK : ∀ n z, z ∈ volterraTriangle → |L n z-K z| ≤ δ n)
    (ef : ∀ n y, y ∈ Icc 0 1 → |g n y-f y| ≤ η n)
    (tδ : Tendsto δ atTop (𝓝 0)) (tη : Tendsto η atTop (𝓝 0)) :
    TendstoUniformly
      (fun n (x : Icc (0 : ℝ) 1) ↦ volterraIntegral
        (VolterraIntegralInput.ofContinuous (hL n) (hg n) x))
      (fun x ↦ volterraIntegral (VolterraIntegralInput.ofContinuous hK hf x)) atTop := by
  have ht : Tendsto (fun n ↦ δ n*F+(M+δ n)*η n) atTop (𝓝 0) := by
    simpa using (tδ.mul_const F).add ((tδ.const_add M).mul tη)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact ((abs_volterraIntegral_sub_le hK (hL n) hf (hg n) hM hF (hδ n) (hη n)
    bK bf (eK n) (ef n) x).trans (mul_le_of_le_one_right
      (by have := hδ n; have := hη n; positivity) x.property.2)).trans_lt hn


end Real
