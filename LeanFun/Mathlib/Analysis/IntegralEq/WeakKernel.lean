/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.Schur
public import LeanFun.Mathlib.MeasureTheory.Measure.ClassicalProduct
/-! # Classical weak L² kernels

Absolute integrability of every weak pairing is part of the kernel data.
Rectangle tests assert integrability as well as the Cauchy–Schwarz bound.
Reference: L² kernel testing and Gutleb–Carrillo–Olver, arXiv:2011.00045, §2.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
noncomputable section
namespace MeasureTheory

structure L2WeakKernel {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  product_measurable : AEMeasurable (fun x : X => Measure.map (Prod.mk x) μ) μ
  kernel : X × X → ℝ
  operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
  pair_integrable : ∀ f g : Lp ℝ 2 μ,
    Integrable (fun z : X × X ↦ kernel z*(g z.1*f z.2)) (μ.prod μ)
  pairing : ∀ f g : Lp ℝ 2 μ,
    ⟪g,operator f⟫_ℝ = ∫ z : X × X, kernel z*(g z.1*f z.2) ∂μ.prod μ

theorem L2WeakKernel.spec {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : L2WeakKernel μ) (f g : Lp ℝ 2 μ) :
    Integrable (fun z : X × X ↦ K.kernel z*(g z.1*f z.2)) (μ.prod μ) ∧
    ⟪g,K.operator f⟫_ℝ = ∫ z : X × X, K.kernel z*(g z.1*f z.2) ∂μ.prod μ :=
  ⟨K.pair_integrable f g,K.pairing f g⟩

-- The existing generic product input is recovered without another measure choice.
def L2WeakKernel.productInput {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : L2WeakKernel μ) : ProductMeasureInput (β := X) μ :=
  ⟨μ, K.product_measurable⟩

/-- S-finite measures automatically supply the classical product certificate. -/
def L2WeakKernel.ofSFinite {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [SFinite μ] (kernel : X × X → ℝ)
    (operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hi : ∀ f g : Lp ℝ 2 μ,
      Integrable (fun z : X × X => kernel z*(g z.1*f z.2)) (μ.prod μ))
    (hp : ∀ f g : Lp ℝ 2 μ,
      ⟪g,operator f⟫_ℝ = ∫ z : X × X, kernel z*(g z.1*f z.2) ∂μ.prod μ) :
    L2WeakKernel μ :=
  ⟨(ProductMeasureInput.ofSFinite μ μ).measurable,kernel,operator,hi,hp⟩

theorem L2WeakKernel.quasiMeasurePreserving_fst {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (K : L2WeakKernel μ) :
    QuasiMeasurePreserving Prod.fst (μ.prod μ) μ := by
  refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_⟩
  rw [Measure.map_apply measurable_fst hs]
  have hp := K.productInput.prod_apply (measurable_fst hs)
  simp only [L2WeakKernel.productInput] at hp
  rw [hp]
  have ha : ∀ᵐ x ∂μ, x ∉ s := by simpa [ae_iff] using hzero
  rw [← lintegral_zero (μ := μ)]
  apply lintegral_congr_ae
  filter_upwards [ha] with x hx
  simp [Set.preimage, hx]

theorem L2WeakKernel.quasiMeasurePreserving_snd {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (K : L2WeakKernel μ) :
    QuasiMeasurePreserving Prod.snd (μ.prod μ) μ := by
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  have hp := K.productInput.prod_apply (measurable_snd hs)
  simp only [L2WeakKernel.productInput] at hp
  rw [hp]
  change (∫⁻ _ : X, μ s ∂μ) = 0
  simp only [hzero, lintegral_zero]

theorem L2WeakKernel.pairing_representatives {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (K : L2WeakKernel μ) (f g : Lp ℝ 2 μ)
    (u v : X → ℝ) (hu : u =ᵐ[μ] g) (hv : v =ᵐ[μ] f) :
    Integrable (fun z : X × X => K.kernel z * (u z.1*v z.2)) (μ.prod μ) ∧
    (∫ z, K.kernel z * (u z.1*v z.2) ∂μ.prod μ) = ⟪g,K.operator f⟫_ℝ := by
  have he : (fun z : X × X => K.kernel z * (u z.1*v z.2)) =ᵐ[μ.prod μ]
      (fun z => K.kernel z * (g z.1*f z.2)) := by
    filter_upwards [K.quasiMeasurePreserving_fst.ae hu,
      K.quasiMeasurePreserving_snd.ae hv] with z hz hz'
    rw [hz,hz']
  exact ⟨(K.pair_integrable f g).congr he.symm,
    (integral_congr_ae he).trans (K.pairing f g).symm⟩


theorem L2WeakKernel.integrableOn_rectangle {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (K : L2WeakKernel μ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IntegrableOn K.kernel (A ×ˢ B) (μ.prod μ) := by
  let u := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let v := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  have he : (fun z : X × X ↦ K.kernel z*(v z.1*u z.2)) =ᵐ[μ.prod μ]
      (A ×ˢ B).indicator K.kernel := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ))),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top μ B) (c := (1 : ℝ)))] with z hz hz'
    change v z.1 = A.indicator (fun _ ↦ (1 : ℝ)) z.1 at hz
    change u z.2 = B.indicator (fun _ ↦ (1 : ℝ)) z.2 at hz'
    rw [hz,hz']
    by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [ha,hb]
  exact (integrable_indicator_iff (hA.prod hB)).mp ((K.pair_integrable u v).congr he)

theorem L2WeakKernel.rectangle_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (K : L2WeakKernel μ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IntegrableOn K.kernel (A ×ˢ B) (μ.prod μ) ∧
    ‖∫ z in A ×ˢ B, K.kernel z ∂μ.prod μ‖ ≤
      ‖K.operator‖*Real.sqrt (μ.real A)*Real.sqrt (μ.real B) := by
  refine ⟨K.integrableOn_rectangle hA hB,?_⟩
  let u := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let v := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  have he : (fun z : X × X ↦ K.kernel z*(v z.1*u z.2)) =ᵐ[μ.prod μ]
      (A ×ˢ B).indicator K.kernel := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ))),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top μ B) (c := (1 : ℝ)))] with z hz hz'
    change v z.1 = A.indicator (fun _ ↦ (1 : ℝ)) z.1 at hz
    change u z.2 = B.indicator (fun _ ↦ (1 : ℝ)) z.2 at hz'
    rw [hz, hz']
    by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [ha, hb]
  have hn (S : Set X) (hS : MeasurableSet S) :
      ‖indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)‖ = Real.sqrt (μ.real S) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow, Measure.real]
  rw [← integral_indicator (hA.prod hB), ← integral_congr_ae he, ← K.pairing u v]
  calc
    _ ≤ ‖v‖ * ‖K.operator u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖K.operator‖ * ‖u‖) := mul_le_mul_of_nonneg_left (K.operator.le_opNorm u) (norm_nonneg _)
    _ = _ := by rw [show ‖v‖ = _ from hn A hA, show ‖u‖ = _ from hn B hB]; ring

end MeasureTheory
