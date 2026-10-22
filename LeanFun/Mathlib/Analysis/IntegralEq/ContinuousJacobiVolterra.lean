/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiVolterraL2
public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraL2

/-! # Continuous kernels in the weighted reflected Volterra realization

Continuity is required only on the physical triangle. The zero extension
provides a measurable representative; the joint measure supplies both Jacobi
marginals. Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real
local notation "μ" => unitJacobiMeasure 1 0
local notation "κ" => jacobiVolterraJoint

/-- Reflection carries almost every joint-measure point to the physical triangle. -/
theorem ae_reflected_mem_volterraTriangle :
    ∀ᵐ z ∂κ, (![1-z.1,z.2] : Fin 2 → ℝ) ∈ volterraTriangle := by
  filter_upwards [ae_mem_jacobiVolterraJoint] with z hz
  change (1-z.1) ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc 0 (1-z.1)
  exact ⟨⟨by linarith [hz.1.2],by linarith [hz.1.1]⟩,
    ⟨hz.2.1.1,by linarith [hz.2.2]⟩⟩

private theorem reflected_kernel_ae (K : (Fin 2 → ℝ) → ℝ) :
    (fun z : ℝ × ℝ ↦ volterraL2Kernel K (1-z.1,z.2)) =ᵐ[κ]
      (fun z ↦ K ![1-z.1,z.2]) := by
  filter_upwards [ae_reflected_mem_volterraTriangle] with z hz
  exact ite_eq_left hz

variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)

/-- The averaged reflected Volterra map on the shifted Jacobi weighted L² space. -/
def jacobiVolterraL2Operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  marginalKernelL2Operator μ μ κ map_fst_jacobiVolterraJoint
    map_snd_jacobiVolterraJoint (fun z ↦ volterraL2Kernel K (1-z.1,z.2))
    ((measurable_volterraL2Kernel hK).comp (by fun_prop)).aestronglyMeasurable hM
    (Eventually.of_forall (fun z ↦ norm_volterraL2Kernel_le hM bK (1-z.1,z.2)))

/-- A uniform physical kernel bound controls the weighted operator norm. -/
theorem norm_jacobiVolterraL2Operator_le : ‖jacobiVolterraL2Operator hK hM bK‖ ≤ M :=
  norm_marginalKernelL2Operator_le ..

include hK hM bK in
/-- The actual continuous-kernel weak pairing is integrable. -/
theorem integrable_jacobiVolterra_pair (f g : Lp ℝ 2 μ) :
    Integrable (fun z : ℝ × ℝ ↦ K ![1-z.1,z.2] * (g z.1*f z.2)) κ := by
  have hi := integrable_marginalKernelL2_pair μ μ κ map_fst_jacobiVolterraJoint
    map_snd_jacobiVolterraJoint (fun z ↦ volterraL2Kernel K (1-z.1,z.2))
    ((measurable_volterraL2Kernel hK).comp (by fun_prop)).aestronglyMeasurable hM
    (Eventually.of_forall (fun z ↦ norm_volterraL2Kernel_le hM bK (1-z.1,z.2))) f g
  apply hi.congr
  filter_upwards [reflected_kernel_ae K] with z hz
  rw [hz]

/-- The weak joint-measure representation uses the original kernel on its physical triangle. -/
theorem inner_jacobiVolterraL2Operator_joint (f g : Lp ℝ 2 μ) :
    ⟪g,jacobiVolterraL2Operator hK hM bK f⟫_ℝ =
      ∫ z : ℝ × ℝ, K ![1-z.1,z.2] * (g z.1*f z.2) ∂κ := by
  rw [jacobiVolterraL2Operator, inner_marginalKernelL2Operator]
  apply integral_congr_ae
  filter_upwards [reflected_kernel_ae K] with z hz
  rw [hz]

/-- The weak physical formula retains reflection, endpoint averaging and measure scaling. -/
theorem inner_jacobiVolterraL2Operator (f g : Lp ℝ 2 μ) :
    ⟪g,jacobiVolterraL2Operator hK hM bK f⟫_ℝ =
      4 * ∫ s : Ioo (0 : ℝ) 1, g s * volterraIntegral
        (.ofJacobiOneZeroLp hK f
          ⟨1-(s : ℝ), by constructor <;> linarith [s.property.1, s.property.2]⟩)
        ∂(volume : Measure ℝ).comap Subtype.val := by
  simp only [VolterraIntegralInput.ofJacobiOneZeroLp,
    VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel]
  rw [integral_subtype_comap measurableSet_Ioo
    (fun s : ℝ ↦ g s * ∫ y in (0 : ℝ)..(1-s), K ![1-s,y] * f y),
    ← integral_Icc_eq_integral_Ioo]
  rw [inner_jacobiVolterraL2Operator_joint,
    integral_jacobiVolterraJoint _ (integrable_jacobiVolterra_pair hK hM bK f g)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  ring

/-- The continuous-kernel construction agrees with the previous polynomial realization. -/
theorem jacobiVolterraL2Operator_polynomial (p : MvPolynomial (Fin 2) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (bp : ∀ z ∈ volterraTriangle, |MvPolynomial.eval z p| ≤ B) :
    jacobiVolterraL2Operator p.continuous_eval.continuousOn hB bp =
      MvPolynomial.jacobiVolterraL2Operator p hB bp := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [inner_jacobiVolterraL2Operator, MvPolynomial.inner_jacobiVolterraL2Operator]

variable {L : (Fin 2 → ℝ) → ℝ} (hL : ContinuousOn L volterraTriangle)
  {N δ : ℝ} (hN : 0 ≤ N) (bL : ∀ z ∈ volterraTriangle, |L z| ≤ N)
  (hδ : 0 ≤ δ) (he : ∀ z ∈ volterraTriangle, |K z-L z| ≤ δ)

/-- Subtracting continuous kernels subtracts their weighted realizations. -/
theorem jacobiVolterraL2Operator_sub :
    jacobiVolterraL2Operator hK hM bK-jacobiVolterraL2Operator hL hN bL =
      jacobiVolterraL2Operator (hK.sub hL) hδ he := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [sub_apply, inner_sub_right]
  simp only [inner_jacobiVolterraL2Operator_joint]
  rw [← integral_sub (integrable_jacobiVolterra_pair hK hM bK f g)
    (integrable_jacobiVolterra_pair hL hN bL f g)]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring

include hδ he in
/-- Uniform kernel error controls the weighted, unpreconditioned operator error. -/
theorem norm_jacobiVolterraL2Operator_sub_le :
    ‖jacobiVolterraL2Operator hK hM bK-jacobiVolterraL2Operator hL hN bL‖ ≤ δ := by
  rw [jacobiVolterraL2Operator_sub hK hM bK hL hN bL hδ he]
  exact norm_jacobiVolterraL2Operator_le (hK.sub hL) hδ he

end Real
