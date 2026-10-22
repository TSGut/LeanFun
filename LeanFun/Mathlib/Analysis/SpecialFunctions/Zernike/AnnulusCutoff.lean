/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SmoothTransition.BoundaryFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusWeakGradient
public import LeanFun.Mathlib.Analysis.IntegralEq.L2Dominated
/-! # Smooth approximation of annular boundary-vanishing polynomials

Cut off the two linearly vanishing boundary factors separately. The resulting
compactly supported smooth functions converge, together with their Cartesian
first derivatives, in the annular area L² space.
Reference: Evans, *Partial Differential Equations*, Chapter 5, smooth density
in zero-boundary Sobolev spaces.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace MvPolynomial.AnnularEnergy
local notation "E" => (Fin 2 → ℝ)
private def box : Set E := Icc (fun _ ↦ -1) (fun _ ↦ 1)
private theorem radius_mem_box {x : E} (hx : x 0^2+x 1^2 ≤ 1) : x ∈ box := by
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

private theorem compact_C1_bound {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  refine ⟨max (max A B) 0,le_max_right _ _,fun x hx ↦ ⟨?_,?_⟩⟩
  · exact (hA x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hB x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

private theorem cutoff_C1_bound {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ K →
      |boundaryFactor a (f x)| ≤ C ∧
      ‖fderiv ℝ (fun y ↦ boundaryFactor a (f y)) x‖ ≤ C := by
  obtain ⟨M,hM,_,hd⟩ := exists_transition_deriv_bound
  obtain ⟨B,hB,hfB⟩ := compact_C1_bound hK hf
  refine ⟨max B ((1+2*M)*B),hB.trans (le_max_left _ _),fun a x hx ↦ ⟨?_,?_⟩⟩
  · exact ((abs_boundaryFactor_le a (f x)).trans (hfB x hx).1).trans (le_max_left _ _)
  · have hbf : HasDerivAt (boundaryFactor a) (deriv (boundaryFactor a) (f x)) (f x) :=
      ((boundaryFactor_contDiff a).differentiable (by simp)).differentiableAt.hasDerivAt
    change ‖fderiv ℝ (boundaryFactor a ∘ f) x‖ ≤ _
    rw [(hbf.comp_hasFDerivAt x (hf.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv,
      norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (abs_deriv_boundaryFactor_le hd a (f x)) (hfB x hx).2
      (norm_nonneg _) (by positivity)).trans (le_max_right _ _)

private theorem mul_C1_bound {K : Set E} {f g : ℕ → E → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfC : ∀ n x, x ∈ K → |f n x| ≤ C ∧ ‖fderiv ℝ (f n) x‖ ≤ C)
    (hgD : ∀ n x, x ∈ K → |g n x| ≤ D ∧ ‖fderiv ℝ (g n) x‖ ≤ D) :
    ∀ n x, x ∈ K → |f n x*g n x| ≤ 2*C*D ∧
      ‖fderiv ℝ (fun y ↦ f n y*g n y) x‖ ≤ 2*C*D := by
  intro n x hx
  obtain ⟨hfv,hfd⟩ := hfC n x hx
  obtain ⟨hgv,hgd⟩ := hgD n x hx
  constructor
  · rw [abs_mul]
    have h := mul_le_mul hfv hgv (abs_nonneg _) hC
    nlinarith [mul_nonneg hC hD]
  · rw [fderiv_fun_mul ((hf n).differentiable (by simp)).differentiableAt
      ((hg n).differentiable (by simp)).differentiableAt]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := mul_le_mul hfv hgd (norm_nonneg _) hC
    have h2 := mul_le_mul hgv hfd (norm_nonneg _) hD
    nlinarith

/-- Cut off both boundary factors of a Cartesian polynomial trial. -/
def cutoffTrial (q : ℝ) (a : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x : E) : ℝ :=
  boundaryFactor a (x 0^2+x 1^2-q) *
    boundaryFactor a (1-(x 0^2+x 1^2)) * eval x p

/-- The cutoff trial is smooth on the entire Cartesian plane. -/
theorem cutoffTrial_contDiff (q a : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ ∞ (cutoffTrial q a p) := by
  unfold cutoffTrial
  exact (((boundaryFactor_contDiff a).comp (by fun_prop)).mul
    ((boundaryFactor_contDiff a).comp (by fun_prop))).mul (p.contDiff_eval.of_le (by simp))

private theorem cutoff_support {q a : ℝ} (ha : 0 < a) (p : MvPolynomial (Fin 2) ℝ) :
    Function.support (cutoffTrial q a p) ⊆
      {x : E | q+1/a ≤ x 0^2+x 1^2 ∧ x 0^2+x 1^2 ≤ 1-1/a} := by
  intro x hx
  have h0 : 1 < a*(x 0^2+x 1^2-q) := by
    by_contra h
    have hh := boundaryFactor_zero (le_of_not_gt h)
    exact hx (by simp only [cutoffTrial, hh, zero_mul])
  have h1 : 1 < a*(1-(x 0^2+x 1^2)) := by
    by_contra h
    have hh := boundaryFactor_zero (le_of_not_gt h)
    exact hx (by simp only [cutoffTrial, hh, mul_zero, zero_mul])
  have h0' : 1/a < x 0^2+x 1^2-q := (div_lt_iff₀ ha).mpr (by nlinarith)
  have h1' : 1/a < 1-(x 0^2+x 1^2) := (div_lt_iff₀ ha).mpr (by nlinarith)
  constructor <;> linarith

/-- Positive cutoff scales give compact support strictly inside the annulus. -/
theorem cutoffTrial_support (q : Ioo (0 : ℝ) 1) {a : ℝ} (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℝ) :
    HasCompactSupport (cutoffTrial q a p) ∧ tsupport (cutoffTrial q a p) ⊆ domain q := by
  let K : Set E := {x | (q : ℝ)+1/a ≤ x 0^2+x 1^2 ∧ x 0^2+x 1^2 ≤ 1-1/a}
  have hc : IsClosed K := by
    have hr : Continuous (fun x : E ↦ x 0^2+x 1^2) := by fun_prop
    exact (isClosed_le continuous_const hr).inter (isClosed_le hr continuous_const)
  have hs : tsupport (cutoffTrial q a p) ⊆ K := closure_minimal (cutoff_support ha p) hc
  have hk : K ⊆ box := by
    intro x hx
    apply radius_mem_box
    have h := hx.2
    have : 0 < 1/a := by positivity
    linarith
  refine ⟨(isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs.trans hk)), ?_⟩
  intro x hx
  have h := hs hx
  change (q : ℝ) < x 0^2+x 1^2 ∧ x 0^2+x 1^2 < 1
  have : 0 < 1/a := by positivity
  constructor <;> linarith [h.1,h.2]

/-- Smooth compactly supported approximants at increasing positive scales. -/
def cutoffTest (q : Ioo (0 : ℝ) 1) (p : MvPolynomial (Fin 2) ℝ) (n : ℕ) :
    TestFunction (domain q) ℝ ⊤ :=
  ⟨cutoffTrial q ((n : ℝ)+1) p,cutoffTrial_contDiff _ _ _,
    (cutoffTrial_support q (by positivity) p).1,(cutoffTrial_support q (by positivity) p).2⟩

private theorem eventually_scaled_gt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, 2 < ((n : ℝ)+1)*r := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact (ht.atTop_mul_const hr).eventually_gt_atTop 2

/-- At every interior point the approximants eventually agree locally with the trial. -/
theorem cutoffTest_eventuallyEq (q : Ioo (0 : ℝ) 1) (p : MvPolynomial (Fin 2) ℝ)
    {x : E} (hx : x ∈ domain q) :
    ∀ᶠ n : ℕ in atTop,
      (cutoffTest q p n : E → ℝ) =ᶠ[𝓝 x] (fun y ↦ eval y (annulusBoundaryWeight q*p)) := by
  have h0 : 0 < x 0^2+x 1^2-(q : ℝ) := sub_pos.mpr hx.1
  have h1 : 0 < 1-(x 0^2+x 1^2) := sub_pos.mpr hx.2
  filter_upwards [eventually_scaled_gt h0,eventually_scaled_gt h1] with n hn0 hn1
  have hc0 : Continuous (fun y : E ↦ ((n : ℝ)+1)*(y 0^2+y 1^2-(q : ℝ))) := by fun_prop
  have hc1 : Continuous (fun y : E ↦ ((n : ℝ)+1)*(1-(y 0^2+y 1^2))) := by fun_prop
  filter_upwards [hc0.continuousAt.eventually (eventually_gt_nhds hn0),
    hc1.continuousAt.eventually (eventually_gt_nhds hn1)] with y hy0 hy1
  change cutoffTrial q ((n : ℝ)+1) p y = _
  simp only [cutoffTrial,boundaryFactor_eq hy0.le,boundaryFactor_eq hy1.le,
    annulusBoundaryWeight,eval_mul,eval_sub,map_one,eval_add,eval_pow,eval_X,eval_C]
  ring


private theorem cutoffTrial_uniform_bound (q : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x ∈ box,
      |cutoffTrial q ((n : ℝ)+1) p x| ≤ C ∧
      ‖fderiv ℝ (cutoffTrial q ((n : ℝ)+1) p) x‖ ≤ C := by
  have hK : IsCompact box := isCompact_Icc
  have hf0 : ContDiff ℝ ∞ (fun x : E ↦ x 0^2+x 1^2-q) := by fun_prop
  have hf1 : ContDiff ℝ ∞ (fun x : E ↦ 1-(x 0^2+x 1^2)) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun x : E ↦ eval x p) := p.contDiff_eval.of_le (by simp)
  obtain ⟨C,hC,hfC⟩ := cutoff_C1_bound hK hf0
  obtain ⟨D,hD,hgD⟩ := cutoff_C1_bound hK hf1
  obtain ⟨P,hP,hpP⟩ := compact_C1_bound hK hp
  have hf (n : ℕ) := (boundaryFactor_contDiff ((n : ℝ)+1)).comp hf0
  have hg (n : ℕ) := (boundaryFactor_contDiff ((n : ℝ)+1)).comp hf1
  have hfg := mul_C1_bound hf hg hC hD (fun n ↦ hfC ((n : ℝ)+1))
    (fun n ↦ hgD ((n : ℝ)+1))
  refine ⟨2*(2*C*D)*P,by positivity,?_⟩
  exact mul_C1_bound (fun n ↦ (hf n).mul (hg n)) (fun _ ↦ hp) (by positivity) hP hfg
    (fun _ ↦ hpP)

private theorem ae_mem_domain (q : Ioo (0 : ℝ) 1) :
    ∀ᵐ x ∂zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0, x ∈ domain q := by
  rw [zernikeAnnulusMeasure_zero_zero_eq_volume q.property]
  exact ae_restrict_mem (domain q).isOpen.measurableSet

private theorem tendsto_testL2_of_bound (q : Ioo (0 : ℝ) 1)
    (φ : ℕ → TestFunction (domain q) ℝ ⊤) (p : MvPolynomial (Fin 2) ℝ) {C : ℝ}
    (hb : ∀ n x, x ∈ domain q → |φ n x| ≤ C)
    (ht : ∀ x ∈ domain q, Tendsto (fun n ↦ φ n x) atTop (𝓝 (eval x p))) :
    Tendsto (fun n ↦ physicalTestL2 q (φ n)) atTop
      (𝓝 (polynomialToL2 (physicalMeasure_moments q) p)) := by
  let : IsFiniteMeasure (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) :=
    (physicalMeasure_moments q).isFiniteMeasure
  obtain ⟨D,_,hD⟩ := compact_C1_bound (show IsCompact box from isCompact_Icc)
    (p.contDiff_eval.of_le (by simp) : ContDiff ℝ ∞ (fun x : E ↦ eval x p))
  have heq : polynomialToL2 (physicalMeasure_moments q) p =
      (memLp_eval_of_hasFiniteMoments (physicalMeasure_moments q) p).toLp (fun x ↦ eval x p) := by
    apply Lp.ext
    exact (coe_polynomialToL2 (physicalMeasure_moments q) p).trans
      (MemLp.coeFn_toLp _).symm
  rw [heq]
  exact tendsto_L2_of_dominated (fun n x ↦ φ n x) (fun x ↦ eval x p)
    (fun n ↦ test_memLp q (φ n)) (memLp_eval_of_hasFiniteMoments (physicalMeasure_moments q) p)
    (fun _ ↦ C+D) (integrable_const _)
    (fun n ↦ (ae_mem_domain q).mono (fun x hx ↦ by
      have h := abs_sub_le (φ n x) 0 (eval x p)
      simp only [sub_zero,zero_sub,abs_neg] at h
      exact h.trans (add_le_add (hb n x hx) (hD x (radius_mem_box hx.2.le)).1)))
    ((ae_mem_domain q).mono ht)

/-- The cutoff approximants converge to the boundary-vanishing trial in L². -/
theorem tendsto_cutoffTest_L2 (q : Ioo (0 : ℝ) 1) (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun n ↦ physicalTestL2 q (cutoffTest q p n)) atTop
      (𝓝 (polynomialToL2 (physicalMeasure_moments q) (annulusBoundaryWeight q*p))) := by
  obtain ⟨C,_,hC⟩ := cutoffTrial_uniform_bound q p
  apply tendsto_testL2_of_bound q (cutoffTest q p) (annulusBoundaryWeight q*p)
    (fun n x hx ↦ (hC n x (radius_mem_box hx.2.le)).1)
  intro x hx
  exact (tendsto_congr' ((cutoffTest_eventuallyEq q p hx).mono
    (fun _ h ↦ h.eq_of_nhds))).mpr tendsto_const_nhds

/-- Each Cartesian first derivative converges in L² to the polynomial derivative. -/
theorem tendsto_cutoffTest_derivative_L2 (q : Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    Tendsto (fun n ↦ physicalTestL2 q (DirichletSpace.testDerivative (domain q) i
      (cutoffTest q p n))) atTop
      (𝓝 (polynomialToL2 (physicalMeasure_moments q) (pderiv i (annulusBoundaryWeight q*p)))) := by
  obtain ⟨C,_,hC⟩ := cutoffTrial_uniform_bound q p
  apply tendsto_testL2_of_bound q
    (fun n ↦ DirichletSpace.testDerivative (domain q) i (cutoffTest q p n))
    (pderiv i (annulusBoundaryWeight q*p)) (C := C)
  · intro n x hx
    rw [DirichletSpace.testDerivative_apply]
    have h := (fderiv ℝ (cutoffTest q p n) x).le_opNorm (Pi.single i 1)
    simp only [Pi.norm_single, norm_one, mul_one] at h
    exact h.trans (hC n x (radius_mem_box hx.2.le)).2
  · intro x hx
    apply (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [cutoffTest_eventuallyEq q p hx] with n hn
    rw [DirichletSpace.testDerivative_apply, hn.fderiv_eq, fderiv_eval_single]
end MvPolynomial.AnnularEnergy
