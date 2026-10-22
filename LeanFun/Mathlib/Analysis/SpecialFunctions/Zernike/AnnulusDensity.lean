/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.MultivariateC1
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusSobolevInclusion
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPolynomialGraph
public import Mathlib.Analysis.SpecificLimits.Basic
/-! # Boundary-preserving polynomial approximation of smooth annular tests

A compactly supported smooth test divided by the annular boundary polynomial
extends smoothly across both circles. Approximate this quotient in C¹ on the
containing square and multiply back by the boundary polynomial. The product
rule and dominated convergence give simultaneous L² convergence of the values
and Cartesian derivatives. Closedness then puts the smooth-test graph in the
completed polynomial energy image.
Reference: Evans, *Partial Differential Equations*, Chapter 5.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MvPolynomial.AnnularEnergy
local notation "E" => (Fin 2 → ℝ)
private def box : Set E := Icc (fun _ ↦ -1) (fun _ ↦ 1)
private theorem radius_mem_box {x : E} (hx : x 0^2+x 1^2 ≤ 1) : x ∈ box := by
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
private theorem smooth_supported_division {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h : ∀ x ∈ tsupport f, g x ≠ 0) :
    ContDiff ℝ ∞ (fun x ↦ f x / g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt.div hg.contDiffAt (h x hx)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_div]

/-- A smooth compactly supported annular test has a globally smooth boundary quotient. -/
theorem exists_smooth_boundary_quotient (q : Ioo (0 : ℝ) 1)
    (φ : TestFunction (domain q) ℝ ⊤) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ x, eval x (annulusBoundaryWeight q) * g x = φ x := by
  have hb : ∀ x ∈ tsupport φ, eval x (annulusBoundaryWeight q) ≠ 0 := by
    intro x hx
    have hx' := φ.tsupport_subset hx
    have hp := mul_pos (sub_pos.mpr hx'.2) (sub_pos.mpr hx'.1)
    simpa only [annulusBoundaryWeight,eval_mul,eval_sub,map_one,eval_add,eval_pow,eval_X,eval_C]
      using hp.ne'
  refine ⟨fun x ↦ φ x / eval x (annulusBoundaryWeight q),
    smooth_supported_division φ.contDiff
      ((annulusBoundaryWeight (q : ℝ)).contDiff_eval.of_le (by simp)) hb, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_div_cancel₀ _ (hb x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

private theorem tendsto_polynomial_L2_of_error (q : Ioo (0 : ℝ) 1)
    {f : E → ℝ} (hf : MemLp f 2 (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0))
    (p : ℕ → MvPolynomial (Fin 2) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, x ∈ box → |eval x (p n)-f x| ≤ C * (1/((n : ℝ)+1))) :
    Tendsto (fun n ↦ polynomialToL2 (physicalMeasure_moments q) (p n)) atTop
      (𝓝 (hf.toLp f)) := by
  let : IsFiniteMeasure (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) := (physicalMeasure_moments q).isFiniteMeasure
  have ha : ∀ᵐ x ∂zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0, x ∈ box :=
    (ae_sq_radius_le_one_zernikeAnnulusMeasure q.property 0 0).mono (fun _ hx ↦ radius_mem_box hx)
  have ht (x : E) (hx : x ∈ box) : Tendsto (fun n ↦ eval x (p n)) atTop (𝓝 (f x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ hb n x hx)
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  have hd (n : ℕ) : (1 : ℝ)/((n : ℝ)+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simp
  have he (n : ℕ) :
      (memLp_eval_of_hasFiniteMoments (physicalMeasure_moments q) (p n)).toLp (fun x ↦ eval x (p n)) =
      polynomialToL2 (physicalMeasure_moments q) (p n) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (coe_polynomialToL2 (physicalMeasure_moments q) (p n)).symm
  simpa only [he] using tendsto_L2_of_dominated (fun n x ↦ eval x (p n)) f
    (fun n ↦ memLp_eval_of_hasFiniteMoments (physicalMeasure_moments q) (p n)) hf
    (fun _ ↦ C) (integrable_const _)
    (fun n ↦ ha.mono (fun x hx ↦ (hb n x hx).trans (by nlinarith [hd n])))
    (ha.mono ht)

private theorem boundary_bound (q : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ box,
    |eval x (annulusBoundaryWeight q)| ≤ M ∧
      ∀ i : Fin 2, |eval x (pderiv i (annulusBoundaryWeight q))| ≤ M := by
  have hK : IsCompact box := isCompact_Icc
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (annulusBoundaryWeight q).continuous_eval.continuousOn
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (pderiv 0 (annulusBoundaryWeight q)).continuous_eval.continuousOn
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (pderiv 1 (annulusBoundaryWeight q)).continuous_eval.continuousOn
  refine ⟨max (max A B) (max C 0),(le_max_right C 0).trans (le_max_right _ _),fun x hx ↦ ⟨?_,?_⟩⟩
  · exact (hA x hx).trans ((le_max_left A B).trans (le_max_left _ _))
  · intro i
    fin_cases i
    · exact (hB x hx).trans ((le_max_right A B).trans (le_max_left _ _))
    · exact (hC x hx).trans ((le_max_left C 0).trans (le_max_right _ _))

private theorem boundary_mul_error (q : Ioo (0 : ℝ) 1)
    (φ : TestFunction (domain q) ℝ ⊤) {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (he : ∀ x, eval x (annulusBoundaryWeight q)*g x = φ x)
    (p : MvPolynomial (Fin 2) ℝ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hB : ∀ x ∈ box, |eval x (annulusBoundaryWeight q)| ≤ M ∧
      ∀ i : Fin 2, |eval x (pderiv i (annulusBoundaryWeight q))| ≤ M)
    (hp : ∀ x ∈ box, |eval x p-g x| ≤ δ ∧
      ∀ i : Fin 2, |eval x (pderiv i p)-fderiv ℝ g x (Pi.single i 1)| ≤ δ)
    (x : E) (hx : x ∈ box) :
    |eval x (annulusBoundaryWeight q*p)-φ x| ≤ 2*M*δ ∧
    ∀ i : Fin 2, |eval x (pderiv i (annulusBoundaryWeight q*p))-
      DirichletSpace.testDerivative (domain q) i φ x| ≤ 2*M*δ := by
  have hbx := hB x hx
  have hpx := hp x hx
  constructor
  · calc
      _ = |eval x (annulusBoundaryWeight q)*(eval x p-g x)| := by
        rw [eval_mul,← he x]; congr 1; ring
      _ = |eval x (annulusBoundaryWeight q)| * |eval x p-g x| := abs_mul _ _
      _ ≤ M*δ := mul_le_mul hbx.1 hpx.1 (abs_nonneg _) hM
      _ ≤ 2*M*δ := by nlinarith [mul_nonneg hM hδ]
  · intro i
    have hd := congrArg (fun f : E → ℝ ↦ fderiv ℝ f x (Pi.single i 1)) (funext he)
    rw [fderiv_fun_mul
      ((annulusBoundaryWeight (q : ℝ)).contDiff_eval.differentiable (by simp)).differentiableAt
      (hg.differentiable (by simp)).differentiableAt] at hd
    simp only [add_apply,smul_apply,smul_eq_mul,fderiv_eval_single] at hd
    calc
      _ = |eval x (pderiv i (annulusBoundaryWeight q))*(eval x p-g x) +
          eval x (annulusBoundaryWeight q)*(eval x (pderiv i p)-fderiv ℝ g x (Pi.single i 1))| := by
        rw [DirichletSpace.testDerivative_apply,← hd]
        simp only [pderiv_mul,eval_add,eval_mul]
        congr 1
        ring
      _ ≤ |eval x (pderiv i (annulusBoundaryWeight q))*(eval x p-g x)| +
          |eval x (annulusBoundaryWeight q)*(eval x (pderiv i p)-fderiv ℝ g x (Pi.single i 1))| :=
        abs_add_le _ _
      _ = |eval x (pderiv i (annulusBoundaryWeight q))| * |eval x p-g x| +
          |eval x (annulusBoundaryWeight q)| * |eval x (pderiv i p)-fderiv ℝ g x (Pi.single i 1)| := by
        rw [abs_mul,abs_mul]
      _ ≤ M*δ + M*δ := add_le_add
        (mul_le_mul (hbx.2 i) hpx.1 (abs_nonneg _) hM)
        (mul_le_mul hbx.1 (hpx.2 i) (abs_nonneg _) hM)
      _ = 2*M*δ := by ring

/-- Boundary-vanishing polynomials approximate every smooth annular test and its gradient in L². -/
theorem exists_boundary_polynomial_approximation (q : Ioo (0 : ℝ) 1)
    (φ : TestFunction (domain q) ℝ ⊤) :
    ∃ p : ℕ → MvPolynomial (Fin 2) ℝ,
      Tendsto (fun n ↦ (polynomialToL2 (physicalMeasure_moments q) (annulusBoundaryWeight q*p n),
        polynomialGradient q (annulusBoundaryWeight q*p n))) atTop
        (𝓝 (physicalTestL2 q φ, physicalTestGradient q φ)) := by
  obtain ⟨g,hg,he⟩ := exists_smooth_boundary_quotient q φ
  choose p hp using (fun n : ℕ ↦ exists_polynomial_C1_near_on_square hg
    (show (0 : ℝ) < 1/((n : ℝ)+1) by positivity))
  obtain ⟨M,hM,hB⟩ := boundary_bound q
  have hb (n : ℕ) (x : E) (hx : x ∈ box) := boundary_mul_error q φ hg he (p n) hM
    (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)+1)) hB
    (fun x hx ↦ ⟨(hp n x hx).1.le,fun i ↦ ((hp n x hx).2 i).le⟩) x hx
  have ht0 : Tendsto (fun n ↦ polynomialToL2 (physicalMeasure_moments q) (annulusBoundaryWeight q*p n))
      atTop (𝓝 (physicalTestL2 q φ)) :=
    tendsto_polynomial_L2_of_error q (test_memLp q φ) _ (by positivity : 0 ≤ 2*M)
      (fun n x hx ↦ (hb n x hx).1)
  have ht (i : Fin 2) : Tendsto
      (fun n ↦ polynomialToL2 (physicalMeasure_moments q) (pderiv i (annulusBoundaryWeight q*p n)))
      atTop (𝓝 (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i φ))) :=
    tendsto_polynomial_L2_of_error q (test_memLp q _) _ (by positivity : 0 ≤ 2*M)
      (fun n x hx ↦ (hb n x hx).2 i)
  have htG : Tendsto (fun n ↦ polynomialGradient q (annulusBoundaryWeight q*p n)) atTop
      (𝓝 (physicalTestGradient q φ)) := by
    have h : Tendsto (fun n ↦ ∑ i : Fin 2, lp.single 2 i
        (polynomialToL2 (physicalMeasure_moments q) (pderiv i (annulusBoundaryWeight q*p n)))) atTop
        (𝓝 (∑ i : Fin 2, lp.single 2 i (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i φ)))) := by
      apply tendsto_finsetSum
      intro i _
      exact (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 i).continuous.tendsto _
        |>.comp (ht i)
    simpa [physicalTestGradient,polynomialGradient,Fin.sum_univ_two] using h
  exact ⟨p,ht0.prodMk_nhds htG⟩

/-- Every smooth annular test graph belongs to the completed polynomial energy image. -/
theorem physicalTestGraph_mem_range (q : Ioo (0 : ℝ) 1)
    (φ : TestFunction (domain q) ℝ ⊤) :
    (physicalTestL2 q φ,physicalTestGradient q φ) ∈ Set.range (functionGradient q) := by
  obtain ⟨p,hp⟩ := exists_boundary_polynomial_approximation q φ
  apply (isClosed_range_functionGradient q).mem_of_tendsto hp
  exact Filter.Eventually.of_forall (fun n ↦ exists_functionGradient_polynomial q (p n))
end MvPolynomial.AnnularEnergy
