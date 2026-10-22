/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.FirstOrderFiniteSection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesDifferentiation

/-! # Function reconstruction for preconditioned first-order solves
Square-summable preconditioned coordinates give absolutely convergent Chebyshev
series. Endpoint data and analytic differentiation agree with the bordered
operator, and coefficient convergence implies uniform function convergence.
Reference: Olver--Townsend (2013), Section 4; ATAP, Chapter 21.
-/

public section
namespace Polynomial.Chebyshev
open Filter Set Complex
open scoped Topology ENNReal

/-- The preconditioned endpoint functional is its actual convergent series. -/
theorem hasSum_firstOrderBoundary (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    HasSum (fun n ↦ (-1 : ℂ) ^ n * (firstOrderPreconditioner x) n) (firstOrderBoundary x) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) firstOrderBoundaryVector x
  convert h using 1
  · funext n
    rw [RCLike.inner_apply']
    change (-1 : ℂ) ^ n * (firstOrderDiagonal n * x n) =
      star ((-1 : ℂ) ^ n * firstOrderDiagonal n) * x n
    simp [firstOrderDiagonal, mul_assoc]
  · rfl

/-- Preconditioning makes the coefficients absolutely summable, with a uniform bound. -/
theorem summable_norm_firstOrderPreconditioner (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    Summable (fun n ↦ ‖firstOrderPreconditioner x n‖) ∧
      (∑' n, ‖firstOrderPreconditioner x n‖) ≤ ‖firstOrderBoundaryVector‖ * ‖x‖ := by
  have h := lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal) firstOrderBoundaryVector x
  simpa only [firstOrderBoundaryVector, firstOrderPreconditioner_apply, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul] using h

/-- Preconditioned coefficients give a convergent point at every interval point. -/
@[expose] noncomputable def ComplexChebyshevSeriesPoint.ofFirstOrder
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (t : Icc (-1 : ℝ) 1) :
    ComplexChebyshevSeriesPoint (firstOrderPreconditioner x) :=
  .ofAbsolute (summable_norm_firstOrderPreconditioner x).1 t

@[simp] theorem ComplexChebyshevSeriesPoint.ofFirstOrder_val
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (t : Icc (-1 : ℝ) 1) :
    (ComplexChebyshevSeriesPoint.ofFirstOrder x t).val = (t.val : ℂ) := rfl

/-- The boundary row is the actual series value at the left endpoint. -/
theorem complexChebyshevSeries_firstOrderPreconditioner_neg_one
    (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    complexChebyshevSeries (firstOrderPreconditioner x)
      (.ofFirstOrder x ⟨-1, by constructor <;> norm_num⟩) = firstOrderBoundary x := by
  apply complexChebyshevSeries_eq_of_tendsto
  simpa only [ComplexChebyshevSeriesPoint.ofFirstOrder_val, ofReal_neg, ofReal_one,
    T_eval_neg_one, Int.cast_negOnePow_natCast, mul_comm] using
    (hasSum_firstOrderBoundary x).tendsto_sum_nat

/-- Reconstruction is uniformly bounded on the full typed interval. -/
theorem norm_complexChebyshevSeries_firstOrderPreconditioner_le
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (t : Icc (-1 : ℝ) 1) :
    ‖complexChebyshevSeries (firstOrderPreconditioner x) (.ofFirstOrder x t)‖ ≤
      ‖firstOrderBoundaryVector‖ * ‖x‖ :=
  (norm_complexChebyshevSeries_le_tsum (summable_norm_firstOrderPreconditioner x).1 t).trans
    (summable_norm_firstOrderPreconditioner x).2

/-- Differentiation cancels the preconditioner diagonal in the U basis. -/
theorem hasSum_derivative_firstOrderPreconditioner
    (x : lp (fun _ : ℕ ↦ ℂ) 2) {C ρ : ℝ} (hρ : 1 < ρ)
    (hx : ∀ n, ‖firstOrderPreconditioner x n‖ ≤ C / ρ ^ n)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ x (n + 1) * (Polynomial.Chebyshev.U ℂ n).eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ hx 1) z) := by
  have h := hasSum_gegenbauer_derivative_complexChebyshevSeries hρ hx z
  convert h using 1
  funext n
  rw [firstOrderPreconditioner_apply, firstOrderDiagonal_succ, gegenbauer_one_eq_chebyshev_U]
  push_cast
  field_simp

/-- Reconstruction respects subtraction on the closed interval. -/
theorem complexChebyshevSeries_firstOrderPreconditioner_sub
    (x y : lp (fun _ : ℕ ↦ ℂ) 2) (t : Icc (-1 : ℝ) 1) :
    complexChebyshevSeries (firstOrderPreconditioner (x - y)) (.ofFirstOrder (x-y) t) =
      complexChebyshevSeries (firstOrderPreconditioner x) (.ofFirstOrder x t) -
      complexChebyshevSeries (firstOrderPreconditioner y) (.ofFirstOrder y t) := by
  have hs (v : lp (fun _ : ℕ ↦ ℂ) 2) :
      Summable (fun n ↦ firstOrderPreconditioner v n * (T ℂ n).eval (t.val : ℂ)) :=
    summable_chebyshevSeries_of_absolute (summable_norm_firstOrderPreconditioner v).1 t
  rw [complexChebyshevSeries_eq_tsum (.ofFirstOrder (x-y) t) (hs (x-y)),
    complexChebyshevSeries_eq_tsum (.ofFirstOrder x t) (hs x),
    complexChebyshevSeries_eq_tsum (.ofFirstOrder y t) (hs y)]
  simp only [ComplexChebyshevSeriesPoint.ofFirstOrder_val, map_sub, lp.coeFn_sub,
    Pi.sub_apply, sub_mul, (hs x).tsum_sub (hs y)]

/-- Coefficient errors control uniform function errors. -/
theorem norm_firstOrder_reconstruction_sub_le
    (x y : lp (fun _ : ℕ ↦ ℂ) 2) (t : Icc (-1 : ℝ) 1) :
    ‖complexChebyshevSeries (firstOrderPreconditioner x) (.ofFirstOrder x t) -
      complexChebyshevSeries (firstOrderPreconditioner y) (.ofFirstOrder y t)‖ ≤
      ‖firstOrderBoundaryVector‖ * ‖x - y‖ := by
  rw [← complexChebyshevSeries_firstOrderPreconditioner_sub x y t]
  exact norm_complexChebyshevSeries_firstOrderPreconditioner_le (x - y) t

/-- Reconstruction carries coefficient convergence to uniform interval convergence. -/
theorem tendstoUniformlyOn_firstOrder_reconstruction
    {ι : Type*} {l : Filter ι} {v : ι → lp (fun _ : ℕ ↦ ℂ) 2}
    {x : lp (fun _ : ℕ ↦ ℂ) 2} (hv : Tendsto v l (𝓝 x)) :
    TendstoUniformly
      (fun n (t : Icc (-1 : ℝ) 1) ↦ complexChebyshevSeries (firstOrderPreconditioner (v n))
        (.ofFirstOrder (v n) t))
      (fun t ↦ complexChebyshevSeries (firstOrderPreconditioner x) (.ofFirstOrder x t)) l := by
  have hb : Tendsto (fun n ↦ ‖firstOrderBoundaryVector‖ * ‖v n - x‖) l (𝓝 0) := by
    simpa using (hv.sub (tendsto_const_nhds (x := x))).norm.const_mul ‖firstOrderBoundaryVector‖
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hb (gt_mem_nhds hε)] with n hn t
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_firstOrder_reconstruction_sub_le (v n) x t).trans_lt hn

/-- An actual solution for prescribed derivative coefficients and left endpoint.
The inverse exists by the nilpotent boundary correction, not by a hypothesis. -/
noncomputable def firstOrderDerivativeSolution (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2) :
    lp (fun _ : ℕ ↦ ℂ) 2 :=
  Ring.inverseAt (fun _ : Unit ↦ 1 + firstOrderBoundaryCorrection) ⟨(), isUnit_firstOrderDerivative⟩
    (lp.single 2 0 c + lp.coefficientShiftRight f)

/-- The explicit inverse solves all bordered coefficient equations. -/
theorem firstOrderDerivativeSolution_equation (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2) :
    (1 + firstOrderBoundaryCorrection) (firstOrderDerivativeSolution c f) =
      lp.single 2 0 c + lp.coefficientShiftRight f := by
  have h := Ring.mul_inverse_cancel (1 + firstOrderBoundaryCorrection) isUnit_firstOrderDerivative
  simpa only [firstOrderDerivativeSolution, Ring.inverseAt_eq_ringInverse,
    mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun L : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 ↦
    L (lp.single 2 0 c + lp.coefficientShiftRight f)) h

/-- The represented solution attains the prescribed boundary value. -/
theorem firstOrderDerivativeSolution_boundary (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2) :
    complexChebyshevSeries (firstOrderPreconditioner (firstOrderDerivativeSolution c f))
      (.ofFirstOrder (firstOrderDerivativeSolution c f) ⟨-1, by constructor <;> norm_num⟩) = c := by
  rw [complexChebyshevSeries_firstOrderPreconditioner_neg_one]
  have h := congrArg (fun x : lp (fun _ : ℕ ↦ ℂ) 2 ↦ x 0)
    (firstOrderDerivativeSolution_equation c f)
  simpa [add_apply, one_apply_eq_self,
    lp.single_apply, Pi.single_apply] using h

/-- The positive coordinates are precisely the given U derivative coefficients. -/
theorem firstOrderDerivativeSolution_succ (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2) (n : ℕ) :
    firstOrderDerivativeSolution c f (n + 1) = f n := by
  have h := congrArg (fun x : lp (fun _ : ℕ ↦ ℂ) 2 ↦ x (n + 1))
    (firstOrderDerivativeSolution_equation c f)
  simpa [add_apply, one_apply_eq_self,
    lp.single_apply, Pi.single_apply] using h

/-- The represented solution has the asserted derivative series, with convergence. -/
theorem firstOrderDerivativeSolution_deriv (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2)
    {C ρ : ℝ} (hρ : 1 < ρ)
    (hx : ∀ n, ‖firstOrderPreconditioner (firstOrderDerivativeSolution c f) n‖ ≤ C / ρ ^ n)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ f n * (Polynomial.Chebyshev.U ℂ n).eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ hx 1) z) := by
  simpa only [firstOrderDerivativeSolution_succ] using
    hasSum_derivative_firstOrderPreconditioner (firstOrderDerivativeSolution c f) hρ hx z

set_option maxHeartbeats 800000 in
/-- Genuine invertible finite solves converge uniformly on the closed interval. -/
theorem tendstoUniformlyOn_firstOrder_derivative_solution
    (c : ℂ) (f : lp (fun _ : ℕ ↦ ℂ) 2) :
    TendstoUniformly
      (fun n : Ring.InvertibleIndex (fun (n : ℕ) ↦ ContinuousLinearMap.liftedFiniteSection
          (lp.coefficientProjection n) firstOrderBoundaryCorrection) ↦
        fun t : Icc (-1 : ℝ) 1 ↦
        let v := Ring.inverseAt (fun (n : ℕ) ↦ ContinuousLinearMap.liftedFiniteSection
          (lp.coefficientProjection n) firstOrderBoundaryCorrection) n
          (lp.coefficientProjection n.val (lp.single 2 0 c + lp.coefficientShiftRight f))
        complexChebyshevSeries (firstOrderPreconditioner v) (.ofFirstOrder v t))
      (fun t ↦ complexChebyshevSeries (firstOrderPreconditioner (firstOrderDerivativeSolution c f))
        (.ofFirstOrder (firstOrderDerivativeSolution c f) t))
      (Ring.invertibleIndexFilter (fun (n : ℕ) ↦ ContinuousLinearMap.liftedFiniteSection
        (lp.coefficientProjection n) firstOrderBoundaryCorrection) atTop) := by
  have h := ContinuousLinearMap.tendsto_liftedFiniteSection_solution
    (lp.coefficientProjection (𝕜 := ℂ)) (lp.norm_coefficientProjection_le (𝕜 := ℂ))
    (lp.tendsto_coefficientProjection (𝕜 := ℂ)) firstOrderBoundaryCorrection
    isCompactOperator_firstOrderBoundaryCorrection isUnit_firstOrderDerivative
    (firstOrderDerivativeSolution c f)
  rw [firstOrderDerivativeSolution_equation] at h
  exact tendstoUniformlyOn_firstOrder_reconstruction h

end Polynomial.Chebyshev
