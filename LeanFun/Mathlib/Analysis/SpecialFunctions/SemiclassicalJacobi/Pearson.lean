/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Weight
public import Mathlib.Algebra.Polynomial.Derivative
public import LeanFun.Mathlib.MeasureTheory.Integral.OpenIntervalFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Ring

/-!
# The semiclassical Jacobi Pearson functional identity

The cubic/quadratic Pearson pair gives a weak derivative identity for polynomial
test functions. Endpoint terms vanish throughout the admissible range, including
integrable endpoint singularities of the original weight.

Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

@[expose] public section
open Set Real MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The cubic multiplier in the semiclassical Jacobi Pearson equation. -/
noncomputable def semiclassicalJacobiSigma (t : ℝ) : ℝ[X] := X * (1 - X) * (C t - X)

/-- The quadratic coefficient in the semiclassical Jacobi Pearson equation. -/
noncomputable def semiclassicalJacobiTau (t α β γ : ℝ) : ℝ[X] :=
  C (α + 1) * (1 - X) * (C t - X) - C (β + 1) * X * (C t - X) -
    C (γ + 1) * X * (1 - X)

/-- The Pearson identity tested against any polynomial, with zero endpoint terms. -/
theorem integral_semiclassicalJacobi_pearson {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    ∫ x, (semiclassicalJacobiSigma t * p.derivative + semiclassicalJacobiTau t α β γ * p).eval x
      ∂semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ = 0 := by
  let q := semiclassicalJacobiSigma t * p.derivative + semiclassicalJacobiTau t α β γ * p
  obtain ⟨F, hF, h0, h1⟩ := exists_continuous_semiclassicalJacobiWeight_add_one
    (γ := γ) ⟨t, ht⟩ hα hβ
  let P : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun x ↦ F x * p.eval (x : ℝ),
    F.continuous.mul (p.continuous.comp continuous_subtype_val)⟩
  have hq := integrable_semiclassicalJacobiMeasure (γ := γ) ht hα hβ q.continuous.continuousOn
  have hg := (integrable_semiclassicalJacobiMeasure_iff ⟨t, ht⟩ α β γ _).mp hq
  have hd (x : Ioo (0 : ℝ) 1) :
      HasDerivAtOnOpen ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
        (fun y ↦ P ⟨y, ⟨y.property.1.le, y.property.2.le⟩⟩)
        ((semiclassicalJacobiWeight ⟨t, ht⟩ α β γ x : ℝ) * q.eval (x : ℝ)) x := by
    have he : (fun y : Ioo (0 : ℝ) 1 ↦ P ⟨y, ⟨y.property.1.le, y.property.2.le⟩⟩) =
        fun y ↦ (semiclassicalJacobiWeight ⟨t, ht⟩ (α+1) (β+1) (γ+1) y : ℝ) * p.eval (y : ℝ) := by
      funext y
      exact congrArg (fun r ↦ r * p.eval (y : ℝ)) (hF y)
    erw [he]
    convert ((hasDerivAt_semiclassicalJacobiWeight_add_one ⟨t, ht⟩ α β γ x).mul
      ⟨_, fun _ ↦ rfl, p.hasDerivAt (x : ℝ)⟩) using 1
    rw [semiclassicalJacobiWeight_add_one]
    simp only [q, semiclassicalJacobiSigma, semiclassicalJacobiTau, eval_add, eval_mul,
      eval_sub, eval_one, eval_X, eval_C]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAtOnOpen
    (show (0 : ℝ) < 1 by norm_num) P ⟨_, hg⟩ hd
  change (∫ x : Ioo (0 : ℝ) 1,
    (semiclassicalJacobiWeight ⟨t, ht⟩ α β γ x : ℝ) * q.eval (x : ℝ)) =
    F ⟨1, by norm_num⟩ * p.eval 1 - F ⟨0, by norm_num⟩ * p.eval 0 at hi
  rw [h0, h1, zero_mul, zero_mul, sub_self] at hi
  exact (integral_semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ ⟨_, hq⟩).trans hi

end Polynomial
