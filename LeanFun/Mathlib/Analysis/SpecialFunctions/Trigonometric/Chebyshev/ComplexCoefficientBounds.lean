/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexCoefficients
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.Comrade
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-! # Complex coefficient bounds and polynomial support
These extend the full-constant coefficient convention to complex polynomial
approximation. Reference: ATAP, Chapters 3 and 8.
-/

public section
namespace Polynomial.Chebyshev
open Real MeasureTheory Set

private theorem cosine_integrable {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) :
    IntervalIntegrable (fun θ ↦ f (cos θ) * (cos (n * θ) : ℂ)) volume 0 π := by
  apply ContinuousOn.intervalIntegrable
  exact (hf.comp continuous_cos.continuousOn
    (fun θ _ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩)).mul (by fun_prop)

/-- The sharp uniform complex coefficient bound, including index zero (ATAP 8.1). -/
theorem norm_complexCoefficient_le {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1))
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ Icc (-1) 1, ‖f x‖ ≤ M) :
    ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖ ≤ (if n = 0 then 1 else 2) * M := by
  have hi : ‖∫ θ in 0..π, f (cos θ) * (cos (n * θ) : ℂ)‖ ≤ M * π := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := π) (C := M)
      (f := fun θ ↦ f (cos θ) * (cos (n * θ) : ℂ)) (by
        intro θ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ M * 1 := mul_le_mul (hb _ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
            (abs_cos_le_one _) (abs_nonneg _) hM
          _ = M := mul_one _)
    simpa only [sub_zero, abs_of_pos pi_pos] using h
  have hn : 0 ≤ (if n = 0 then 1 else 2 : ℝ) / π := by positivity
  rw [complexCoefficient_eq_integral_cos hf, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    _ ≤ ((if n = 0 then 1 else 2) / π) * (M * π) := mul_le_mul_of_nonneg_left hi hn
    _ = _ := by field_simp

/-- Subtraction commutes with complex Chebyshev coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_sub {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hg : ContinuousOn g (Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x ↦ f x - g x) (by fun_prop) n)) =
      (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)) - (complexCoefficient (ComplexCoefficientInput.ofContinuousOn g hg n)) := by
  rw [complexCoefficient_eq_integral_cos (f := fun x ↦ f x - g x) (hf.sub hg), complexCoefficient_eq_integral_cos hf,
    complexCoefficient_eq_integral_cos hg]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (cosine_integrable hf n) (cosine_integrable hg n), mul_sub]

/-- Complex scalars commute with coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_const_mul (c : ℂ) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x ↦ c * f x) (by fun_prop) n)) = c * (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)) := by
  rw [complexCoefficient_eq_integral_cos (f := fun x ↦ c * f x) (continuousOn_const.mul hf),
    complexCoefficient_eq_integral_cos hf]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Finite sums commute with coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Icc (-1) 1)) (n : ℕ) :
    complexCoefficient (ComplexCoefficientInput.ofContinuousOn
      (fun x ↦ ∑ i ∈ s, f i x) (continuousOn_finsetSum _ hf) n) =
      ∑ i : ↥s, complexCoefficient
        (ComplexCoefficientInput.ofContinuousOn (f i) (hf i i.property) n) := by
  rw [complexCoefficient_eq_integral_cos]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun i hi ↦ cosine_integrable (hf i hi) n),
    Finset.mul_sum, ← s.sum_attach]
  apply Finset.sum_congr rfl
  intro i hi
  exact (complexCoefficient_eq_integral_cos (hf i i.property) n).symm

/-- A Chebyshev polynomial has exactly its matching complex coefficient. -/
@[simp] theorem complexCoefficient_eval_T (m n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x : ℝ ↦ (T ℂ m).eval (x : ℂ)) (by fun_prop) n)) = if m = n then 1 else 0 := by
  simp_rw [← complex_ofReal_eval_T]
  have h := (complexCoefficient_ofReal (CoefficientInput.ofContinuousOn
    (fun x ↦ (T ℝ m).eval x) (by fun_prop) n)).trans
      (congrArg (fun r : ℝ ↦ (r : ℂ)) (coefficient_eval_T m n))
  split_ifs with hmn <;> simpa [complexCoefficient, ComplexCoefficientInput.ofContinuousOn, ComplexCoefficientInput.ofL1, ComplexCoefficientInput.ofReal, CoefficientInput.ofContinuousOn, CoefficientInput.ofL1, hmn] using h

/-- A complex polynomial has no Chebyshev coefficient above its degree (ATAP 3). -/
theorem complexCoefficient_polynomial_eq_zero {p : ℂ[X]} {n : ℕ} (hp : p.degree < n) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x : ℝ ↦ p.eval (x : ℂ)) (by fun_prop) n)) = 0 := by
  classical
  let P := chebyshevTsequence ℂ
  let c := (P.basis P.isUnit_leadingCoeff).repr p
  have he : p = ∑ i : Fin n, c i • T ℂ (i : ℕ) := (P.sum_fin_repr hp).symm
  rw [he]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  rw [complexCoefficient_sum _ (fun i _ ↦ by fun_prop)]
  apply Finset.sum_eq_zero
  intro i _
  rw [complexCoefficient_const_mul _ (by fun_prop), complexCoefficient_eval_T,
    ite_eq_right (ne_of_lt i.val.isLt), mul_zero]

end Polynomial.Chebyshev
