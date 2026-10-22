/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.CoefficientInput

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev coefficients

Weighted integral coefficients, with the full constant term convention:
`f = a₀ + ∑ n ≥ 1, aₙ Tₙ`. The coefficient of `T₀` is normalised by `1 / π`,
and all positive-index coefficients by `2 / π`.

## References

* Trefethen, *Approximation Theory and Approximation Practice*, Chapters 3 and 8.
* DLMF Table 18.3.1: https://dlmf.nist.gov/18.3
-/

public section

namespace Polynomial.Chebyshev

open Real MeasureTheory

/-- Chebyshev coefficient in the full constant term convention (ATAP, Chapters 3 and 8).
The input carries integrability at the selected index. -/
@[expose] noncomputable def coefficient {n : ℕ} (f : CoefficientInput n) : ℝ :=
  (if n = 0 then 1 else 2) / π * ∫ x, f.val x * (T ℝ n).eval x ∂classicalMeasureT


/-- The classical coefficient formula on its exact fixed-index domain (ATAP Ch. 3). -/
theorem coefficient_apply {n : ℕ} (f : CoefficientInput n) :
    coefficient f = (if n = 0 then 1 else 2) / π *
      ∫ x, f.val x * (T ℝ n).eval x ∂classicalMeasureT := rfl

/-- Internal bridge to the ambient measure representation. -/
theorem coefficient_eq_integral {n : ℕ} (f : CoefficientInput n) :
    coefficient f = (if n = 0 then 1 else 2) / π *
      ∫ x, f.val x * (T ℝ n).eval x ∂measureT := by
  simp only [coefficient, classicalMeasureT_eq]

/-- The constant coefficient uses 1 / π (ATAP Ch. 3). -/
@[simp] theorem coefficient_zero (f : CoefficientInput 0) :
    coefficient f = (∫ x, f.val x ∂measureT) / π := by
  simp [coefficient_eq_integral, div_eq_mul_inv, mul_comm]

/-- The positive-index coefficient formula (ATAP Ch. 3). -/
theorem coefficient_of_ne_zero {n : ℕ} (f : CoefficientInput n) (hn : n ≠ 0) :
    coefficient f = 2 / π * ∫ x, f.val x * (T ℝ n).eval x ∂measureT := by
  simp [coefficient_eq_integral, hn]

/-- Cosine representation for an integrable coefficient integrand (ATAP Ch. 3). -/
theorem coefficient_eq_integral_cos {n : ℕ} (f : CoefficientInput n) :
    coefficient f = (if n = 0 then 1 else 2) / π *
      ∫ θ in 0..π, f.val (cos θ) * cos (n * θ) := by
  simp only [coefficient_eq_integral, integral_measureT_eq_integral_cos,
    T_real_cos, Int.cast_natCast]

/-- The cosine integrand is integrable on the same full fixed-index domain. -/
theorem coefficient_integrable_cos {n : ℕ} (f : CoefficientInput n) :
    IntervalIntegrable (fun θ ↦ f.val (cos θ) * cos (n * θ)) volume 0 π := by
  simpa only [T_real_cos, Int.cast_natCast] using
    intervalIntegrable_classicalMeasureT_cos ⟨_, f.property⟩

/-- Coefficients respect almost-everywhere equality (ATAP Ch. 3). -/
theorem coefficient_congr_ae {n : ℕ} {f g : CoefficientInput n}
    (h : f.val =ᵐ[classicalMeasureT] g.val) : coefficient f = coefficient g := by
  simp only [coefficient]
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Additivity on the full integrable-product domain (ATAP Ch. 3). -/
theorem coefficient_add {n : ℕ} (f g : CoefficientInput n) :
    coefficient (f.add g) = coefficient f + coefficient g := by
  simp only [coefficient, CoefficientInput.add, add_mul,
    integral_add f.property g.property, mul_add]

/-- Continuous functions satisfy coefficient additivity (ATAP Ch. 3). -/
theorem coefficient_add_of_continuousOn {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (hg : ContinuousOn g (Set.Icc (-1) 1))
    (n : ℕ) :
    coefficient (CoefficientInput.ofContinuousOn (fun x ↦ f x + g x) (hf.add hg) n) =
      coefficient (CoefficientInput.ofContinuousOn f hf n) +
      coefficient (CoefficientInput.ofContinuousOn g hg n) :=
  by
    simpa [CoefficientInput.ofContinuousOn, CoefficientInput.ofL1, CoefficientInput.add] using
      coefficient_add (CoefficientInput.ofContinuousOn f hf n)
        (CoefficientInput.ofContinuousOn g hg n)

/-- Scalar multiplication preserves coefficients (ATAP Ch. 3). -/
theorem coefficient_const_mul {n : ℕ} (c : ℝ) (f : CoefficientInput n) :
    coefficient (f.constMul c) = c * coefficient f := by
  simp only [coefficient, CoefficientInput.constMul, mul_assoc, integral_const_mul]
  ring

/-- The zero function has zero coefficients (ATAP Ch. 3). -/
@[simp] theorem coefficient_zero_fun (n : ℕ) :
    coefficient (CoefficientInput.ofContinuousOn (fun _ ↦ 0) (by fun_prop) n) = 0 := by
  simp [coefficient, CoefficientInput.ofContinuousOn, CoefficientInput.ofL1]

/-- Coefficients commute with finite sums of integrable products (ATAP Ch. 3). -/
theorem coefficient_sum {ι : Type*} (s : Finset ι) {n : ℕ}
    (f : ↥s → CoefficientInput n) :
    coefficient (n := n) ⟨(fun x ↦ ∑ i : ↥s, (f i).val x), by
      simpa only [Finset.sum_mul] using
        integrable_finsetSum Finset.univ (fun i _ ↦ (f i).property)⟩ =
      ∑ i : ↥s, coefficient (f i) := by
  simp only [coefficient, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (f i).property), Finset.mul_sum]

/-- A basis polynomial's coefficients form the Kronecker delta (DLMF 18.3). -/
@[simp] theorem coefficient_eval_T (m n : ℕ) :
    coefficient (CoefficientInput.ofContinuousOn (fun x ↦ (T ℝ m).eval x)
      (by fun_prop) n) = if m = n then 1 else 0 := by
  rw [coefficient]
  change (if n = 0 then 1 else 2) / π *
    (∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂classicalMeasureT) = _
  rw [(classicalMeasureT_orthogonality m n).2]
  by_cases h : m = n
  · subst m; simp only [ite_true]; split_ifs <;> field_simp
  · simp [h]

/-- Coefficients recover finite Chebyshev expansions (ATAP Ch. 3). -/
theorem coefficient_sum_eval_T (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    coefficient (CoefficientInput.ofContinuousOn
      (fun x ↦ ∑ k ∈ s, c k * (T ℝ k).eval x) (by fun_prop) n) =
      if n ∈ s then c n else 0 := by
  simp only [coefficient, CoefficientInput.ofContinuousOn_val, Finset.sum_mul]
  rw [integral_finsetSum s (fun k hk ↦ integrable_classicalMeasureT (by fun_prop)),
    Finset.mul_sum]
  simp only [mul_assoc, integral_const_mul]
  have hc (k : ℕ) : (if n = 0 then 1 else 2) / π *
      (c k * ∫ x, (T ℝ k).eval x * (T ℝ n).eval x ∂classicalMeasureT) =
        c k * (if k = n then 1 else 0) := by
    rw [← coefficient_eval_T k n]
    simp only [coefficient, CoefficientInput.ofContinuousOn, CoefficientInput.ofL1]
    ring
  simp_rw [hc]
  simp

/-- Constant functions have only the constant coefficient (ATAP Ch. 3). -/
@[simp] theorem coefficient_const (c : ℝ) (n : ℕ) :
    coefficient (CoefficientInput.ofContinuousOn (fun _ ↦ c) (by fun_prop) n) =
      if n = 0 then c else 0 := by
  have h := coefficient_const_mul c
    (CoefficientInput.ofContinuousOn (fun x ↦ (T ℝ (0 : ℕ)).eval x) (by fun_prop) n)
  rw [coefficient_eval_T] at h
  simpa [CoefficientInput.constMul, CoefficientInput.ofContinuousOn,
    CoefficientInput.ofL1, mul_ite, eq_comm] using h

/-- Only values on the approximation interval affect coefficients (ATAP Ch. 3). -/
theorem coefficient_congr {n : ℕ} {f g : CoefficientInput n}
    (h : Set.EqOn f.val g.val (Set.Icc (-1) 1)) : coefficient f = coefficient g := by
  rw [coefficient_eq_integral_cos, coefficient_eq_integral_cos]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [h ⟨neg_one_le_cos θ, cos_le_one θ⟩]

/-- The sharp uniform bound, on the classical fixed-index domain (ATAP Ch. 3). -/
theorem abs_coefficient_le {n : ℕ} (f : CoefficientInput n) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc (-1) 1, |f.val x| ≤ M) :
    |coefficient f| ≤ (if n = 0 then 1 else 2) * M := by
  have hi : |∫ θ in 0..π, f.val (cos θ) * cos (n * θ)| ≤ M * π := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := π) (C := M) (f := fun θ ↦ f.val (cos θ) * cos (n * θ)) (by
        intro θ hθ
        rw [Real.norm_eq_abs, abs_mul]
        calc
          _ ≤ M * 1 := mul_le_mul (hf _ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
            (abs_cos_le_one _) (abs_nonneg _) hM
          _ = M := mul_one _)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos pi_pos] using h
  have hn : 0 ≤ (if n = 0 then 1 else 2 : ℝ) / π := by positivity
  rw [coefficient_eq_integral_cos, abs_mul, abs_of_nonneg hn]
  calc
    _ ≤ ((if n = 0 then 1 else 2) / π) * (M * π) := mul_le_mul_of_nonneg_left hi hn
    _ = _ := by field_simp

end Polynomial.Chebyshev
