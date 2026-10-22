/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesMultiplication
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticCharacterization

/-! # Multiplication of absolutely convergent Chebyshev expansions
Collect both output modes of T_m T_n=(T_(m+n)+T_|m-n|)/2. Keeping both
contributions handles the constant row without exceptions or double counting.
Reference: ATAP, Chapter 3; Olver--Townsend (2013), Section 2.2.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Complex Set

/-- Two coefficient sequences with convergence in the chosen difference fibre.
The addition fibre is finite, so requires no assumption (DLMF 18.18.21). -/
structure ChebyshevProductInput (k : ℕ) where
  left : ℕ → ℂ
  right : ℕ → ℂ
  difference_summable : Summable (fun p : {p : ℕ × ℕ // ((p.1 : ℤ) - p.2).natAbs = k} ↦
    left p.val.1 * right p.val.2)

/-- Only finitely many natural pairs have a prescribed sum. -/
theorem finite_add_fibre (k : ℕ) : Finite {p : ℕ × ℕ // p.1 + p.2 = k} := by
  apply Finite.of_injective
    (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} ↦ (⟨p.val.1, by have := p.property; omega⟩ : Fin (k+1)))
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val h
  · have h1 := congrArg Fin.val h
    have hp := p.property
    have hq := q.property
    dsimp at h1
    omega

/-- The finite addition fibre always supplies an admissible regrouping input. -/
noncomputable def ChebyshevProductInput.addInput {k : ℕ} (d : ChebyshevProductInput k) :
    RegroupCoefficientInput (fun p : ℕ × ℕ ↦ p.1 + p.2) k := by
  letI := finite_add_fibre k
  letI := Fintype.ofFinite {p : ℕ × ℕ // p.1 + p.2 = k}
  exact ⟨fun p ↦ d.left p.1 * d.right p.2, (hasSum_fintype _).summable⟩

/-- Absolute summability of both sequences supplies every product coefficient input. -/
def ChebyshevProductInput.ofSummableNorm {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) (k : ℕ) :
    ChebyshevProductInput k :=
  ⟨a, b, (ha.mul_norm hb).of_norm.subtype _⟩

/-- The product coefficient in the full-constant convention, on its classical domain
(DLMF 18.18.21; Olver--Townsend, Section 2.2). -/
noncomputable def chebyshevProductCoefficients {k : ℕ} (d : ChebyshevProductInput k) : ℂ :=
  (Polynomial.regroupCoefficients d.addInput +
    Polynomial.regroupCoefficients
      (e := fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2).natAbs)
      ⟨fun p ↦ d.left p.1 * d.right p.2, d.difference_summable⟩) / 2

/-- Both classical fibres contribute to the full-constant product coefficient. -/
theorem chebyshevProductCoefficients_eq {k : ℕ} (d : ChebyshevProductInput k) :
    chebyshevProductCoefficients d =
      ((∑' p : {p : ℕ × ℕ // p.1 + p.2 = k}, d.left p.val.1 * d.right p.val.2) +
        ∑' p : {p : ℕ × ℕ // ((p.1 : ℤ) - p.2).natAbs = k},
          d.left p.val.1 * d.right p.val.2) / 2 := rfl

/-- Products preserve absolute coefficient summability. -/
theorem summable_norm_chebyshevProductCoefficients {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) :
    Summable (fun k ↦ ‖chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k)‖) := by
  exact (((Polynomial.summable_norm_regroupCoefficients (ha.mul_norm hb) _).of_norm.add
    (Polynomial.summable_norm_regroupCoefficients (ha.mul_norm hb) _).of_norm).div_const 2).norm

/-- The absolute coefficient norm is submultiplicative. -/
theorem tsum_norm_chebyshevProductCoefficients_le {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) :
    ∑' k, ‖chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k)‖ ≤
      (∑' n, ‖a n‖) * ∑' n, ‖b n‖ := by
  let c (p : ℕ × ℕ) := a p.1 * b p.2
  let e (p : ℕ × ℕ) := p.1 + p.2
  let d (p : ℕ × ℕ) := ((p.1 : ℤ) - p.2).natAbs
  have hc : Summable (fun p ↦ ‖c p‖) := ha.mul_norm hb
  have he := Polynomial.summable_norm_regroupCoefficients hc e
  have hd := Polynomial.summable_norm_regroupCoefficients hc d
  have ht := (summable_norm_chebyshevProductCoefficients ha hb).tsum_le_tsum
    (g := fun k ↦ (‖Polynomial.regroupCoefficients (RegroupCoefficientInput.ofSummableNorm hc e k)‖ + ‖Polynomial.regroupCoefficients (RegroupCoefficientInput.ofSummableNorm hc d k)‖) / 2)
    (fun k ↦ by
      rw [chebyshevProductCoefficients, norm_div, norm_ofNat]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num))
    ((he.add hd).div_const 2)
  rw [tsum_div_const, he.tsum_add hd] at ht
  have h1 := Polynomial.tsum_norm_regroupCoefficients_le hc e
  have h2 := Polynomial.tsum_norm_regroupCoefficients_le hc d
  have hm : (∑' p, ‖c p‖) = (∑' n, ‖a n‖) * ∑' n, ‖b n‖ := by
    simpa only [c, norm_mul] using (tsum_mul_tsum_of_summable_norm ha.norm hb.norm).symm
  rw [hm] at h1 h2
  linarith

private theorem product_mode (m n : ℕ) (z : ℂ) :
    (T ℂ m).eval z * (T ℂ n).eval z =
      ((T ℂ (m + n : ℕ)).eval z + (T ℂ ((m : ℤ) - n).natAbs).eval z) / 2 := by
  have h := congrArg (fun p : ℂ[X] ↦ p.eval z) (T_mul_T ℂ m n)
  simp only [eval_mul, eval_ofNat, eval_add] at h
  rw [T_natAbs]
  push_cast
  linear_combination h / 2

/-- The collected product coefficients represent the pointwise product on the
whole closed interval. All rearrangements are absolutely convergent. -/
theorem hasSum_chebyshevProductCoefficients {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (x : Icc (-1 : ℝ) 1) :
    HasSum (fun k ↦ chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k) * (T ℂ k).eval (x : ℂ))
      (complexChebyshevSeries a (.ofAbsolute ha x) * complexChebyshevSeries b (.ofAbsolute hb x)) := by
  let c (p : ℕ × ℕ) := a p.1 * b p.2
  let e (p : ℕ × ℕ) := p.1 + p.2
  let d (p : ℕ × ℕ) := ((p.1 : ℤ) - p.2).natAbs
  have hc : Summable (fun p ↦ ‖c p‖) := ha.mul_norm hb
  have hs := Polynomial.hasSum_regrouped_series hc e (fun k ↦ norm_eval_T_complex_le_one k x.property)
  have hd := Polynomial.hasSum_regrouped_series hc d (fun k ↦ norm_eval_T_complex_le_one k x.property)
  have heval (v : ℕ → ℂ) (hv : Summable (fun n ↦ ‖v n‖)) :
      Summable (fun n ↦ ‖v n * (T ℂ n).eval (x : ℂ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hv
    intro n
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one n x.property)
  have htotal : (∑' p, c p * (T ℂ (e p)).eval (x : ℂ)) +
      (∑' p, c p * (T ℂ (d p)).eval (x : ℂ)) =
      2 * (complexChebyshevSeries a (.ofAbsolute ha x) * complexChebyshevSeries b (.ofAbsolute hb x)) := by
    have hsum (j : ℕ × ℕ → ℕ) : Summable (fun p ↦ c p * (T ℂ (j p)).eval (x : ℂ)) := by
      apply Summable.of_norm
      apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hc
      intro p
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one _ x.property)
    rw [← (hsum e).tsum_add (hsum d)]
    rw [complexChebyshevSeries_eq_tsum (.ofAbsolute ha x) (summable_chebyshevSeries_of_absolute ha x),
      complexChebyshevSeries_eq_tsum (.ofAbsolute hb x) (summable_chebyshevSeries_of_absolute hb x)]
    simp only [ComplexChebyshevSeriesPoint.ofAbsolute_val]
    rw [tsum_mul_tsum_of_summable_norm (heval a ha) (heval b hb), ← tsum_mul_left]
    apply tsum_congr
    intro p
    dsimp [c, e, d]
    have hm := product_mode p.1 p.2 (x : ℂ)
    simp only [Nat.cast_add] at hm ⊢
    linear_combination -2 * a p.1 * b p.2 * hm
  have h := (hs.add hd).div_const 2
  rw [htotal] at h
  convert h using 1
  · ext k
    dsimp [chebyshevProductCoefficients, ChebyshevProductInput.ofSummableNorm,
      ChebyshevProductInput.addInput, Polynomial.regroupCoefficients,
      RegroupCoefficientInput.ofSummableNorm, RegroupCoefficientInput.ofSummable, c, e, d]
    ring
  · ring

/-- The product expansion is an equality of the represented functions. -/
theorem complexChebyshevSeries_product {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (x : Icc (-1 : ℝ) 1) :
    complexChebyshevSeries ((fun k ↦ chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k)))
      (.ofAbsolute (summable_norm_chebyshevProductCoefficients ha hb) x) =
      complexChebyshevSeries a (.ofAbsolute ha x) * complexChebyshevSeries b (.ofAbsolute hb x) := by
  rw [complexChebyshevSeries_eq_tsum
    (.ofAbsolute (summable_norm_chebyshevProductCoefficients ha hb) x)
    (summable_chebyshevSeries_of_absolute (summable_norm_chebyshevProductCoefficients ha hb) x)]
  exact (hasSum_chebyshevProductCoefficients ha hb x).tsum_eq

/-- Integral coefficients of an interval representative of the product. -/
theorem complexCoefficient_product_series {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (k : ℕ) (f : ComplexCoefficientInput k)
    (he : ∀ x : Icc (-1 : ℝ) 1, f.val x.val =
      complexChebyshevSeries a (.ofAbsolute ha x) * complexChebyshevSeries b (.ofAbsolute hb x)) :
    complexCoefficient f = chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k) := by
  apply complexCoefficient_complexChebyshevSeries (summable_norm_chebyshevProductCoefficients ha hb) k f
  intro x
  exact (he x).trans (complexChebyshevSeries_product ha hb x).symm

/-- Truncating the product coefficients has error at most their absolute tail. -/
theorem norm_product_series_sub_sum_le {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (x : Icc (-1 : ℝ) 1) (N : ℕ) :
    ‖complexChebyshevSeries a (.ofAbsolute ha x) * complexChebyshevSeries b (.ofAbsolute hb x) -
      ∑ k ∈ Finset.range N, chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb k) * (T ℂ k).eval (x : ℂ)‖ ≤
      ∑' k, ‖chebyshevProductCoefficients (ChebyshevProductInput.ofSummableNorm ha hb (k + N))‖ := by
  apply norm_series_sub_sum_le_tail (hasSum_chebyshevProductCoefficients ha hb x)
    (summable_norm_chebyshevProductCoefficients ha hb)
  intro k
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one k x.property)



end Polynomial.Chebyshev
