/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesDifferentialOperator
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.IteratedSeriesCalculus
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.UltrasphericalDifferentialOperator

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.MultiplicationEntries

/-! # Analytic consistency of ultraspherical differential operators
The finite matrices act on infinite coefficient sequences by finite banded rows.
Weighted reconstruction represents the analytic residual, and Cauchy estimates
control truncation. Reference: Olver--Townsend (2013), Section 3.
-/

@[expose] public noncomputable section
namespace Polynomial
open Complex

theorem exists_isBanded_chebyshev_mul (p : ℝ[X]) :
    ∃ d, (chebyshevBasis.toMatrix (fun j ↦ p * chebyshevBasis j)).IsBanded d d := by
  classical
  let d := (chebyshevBasis.repr p).support.sup id
  refine ⟨d, ?_⟩
  intro i j hij
  change chebyshevBasis.repr (p * chebyshevBasis j) i = 0
  have hp : ∑ k ∈ (chebyshevBasis.repr p).support,
      (chebyshevBasis.repr p k) • chebyshevBasis k = p := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      chebyshevBasis.linearCombination_repr p
  rw [← hp, Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hk' : k ≤ d := Finset.le_sup (f := id) hk
  have hdiff : ((k : ℤ) - j).natAbs = if j ≤ k then k - j else j - k := by
    split_ifs with h
    · exact Int.natAbs_natCast_sub_natCast_of_ge h
    · exact Int.natAbs_natCast_sub_natCast_of_le (by omega)
  have h1 : i ≠ k + j := by rcases hij with h | h <;> omega
  have h2 : i ≠ ((k : ℤ) - j).natAbs := by
    rw [hdiff]
    split_ifs <;> rcases hij with h | h <;> omega
  have he := two_mul_chebyshevBasis_repr_mul k j i
  simp only [ite_eq_right h1, ite_eq_right h2, add_zero] at he
  have hz : chebyshevBasis.repr (chebyshevBasis k * chebyshevBasis j) i = 0 := by linarith
  rw [hz, mul_zero]

theorem exists_isBanded_ultraspherical_differentialOperator (A : ℕ → ℝ[X]) (m : ℕ) :
    ∃ l u, ((ultrasphericalBasis m).toMatrix
      (fun j ↦ differentialOperator A m (chebyshevBasis j))).IsBanded l u := by
  classical
  cases m with
  | zero =>
    obtain ⟨d, hd⟩ := exists_isBanded_chebyshev_mul (A 0)
    refine ⟨d, d, ?_⟩
    simpa only [ultrasphericalBasis_zero, differentialOperator_apply, Nat.zero_add, Finset.sum_range_one,
      Function.iterate_zero, id_eq] using hd
  | succ m =>
    let d := (Finset.range (m + 1 + 1)).sup (fun k ↦ (A k).natDegree)
    exact ⟨d, d + 2 * (m + 1), ultraspherical_differentialOperator_isBanded_of_degree_le A
      (by omega) (fun k hk ↦ Finset.le_sup (f := fun k ↦ (A k).natDegree)
        (Finset.mem_range.mpr (by omega)))⟩

/-- Every polynomial differential operator has finite ultraspherical rows,
including the order-zero multiplication operator. -/
def ultrasphericalDifferentialSeriesInput (A : ℕ → ℝ[X]) (m : ℕ)
    (a : ℕ → ℂ) (i : ℕ) :
    chebyshevBasis.SeriesCoefficientInput (ultrasphericalBasis m)
      (differentialOperator A m) ofRealHom i := ⟨a, by
  obtain ⟨l, u, h⟩ := exists_isBanded_ultraspherical_differentialOperator A m
  exact (Module.Basis.SeriesCoefficientInput.ofBanded _ _ _ _ a h i).property⟩

@[simp] theorem ultrasphericalDifferentialSeriesInput_val (A : ℕ → ℝ[X]) (m : ℕ)
    (a : ℕ → ℂ) (i : ℕ) :
    (ultrasphericalDifferentialSeriesInput A m a i).val = a := rfl

end Polynomial

public section
namespace Polynomial
open Complex Set

/-- Infinite residual assembly uses the proven finite row window. -/
theorem ultraspherical_series_differentialOperator_eq_sum
    (A : ℕ → ℝ[X]) {m d : ℕ} (hm : 1 ≤ m)
    (hd : ∀ k ≤ m, (A k).natDegree ≤ d) (a : ℕ → ℂ) (i : ℕ) :
    chebyshevBasis.seriesCoefficientMap (ultrasphericalBasis m)
      (differentialOperator A m) ofRealHom (ultrasphericalDifferentialSeriesInput A m a i) =
      ∑ j ∈ Finset.range (i + (d + 2 * m) + 1),
        a j * ((ultrasphericalBasis m).repr (differentialOperator A m (chebyshevBasis j)) i : ℂ) := by
  have he : ultrasphericalDifferentialSeriesInput A m a i =
      Module.Basis.SeriesCoefficientInput.ofBanded _ _ _ _ a
        (ultraspherical_differentialOperator_isBanded_of_degree_le A hm hd) i :=
    Subtype.ext rfl
  rw [he]
  exact chebyshevBasis.seriesCoefficientMap_eq_sum_of_isBanded (ultrasphericalBasis m)
    (differentialOperator A m) ofRealHom a
    (ultraspherical_differentialOperator_isBanded_of_degree_le A hm hd) i

/-- The normally convergent expansion's ultraspherical residual represents its
actual differential action, also for order-zero multiplication. -/
theorem hasSum_ultraspherical_differentialOperator_series
    {a : ℕ → ℂ} {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (Chebyshev.T ℂ n).eval z‖ ≤ u n)
    (A : ℕ → ℝ[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (Chebyshev.T ℂ n).eval z.val) (f.val z))
    (z : U) (w : ℕ → ℝ)
    (hw : ∀ i, ‖(ultrasphericalBasis m i).eval₂ ofRealHom z.val‖ ≤ w i)
    (ha : Summable (fun j ↦ ‖a j‖ *
      ∑ i ∈ ((ultrasphericalBasis m).repr (differentialOperator A m (chebyshevBasis j))).support,
        ‖(((ultrasphericalBasis m).repr (differentialOperator A m (chebyshevBasis j))) i : ℂ)‖ * w i)) :
    HasSum (fun i ↦ chebyshevBasis.seriesCoefficientMap (ultrasphericalBasis m)
      (differentialOperator A m) ofRealHom (ultrasphericalDifferentialSeriesInput A m a i) *
      (ultrasphericalBasis m i).eval₂ ofRealHom z.val)
      (differentialOperatorOnFunctions (fun k ↦ (A k).map ofRealHom) m f.val (.ofIterated f z)) := by
  have he (n : ℕ) (v : ℂ) : (chebyshevBasis n).eval₂ ofRealHom v =
      (Chebyshev.T ℂ n).eval v := by
    rw [chebyshevBasis_apply, eval₂_eq_eval_map, Chebyshev.map_T]
  exact hasSum_seriesCoefficientMap_differentialOperator_eval₂_of_rows chebyshevBasis
    (ultrasphericalBasis m) ofRealHom hu (by simpa only [he] using hb) A m f
    (by simpa only [he] using hf) z
    (chebyshevBasis.summable_norm_seriesCoefficientMap_terms (ultrasphericalBasis m)
      (differentialOperator A m) ofRealHom a z.val w hw ha)
    (ultrasphericalDifferentialSeriesInput A m a) (fun _ ↦ rfl)

namespace Chebyshev

/-- Boundary errors involve certified derivative values at exactly the used points. -/
theorem norm_boundary_complexChebyshevSeries_sub_sum_le
    {a : ℕ → ℂ} {C ρ r : ℝ} (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ)
    (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℕ) (z : ι → ℂ) (δ : ι → ℝ)
    (hz : ∀ i ∈ s, z i ∈ bernsteinEllipse ⟨r, hr⟩) (hδ : ∀ i ∈ s, 0 < δ i)
    (hball : ∀ i ∈ s, Metric.sphere (z i) (δ i) ⊆ bernsteinEllipse ⟨r, hr⟩) (N : ℕ) :
    ‖(∑ i : s, c i.val * iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha (k i.val))
        ⟨z i.val, (closure_bernsteinEllipse_subset hr hrρ) (subset_closure (hz i.val i.property))⟩) -
      ∑ i ∈ s, c i * ∑ n ∈ Finset.range N, a n * (derivative^[k i] (T ℂ n)).eval (z i)‖ ≤
      (∑ i ∈ s, ‖c i‖ * (k i).factorial / (δ i) ^ k i) *
        (C * (r / ρ) ^ N / (1 - r / ρ)) := by
  rw [← s.sum_coe_sort (fun i ↦ c i * ∑ n ∈ Finset.range N,
    a n * (derivative^[k i] (T ℂ n)).eval (z i)),
    ← s.sum_coe_sort (fun i ↦ ‖c i‖ * (k i).factorial / (δ i) ^ k i),
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ ‖c i.val‖ * ((k i.val).factorial * (C * (r / ρ) ^ N / (1 - r / ρ)) /
        (δ i.val) ^ k i.val) :=
      mul_le_mul_of_nonneg_left
        (norm_iterated_derivative_complexChebyshevSeries_sub_sum_le hρ hr hrρ ha (k i.val) _
          (hz i.val i.property) (hδ i.val i.property) (hball i.val i.property) N) (norm_nonneg _)
    _ = _ := by ring

/-- Residual errors are bounded on the actual geometric derivative domain. -/
theorem norm_differentialOperator_complexChebyshevSeries_sub_sum_le
    {a : ℕ → ℂ} {C ρ r δ : ℝ} (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ)
    (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (A : ℕ → ℂ[X]) (m : ℕ)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) (hz : z.val ∈ bernsteinEllipse ⟨r, hr⟩) (hδ : 0 < δ)
    (hball : Metric.sphere z.val δ ⊆ bernsteinEllipse ⟨r, hr⟩) (N : ℕ) :
    ‖differentialOperatorOnFunctions A m (complexChebyshevSeriesDerivInput hρ ha m).val
        (.ofIterated (complexChebyshevSeriesDerivInput hρ ha m) z) -
      (differentialOperator A m (∑ n ∈ Finset.range N, a n • T ℂ n)).eval z.val‖ ≤
      (∑ k ∈ Finset.range (m + 1), ‖(A k).eval z.val‖ * k.factorial / δ ^ k) *
        (C * (r / ρ) ^ N / (1 - r / ρ)) := by
  have h := norm_boundary_complexChebyshevSeries_sub_sum_le hρ hr hrρ ha
    (Finset.range (m + 1)) (fun k ↦ (A k).eval z.val) id (fun _ ↦ z.val) (fun _ ↦ δ)
    (fun _ _ ↦ hz) (fun _ _ ↦ hδ) (fun _ _ ↦ hball) N
  have he : ∀ w : bernsteinEllipse ⟨ρ, hρ⟩,
      (∑' n, a n * (T ℂ n).eval w.val) = (complexChebyshevSeriesDerivInput hρ ha m).val w := by
    intro w
    exact (complexChebyshevSeries_eq_tsum (ComplexChebyshevSeriesPoint.ofGeometric hρ ha w)
      (summable_chebyshevSeries_of_geometric hρ ha w.property)).symm
  rw [differentialOperatorOnFunctions_eq_extension A m (complexChebyshevSeriesDerivInput hρ ha m)
    _ (analyticOnNhd_chebyshev_tsum hρ ha) he]
  simp_rw [iteratedDeriv_complexChebyshevSeries_eq] at h
  simp only [id_eq] at h
  rw [(Finset.range (m + 1)).sum_coe_sort
    (fun k ↦ (A k).eval z.val * iteratedDeriv k (fun w ↦ ∑' n, a n * (T ℂ n).eval w) z.val)] at h
  simpa only [differentialOperator_apply, iterate_derivative_sum, iterate_derivative_smul,
    eval_finsetSum, eval_mul, eval_smul, smul_eq_mul, id_eq] using h

end Chebyshev
end Polynomial
