/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.IteratedSeriesCalculus
public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCoefficientMap
public import LeanFun.Mathlib.Algebra.Polynomial.DifferentialOperator

public import LeanFun.Mathlib.Analysis.Calculus.IteratedDeriv.Pointwise
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Differential operators on convergent polynomial expansions
Polynomial operator assembly agrees with analytic differentiation of a normally
convergent expansion. Cauchy estimates control residuals and boundary data.
Reference: Olver--Townsend (2013), Section 3; ATAP, Chapters 8 and 21.
-/

@[expose] public noncomputable section
namespace Polynomial

/-- A finite differential expression, only at points possessing its derivative jet. -/
noncomputable def differentialOperatorOnFunctions (A : ℕ → ℂ[X]) (m : ℕ)
    {U : TopologicalSpace.Opens ℂ} (f : U → ℂ) (z : DerivativeJetPoint U m f) : ℂ :=
  ∑ k : Fin (m + 1), (A k.val).eval z.val.val * derivativeJet z k

/-- Actual derivative chains supply the pointwise differential action. -/
theorem differentialOperatorOnFunctions_ofIterated
    (A : ℕ → ℂ[X]) (m : ℕ) {U : TopologicalSpace.Opens ℂ}
    (f : IteratedDerivInput U m) (z : U) :
    differentialOperatorOnFunctions A m f.val (.ofIterated f z) =
      ∑ k : Fin (m + 1), (A k.val).eval z.val *
        iteratedDerivOnOpen (f.truncate (Nat.le_of_lt_succ k.isLt)) z := by
  unfold differentialOperatorOnFunctions
  apply Finset.sum_congr rfl
  intro k _
  change (A k.val).eval z.val * derivativeJet (DerivativeJetPoint.ofIterated f z) k = _
  rw [derivativeJet_ofIterated]

/-- Internal bridge on an actual domain of analyticity. -/
theorem differentialOperatorOnFunctions_eq_extension
    (A : ℕ → ℂ[X]) (m : ℕ) {U : TopologicalSpace.Opens ℂ}
    (f : IteratedDerivInput U m) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F U) (he : ∀ x : U, F x = f.val x) (z : U) :
    differentialOperatorOnFunctions A m f.val (.ofIterated f z) =
      ∑ k ∈ Finset.range (m + 1), (A k).eval z.val * iteratedDeriv k F z.val := by
  rw [differentialOperatorOnFunctions_ofIterated]
  have hd (k : Fin (m + 1)) :
      iteratedDerivOnOpen (f.truncate (Nat.le_of_lt_succ k.isLt)) z =
        iteratedDeriv k.val F z.val :=
    congrFun (iteratedDerivOnOpen_eq_iteratedDeriv
      (f.truncate (Nat.le_of_lt_succ k.isLt)) F hF he) z
  simp_rw [hd]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (A k).eval z.val * iteratedDeriv k F z.val) (m + 1)

end Polynomial

public section
namespace Polynomial
open Complex Set

/-- Applying a polynomial differential operator termwise represents its analytic action. -/
private theorem hasSum_differentialOperator_series_tsum {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun n ↦ a n * (differentialOperator A m (P n)).eval z)
      ((∑ k ∈ Finset.range (m + 1), (A k).eval z * iteratedDeriv k (fun w ↦ ∑' n, a n * (P n).eval w) z)) := by
  have h := hasSum_sum (s := Finset.range (m + 1)) (fun k _ ↦
    (hasSum_iterated_derivative_series hU hu hb k hz).mul_left ((A k).eval z))
  simpa only [differentialOperator_apply,
    eval_finsetSum, eval_mul, Finset.mul_sum, mul_left_comm] using h

/-- Absolute matrix reconstruction identifies the assembled coefficient series
with the differential operator on the represented analytic function. -/
private theorem hasSum_seriesCoefficientMap_differentialOperator_tsum
    (b c : Module.Basis ℕ ℂ ℂ[X]) {a : ℕ → ℂ} {u : ℕ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (b n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) {z : ℂ} (hz : z ∈ U)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * c.repr (differentialOperator A m (b p.1)) p.2 * (c p.2).eval z‖)) :
    HasSum (fun i ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm habs Prod.snd i))
      ((∑ k ∈ Finset.range (m + 1), (A k).eval z * iteratedDeriv k (fun w ↦ ∑' n, a n * (b n).eval w) z)) := by
  have h := b.hasSum_seriesCoefficientMap c (differentialOperator A m) (RingHom.id ℂ) a z habs
  simpa only [eval₂_id, RingHom.id_apply,
    (hasSum_differentialOperator_series_tsum hU hu hb A m hz).tsum_eq] using h

/-- A finite combination of derivative evaluations has an explicit truncation
error. This includes endpoint values, derivatives, and Robin boundary rows. -/
private theorem norm_boundary_series_sub_sum_le_tsum {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℕ) (z : ι → ℂ) (δ : ι → ℝ)
    (hz : ∀ i ∈ s, z i ∈ U) (hδ : ∀ i ∈ s, 0 < δ i)
    (hball : ∀ i ∈ s, Metric.sphere (z i) (δ i) ⊆ U) (N : ℕ) :
    ‖(∑ i ∈ s, c i * iteratedDeriv (k i) (fun w ↦ ∑' n, a n * (P n).eval w) (z i)) -
      ∑ i ∈ s, c i * ∑ n ∈ Finset.range N, a n * (derivative^[k i] (P n)).eval (z i)‖ ≤
      (∑ i ∈ s, ‖c i‖ * (k i).factorial / (δ i) ^ k i) * (∑' n, u (n + N)) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ ‖c i‖ * ((k i).factorial * (∑' n, u (n + N)) / (δ i) ^ k i) :=
      mul_le_mul_of_nonneg_left
        (norm_iterated_derivative_series_sub_sum_le hU hu hb (k i)
          (hz i hi) (hδ i hi) (hball i hi) N) (norm_nonneg _)
    _ = _ := by ring

/-- Residual truncation is controlled by the same original coefficient tail,
with explicit polynomial-coefficient and Cauchy-radius factors. -/
private theorem norm_differentialOperator_series_sub_sum_le_tsum {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) {z : ℂ} (hz : z ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.sphere z δ ⊆ U) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (m + 1), (A k).eval z * iteratedDeriv k (fun w ↦ ∑' n, a n * (P n).eval w) z) -
      (differentialOperator A m (∑ n ∈ Finset.range N, a n • P n)).eval z‖ ≤
      (∑ k ∈ Finset.range (m + 1), ‖(A k).eval z‖ * k.factorial / δ ^ k) *
        (∑' n, u (n + N)) := by
  have h := norm_boundary_series_sub_sum_le_tsum hU hu hb (Finset.range (m + 1))
    (fun k ↦ (A k).eval z) id (fun _ ↦ z) (fun _ ↦ δ)
    (fun _ _ ↦ hz) (fun _ _ ↦ hδ) (fun _ _ ↦ hball) N
  simpa only [differentialOperator_apply,
    iterate_derivative_sum, iterate_derivative_smul, eval_finsetSum, eval_mul,
    eval_smul, smul_eq_mul, id_eq] using h

/-- The same consistency private theorem uses the original coefficient-ring bases,
with complex evaluation through a homomorphism. In particular real
ultraspherical matrices need not be redefined over complex scalars. -/
private theorem hasSum_seriesCoefficientMap_differentialOperator_eval₂_tsum
    {R : Type*} [CommRing R] (b c : Module.Basis ℕ R R[X]) (σ : R →+* ℂ)
    {a : ℕ → ℂ} {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (b n).eval₂ σ z‖ ≤ u n)
    (A : ℕ → R[X]) (m : ℕ) {z : ℂ} (hz : z ∈ U)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (differentialOperator A m (b p.1)) p.2) *
        (c p.2).eval₂ σ z‖)) :
    HasSum (fun i ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm habs Prod.snd i))
      ((∑ k ∈ Finset.range (m + 1), ((fun k ↦ (A k).map σ) k).eval z * iteratedDeriv k (fun w ↦ ∑' n, a n * (b n).eval₂ σ w) z)) := by
  have hb' : ∀ n z, z ∈ U → ‖a n * ((b n).map σ).eval z‖ ≤ u n := by
    simpa only [eval_map] using hb
  have hs := hasSum_differentialOperator_series_tsum hU hu hb'
    (fun k ↦ (A k).map σ) m hz
  simp only [← differentialOperator_map, eval_map] at hs
  have h := b.hasSum_seriesCoefficientMap c (differentialOperator A m) σ a z habs
  rw [hs.tsum_eq] at h
  simpa only [eval_map] using h

end Polynomial

@[expose] public noncomputable section
namespace Polynomial
open Complex Set Filter
open scoped Topology

/-- Internal analytic representative, used only on its domain of normal convergence. -/
private theorem analyticOnNhd_polynomial_tsum {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' n, a n * (P n).eval z) U :=
  (differentiableOn_tsum_of_summable_norm hu
    (fun n ↦ ((P n).differentiable.const_mul (a n)).differentiableOn)
    U.isOpen hb).analyticOnNhd U.isOpen

/-- A normally convergent polynomial expansion is analytic on its typed domain. -/
theorem analyticOnOpen_of_hasSum_polynomial {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    {f : U → ℂ} (hf : ∀ z : U, HasSum (fun n ↦ a n * (P n).eval z.val) (f z)) :
    AnalyticOnOpen U f :=
  (analyticOnOpen_iff U f (fun z ↦ ∑' n, a n * (P n).eval z)
    (fun z ↦ (hf z).tsum_eq)).2 (analyticOnNhd_polynomial_tsum hu hb)

/-- Normal convergence supplies a derivative input of every finite order. -/
theorem exists_iteratedDerivInput_of_polynomialSeries {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n) (m : ℕ) :
    ∃ f : IteratedDerivInput U m,
      ∀ z : U, HasSum (fun n ↦ a n * (P n).eval z.val) (f.val z) := by
  have hs (z : U) : HasSum (fun n ↦ a n * (P n).eval z.val)
      (∑' n, a n * (P n).eval z.val) :=
    ((Summable.of_nonneg_of_le (fun n ↦ norm_nonneg (a n * (P n).eval z.val))
      (fun n ↦ hb n z.val z.property) hu).of_norm).hasSum
  exact ⟨.ofAnalytic _ (analyticOnOpen_of_hasSum_polynomial hu hb hs) m, hs⟩

/-- Polynomial functions supply actual derivative chains on every open domain. -/
def iteratedDerivInputOnOpen (p : ℂ[X]) (U : TopologicalSpace.Opens ℂ) (m : ℕ) :
    IteratedDerivInput U m :=
  .ofAnalytic (fun z ↦ p.eval z.val)
    ((analyticOnOpen_iff U _ (fun z ↦ p.eval z) (fun _ ↦ rfl)).2
      (p.differentiable.differentiableOn.analyticOnNhd U.isOpen)) m

@[simp] theorem iteratedDerivInputOnOpen_val (p : ℂ[X]) (U : TopologicalSpace.Opens ℂ) (m : ℕ) :
    (p.iteratedDerivInputOnOpen U m).val = fun z : U ↦ p.eval z.val := rfl

/-- Classical differential action agrees with polynomial differential action. -/
theorem differentialOperatorOnFunctions_eval (A : ℕ → ℂ[X]) (m : ℕ)
    (p : ℂ[X]) (U : TopologicalSpace.Opens ℂ) (z : U) :
    differentialOperatorOnFunctions A m (p.iteratedDerivInputOnOpen U m).val
      (.ofIterated (p.iteratedDerivInputOnOpen U m) z) =
      (differentialOperator A m p).eval z.val := by
  rw [differentialOperatorOnFunctions_eq_extension A m (p.iteratedDerivInputOnOpen U m)
    (fun z ↦ p.eval z) (p.differentiable.differentiableOn.analyticOnNhd U.isOpen) (fun _ ↦ rfl)]
  simp only [iteratedDeriv_eval, differentialOperator_apply, eval_finsetSum, eval_mul]

/-- Termwise application represents the actual differential action. -/
theorem hasSum_differentialOperator_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (P n).eval z.val) (f.val z)) (z : U) :
    HasSum (fun n ↦ a n * (differentialOperator A m (P n)).eval z.val)
      (differentialOperatorOnFunctions A m f.val (.ofIterated f z)) := by
  rw [differentialOperatorOnFunctions_eq_extension A m f
    (fun z ↦ ∑' n, a n * (P n).eval z) (analyticOnNhd_polynomial_tsum hu hb)
    (fun z ↦ (hf z).tsum_eq)]
  exact hasSum_differentialOperator_series_tsum U.isOpen hu hb A m z.property

/-- Absolute coefficient reconstruction agrees with the classical differential action. -/
theorem hasSum_seriesCoefficientMap_differentialOperator
    (b c : Module.Basis ℕ ℂ ℂ[X]) {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (b n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (b n).eval z.val) (f.val z)) (z : U)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * c.repr (differentialOperator A m (b p.1)) p.2 * (c p.2).eval z.val‖)) :
    HasSum (fun i ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm habs Prod.snd i))
      (differentialOperatorOnFunctions A m f.val (.ofIterated f z)) := by
  rw [differentialOperatorOnFunctions_eq_extension A m f
    (fun z ↦ ∑' n, a n * (b n).eval z) (analyticOnNhd_polynomial_tsum hu hb)
    (fun z ↦ (hf z).tsum_eq)]
  exact hasSum_seriesCoefficientMap_differentialOperator_tsum b c U.isOpen hu hb A m z.property habs

/-- Differential residual error on the genuine derivative domain. -/
theorem norm_differentialOperator_series_sub_sum_le {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (A : ℕ → ℂ[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (P n).eval z.val) (f.val z))
    (z : U) {δ : ℝ} (hδ : 0 < δ) (hball : Metric.sphere z.val δ ⊆ U) (N : ℕ) :
    ‖differentialOperatorOnFunctions A m f.val (.ofIterated f z) -
      (differentialOperator A m (∑ n ∈ Finset.range N, a n • P n)).eval z.val‖ ≤
      (∑ k ∈ Finset.range (m + 1), ‖(A k).eval z.val‖ * k.factorial / δ ^ k) *
        (∑' n, u (n + N)) := by
  rw [differentialOperatorOnFunctions_eq_extension A m f
    (fun z ↦ ∑' n, a n * (P n).eval z) (analyticOnNhd_polynomial_tsum hu hb)
    (fun z ↦ (hf z).tsum_eq)]
  exact norm_differentialOperator_series_sub_sum_le_tsum U.isOpen hu hb A m z.property hδ hball N

/-- The reconstruction also respects coefficient-ring evaluation maps. -/
theorem hasSum_seriesCoefficientMap_differentialOperator_eval₂
    {R : Type*} [CommRing R] (b c : Module.Basis ℕ R R[X]) (σ : R →+* ℂ)
    {a : ℕ → ℂ} {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (b n).eval₂ σ z‖ ≤ u n)
    (A : ℕ → R[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (b n).eval₂ σ z.val) (f.val z)) (z : U)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (differentialOperator A m (b p.1)) p.2) *
        (c p.2).eval₂ σ z.val‖)) :
    HasSum (fun i ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm habs Prod.snd i))
      (differentialOperatorOnFunctions (fun k ↦ (A k).map σ) m f.val (.ofIterated f z)) := by
  have hb' : ∀ n z, z ∈ U → ‖a n * ((b n).map σ).eval z‖ ≤ u n := by
    simpa only [eval_map] using hb
  rw [differentialOperatorOnFunctions_eq_extension _ m f
    (fun z ↦ ∑' n, a n * ((b n).map σ).eval z) (analyticOnNhd_polynomial_tsum hu hb')
    (fun z ↦ by simpa only [eval_map] using (hf z).tsum_eq)]
  simpa only [eval_map] using
    hasSum_seriesCoefficientMap_differentialOperator_eval₂_tsum b c σ U.isOpen hu hb A m z.property habs

end Polynomial

public section
namespace Polynomial
open Set

/-- Boundary combinations use only certified derivatives at the finitely many
points that actually occur, retaining the empty-sum and empty-domain cases. -/
theorem norm_boundary_series_sub_sum_le {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (f : U → ℂ) (hf : ∀ z : U, HasSum (fun n ↦ a n * (P n).eval z.val) (f z))
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℕ) (z : ι → ℂ) (δ : ι → ℝ)
    (hz : ∀ i ∈ s, z i ∈ U) (hδ : ∀ i ∈ s, 0 < δ i)
    (hball : ∀ i ∈ s, Metric.sphere (z i) (δ i) ⊆ U) (N : ℕ) :
    ‖(∑ i : s, c i.val * iteratedDerivOnOpen
        (IteratedDerivInput.ofAnalytic f (analyticOnOpen_of_hasSum_polynomial hu hb hf) (k i.val))
        ⟨z i.val, hz i.val i.property⟩) -
      ∑ i ∈ s, c i * ∑ n ∈ Finset.range N, a n * (derivative^[k i] (P n)).eval (z i)‖ ≤
      (∑ i ∈ s, ‖c i‖ * (k i).factorial / (δ i) ^ k i) * (∑' n, u (n + N)) := by
  have hd (i : s) : iteratedDerivOnOpen
      (IteratedDerivInput.ofAnalytic f (analyticOnOpen_of_hasSum_polynomial hu hb hf) (k i.val))
      ⟨z i.val, hz i.val i.property⟩ =
      iteratedDeriv (k i.val) (fun w ↦ ∑' n, a n * (P n).eval w) (z i.val) :=
    congrFun (iteratedDerivOnOpen_eq_iteratedDeriv _
      (fun w ↦ ∑' n, a n * (P n).eval w) (analyticOnNhd_polynomial_tsum hu hb)
      (fun w ↦ (hf w).tsum_eq)) ⟨z i.val, hz i.val i.property⟩
  simp_rw [hd]
  rw [s.sum_coe_sort (fun i ↦ c i * iteratedDeriv (k i) (fun w ↦ ∑' n, a n * (P n).eval w) (z i))]
  exact norm_boundary_series_sub_sum_le_tsum U.isOpen hu hb s c k z δ hz hδ hball N

end Polynomial

public section
namespace Polynomial

/-- Convergent coefficient rows give the coordinate form of analytic residual
reconstruction. Weighted contributions alone need not have convergent rows. -/
theorem hasSum_seriesCoefficientMap_differentialOperator_eval₂_of_rows
    {R : Type*} [CommRing R] (b c : Module.Basis ℕ R R[X]) (σ : R →+* ℂ)
    {a : ℕ → ℂ} {u : ℕ → ℝ} {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (b n).eval₂ σ z‖ ≤ u n)
    (A : ℕ → R[X]) (m : ℕ) (f : IteratedDerivInput U m)
    (hf : ∀ z : U, HasSum (fun n ↦ a n * (b n).eval₂ σ z.val) (f.val z)) (z : U)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (differentialOperator A m (b p.1)) p.2) *
        (c p.2).eval₂ σ z.val‖))
    (rows : ∀ i, b.SeriesCoefficientInput c (differentialOperator A m) σ i)
    (hrows : ∀ i, (rows i).val = a) :
    HasSum (fun i ↦ b.seriesCoefficientMap c (differentialOperator A m) σ (rows i) *
      (c i).eval₂ σ z.val)
      (differentialOperatorOnFunctions (fun k ↦ (A k).map σ) m f.val (.ofIterated f z)) := by
  have hb' : ∀ n z, z ∈ U → ‖a n * ((b n).map σ).eval z‖ ≤ u n := by
    simpa only [eval_map] using hb
  have hf' : ∀ z : U, HasSum (fun n ↦ a n * ((b n).map σ).eval z.val) (f.val z) := by
    simpa only [eval_map] using hf
  have hs := hasSum_differentialOperator_series hu hb' (fun k ↦ (A k).map σ) m f hf' z
  simp only [← differentialOperator_map, eval_map] at hs
  have h := b.hasSum_seriesCoefficientMap_of_rows c (differentialOperator A m) σ a z.val habs rows hrows
  rw [hs.tsum_eq] at h
  exact h

end Polynomial
