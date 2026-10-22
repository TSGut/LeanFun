/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Basis.FiniteSection
public import LeanFun.Mathlib.Analysis.Polynomial.SeriesMultiplication
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-! # Coefficient maps on convergent polynomial expansions
The same basis matrices as the finite algebraic API collect infinite input
coefficients. Absolute convergence is explicit; banded rows remain finite sums.
Reference: Olver--Townsend (2013), Sections 2--3.
-/

@[expose] public section
namespace Module.Basis
open Polynomial
variable {R : Type*} [CommRing R]

/-- Input whose selected matrix row converges classically. -/
abbrev SeriesCoefficientInput (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (i : ℕ) :=
  {a : ℕ → ℂ // Summable (fun j ↦ a j * σ (c.repr (L (b j)) i))}

/-- The sum of a certified convergent matrix row. -/
noncomputable def seriesCoefficientMap (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) {i : ℕ}
    (a : SeriesCoefficientInput b c L σ i) : ℂ :=
  ∑' j, a.val j * σ (c.repr (L (b j)) i)

/-- Characterization by the classical row sum. -/
theorem hasSum_seriesCoefficientMap_row (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) {i : ℕ}
    (a : SeriesCoefficientInput b c L σ i) :
    HasSum (fun j ↦ a.val j * σ (c.repr (L (b j)) i))
      (b.seriesCoefficientMap c L σ a) := a.property.hasSum

/-- Banded rows are finite, for every input sequence. -/
def SeriesCoefficientInput.ofBanded (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (a : ℕ → ℂ) {l u : ℕ}
    (hL : (c.toMatrix (fun j ↦ L (b j))).IsBanded l u) (i : ℕ) :
    SeriesCoefficientInput b c L σ i := by
  refine ⟨a, ?_⟩
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (i + u + 1)) ?_).summable
  intro j hj
  have hz := hL i j (Or.inr (by simp only [Finset.mem_range] at hj; omega))
  change c.repr (L (b j)) i = 0 at hz
  rw [hz, map_zero, mul_zero]

/-- Finitely supported inputs give convergent rows for every polynomial map. -/
def SeriesCoefficientInput.ofFinsupp (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (v : ℕ →₀ R) (i : ℕ) :
    SeriesCoefficientInput b c L σ i := by
  classical
  refine ⟨fun j ↦ σ (v j), ?_⟩
  apply (hasSum_sum_of_ne_finset_zero (s := v.support) ?_).summable
  intro j hj
  simp only [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul]

/-- Finite basis reconstruction is also an unconditional evaluation series. -/
theorem hasSum_repr_eval₂ (c : Basis ℕ R R[X]) (σ : R →+* ℂ) (p : R[X]) (z : ℂ) :
    HasSum (fun i ↦ σ (c.repr p i) * (c i).eval₂ σ z) (p.eval₂ σ z) := by
  classical
  have he := congrArg (fun q : R[X] ↦ q.eval₂ σ z) (c.linearCombination_repr p)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, eval₂_finsetSum, eval₂_smul] at he
  rw [← he]
  apply hasSum_sum_of_ne_finset_zero
  intro i hi
  rw [Finsupp.notMem_support_iff.mp hi, map_zero, zero_mul]

/-- Absolute convergence permits regrouping weighted contributions, including
zero output modes, without asserting convergence of unweighted rows. -/
theorem hasSum_seriesCoefficientMap (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (a : ℕ → ℂ) (z : ℂ)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (L (b p.1)) p.2) * (c p.2).eval₂ σ z‖)) :
    HasSum (fun i ↦ regroupCoefficients
      (RegroupCoefficientInput.ofSummableNorm habs Prod.snd i))
      (∑' j, a j * (L (b j)).eval₂ σ z) := by
  have hs := habs.of_norm
  have hcol (j : ℕ) : (∑' i, a j * σ (c.repr (L (b j)) i) * (c i).eval₂ σ z) =
      a j * (L (b j)).eval₂ σ z := by
    simpa only [mul_assoc] using ((c.hasSum_repr_eval₂ σ (L (b j)) z).mul_left (a j)).tsum_eq
  have he : (∑' p : ℕ × ℕ, a p.1 * σ (c.repr (L (b p.1)) p.2) * (c p.2).eval₂ σ z) =
      ∑' j, a j * (L (b j)).eval₂ σ z := by
    rw [hs.tsum_prod]
    exact tsum_congr hcol
  simpa only [he, regroupCoefficients, RegroupCoefficientInput.ofSummableNorm,
    RegroupCoefficientInput.ofSummable, Set.preimage_singleton, Set.coe_ofPred] using hs.hasSum.tsum_fiberwise Prod.snd

/-- Certified coefficient rows can be factored from their output modes. -/
theorem hasSum_seriesCoefficientMap_of_rows (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (a : ℕ → ℂ) (z : ℂ)
    (habs : Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (L (b p.1)) p.2) * (c p.2).eval₂ σ z‖))
    (rows : ∀ i, SeriesCoefficientInput b c L σ i)
    (hrows : ∀ i, (rows i).val = a) :
    HasSum (fun i ↦ b.seriesCoefficientMap c L σ (rows i) * (c i).eval₂ σ z)
      (∑' j, a j * (L (b j)).eval₂ σ z) := by
  have hs := habs.of_norm
  have hcol (j : ℕ) : (∑' i, a j * σ (c.repr (L (b j)) i) * (c i).eval₂ σ z) =
      a j * (L (b j)).eval₂ σ z := by
    simpa only [mul_assoc] using ((c.hasSum_repr_eval₂ σ (L (b j)) z).mul_left (a j)).tsum_eq
  have he : (∑' p : ℕ × ℕ, a p.1 * σ (c.repr (L (b p.1)) p.2) * (c p.2).eval₂ σ z) =
      ∑' j, a j * (L (b j)).eval₂ σ z := by
    rw [hs.tsum_prod]
    exact tsum_congr hcol
  have h := hs.prod_symm.prod.hasSum
  simp only [Prod.swap_prod_mk] at h
  have he' : (∑' i, ∑' j, a j * σ (c.repr (L (b j)) i) * (c i).eval₂ σ z) =
      ∑' j, a j * (L (b j)).eval₂ σ z := by
    rw [hs.tsum_comm]
    exact tsum_congr hcol
  rw [he'] at h
  simpa only [seriesCoefficientMap, hrows, tsum_mul_right] using h

/-- Banded matrix rows define finite sums even on an infinite input sequence.
No convergence hypothesis is needed for this coordinate identity. -/
theorem seriesCoefficientMap_eq_sum_of_isBanded (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (a : ℕ → ℂ) {l u : ℕ}
    (hL : (c.toMatrix (fun j ↦ L (b j))).IsBanded l u) (i : ℕ) :
    b.seriesCoefficientMap c L σ (.ofBanded b c L σ a hL i) =
      ∑ j ∈ Finset.range (i + u + 1), a j * σ (c.toMatrix (fun j ↦ L (b j)) i j) := by
  classical
  simp only [seriesCoefficientMap, SeriesCoefficientInput.ofBanded, toMatrix_apply]
  apply tsum_eq_sum
  intro j hj
  have hz := hL i j (Or.inr (by simp only [Finset.mem_range] at hj; omega))
  change c.repr (L (b j)) i = 0 at hz
  rw [hz, map_zero, mul_zero]

/-- On finitely supported input, the series action is exactly the existing
finite coefficient map, embedded by the coefficient homomorphism. -/
theorem seriesCoefficientMap_finsupp (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (v : ℕ →₀ R) (i : ℕ) :
    b.seriesCoefficientMap c L σ (.ofFinsupp b c L σ v i) = σ (b.coefficientMap c L v i) := by
  classical
  rw [coefficientMap_apply, Finsupp.sum, map_sum]
  simp only [seriesCoefficientMap, SeriesCoefficientInput.ofFinsupp, toMatrix_apply, map_mul, mul_comm]
  apply tsum_eq_sum
  intro j hj
  rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul]

/-- A single weighted coefficient sum suffices for absolute convergence of
matrix reconstruction; every polynomial matrix column has finite support. -/
theorem summable_norm_seriesCoefficientMap_terms (b c : Basis ℕ R R[X])
    (L : R[X] →ₗ[R] R[X]) (σ : R →+* ℂ) (a : ℕ → ℂ) (z : ℂ) (w : ℕ → ℝ)
    (hw : ∀ i, ‖(c i).eval₂ σ z‖ ≤ w i)
    (ha : Summable (fun j ↦ ‖a j‖ * ∑ i ∈ (c.repr (L (b j))).support,
      ‖σ (c.repr (L (b j)) i)‖ * w i)) :
    Summable (fun p : ℕ × ℕ ↦
      ‖a p.1 * σ (c.repr (L (b p.1)) p.2) * (c p.2).eval₂ σ z‖) := by
  classical
  have hw0 (i : ℕ) : 0 ≤ w i := (norm_nonneg _).trans (hw i)
  have hrow (j : ℕ) : HasSum (fun i ↦ ‖a j‖ * ‖σ (c.repr (L (b j)) i)‖ * w i)
      (‖a j‖ * ∑ i ∈ (c.repr (L (b j))).support, ‖σ (c.repr (L (b j)) i)‖ * w i) := by
    rw [Finset.mul_sum]
    simp only [← mul_assoc]
    apply hasSum_sum_of_ne_finset_zero
    intro i hi
    rw [Finsupp.notMem_support_iff.mp hi, map_zero, norm_zero, mul_zero, zero_mul]
  have hs : Summable (fun p : ℕ × ℕ ↦ ‖a p.1‖ *
      ‖σ (c.repr (L (b p.1)) p.2)‖ * w p.2) := by
    apply (summable_prod_of_nonneg (fun p ↦
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw0 p.2))).2
    refine ⟨fun j ↦ (hrow j).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using ha
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hs
  intro p
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (hw p.2) (by positivity)

end Module.Basis
