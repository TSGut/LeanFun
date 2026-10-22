/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.MultiplicationPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

import Mathlib.Topology.Algebra.Polynomial

/-!
# Coordinate multiplication bandwidths

The x operator preserves the inner label. For y, adjacent inner labels reduce
to shifted outer orthogonality. Reference: Dunkl–Xu, multivariate recurrences.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} (S : KoornwinderSystem a ρ μ ν)
    [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
include hρ ha

/-- Multiplication by x has block bandwidth one and no off-diagonal inner indices. -/
theorem multiplicationEntry_x_eq_zero (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ))
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : k ≠ j ∨ n+1 < m ∨ m+1 < n) : S.multiplicationEntry 0 n k m j = 0 := by
  rw [S.multiplicationEntry_x hρ n k m j (hi := (S.hasFiniteMoments hρ ha).integrable_mul _ _)]
  by_cases hkj : k=j
  · subst j
    rw [S.inner_norm, mul_one]
    have he : (∫ x : D, (x : ℝ)*(S.outer k (n-k)).eval (x : ℝ)*(S.outer k (m-k)).eval (x : ℝ)*ρ x^(k+k) ∂μ) =
        Polynomial.integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.X*S.outer k (n-k)) (S.outer k (m-k))) := by
      simp only [Polynomial.integralInner]
      have hpos := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
      have hpair := (hμ.koornwinderOuterMeasure a
        (ae_nonneg_eval_map_subtype hpos) k).integrable_mul
          (Polynomial.X*S.outer k (n-k)) (S.outer k (m-k))
      have ht := integral_koornwinderOuterMeasure_map_subtype μ a hpos k
        ⟨fun x : ℝ => (Polynomial.X*S.outer k (n-k)).eval x *
          (S.outer k (m-k)).eval x, hpair⟩
      dsimp only at ht
      rw [ht]
      apply integral_congr_ae
      filter_upwards [ha] with x hx
      rw [show k+k=2*k by omega, pow_mul, hx]
      simp only [Polynomial.eval_mul,Polynomial.eval_X]
      ring
    rw [he]
    exact (S.outer_orthogonal k).integralInner_X_mul_eq_zero
      (hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x)))) k)
      (by omega)
  · rw [show Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (S.inner k) (S.inner j)) = 0 from
      S.inner_orthogonal.orthogonal k j hkj, mul_zero]

/-- An upward inner step turns y multiplication into the next shifted outer pairing. -/
theorem multiplicationEntry_y_succ_inner (n k m : ℕ) :
    S.multiplicationEntry 1 n k m (k+1) =
      Polynomial.integralInner (koornwinderOuterMeasure a (k+1) ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a (k+1) ((Measure.map Subtype.val μ).comap Subtype.val)) (S.outer k (n-k)) (S.outer (k+1) (m-(k+1)))) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (Polynomial.X*S.inner k) (S.inner (k+1))) := by
  rw [S.multiplicationEntry_y hρ n k m (k+1) (hi := (S.hasFiniteMoments hρ ha).integrable_mul _ _)]
  congr 1
  rw [Polynomial.integralInner, integral_koornwinderOuterMeasure_map_subtype μ a
    (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))) (k+1) ⟨fun x => (S.outer k (n-k)).eval x*(S.outer (k+1) (m-(k+1))).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩]
  dsimp only
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [show k+(k+1)+1=2*(k+1) by omega, pow_mul, hx]
  ring

/-- The same pairing can transfer one squared radius to the old outer measure. -/
theorem multiplicationEntry_y_succ_inner_transfer (n k m : ℕ) :
    S.multiplicationEntry 1 n k m (k+1) =
      Polynomial.integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (a*S.outer (k+1) (m-(k+1))) (S.outer k (n-k))) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (Polynomial.X*S.inner k) (S.inner (k+1))) := by
  rw [S.multiplicationEntry_y_succ_inner hρ ha]
  congr 1
  have hapos := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
  rw [Polynomial.integralInner, Polynomial.integralInner,
    integral_koornwinderOuterMeasure_map_subtype μ a hapos (k+1) ⟨fun x => (S.outer k (n-k)).eval x*(S.outer (k+1) (m-(k+1))).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩,
    integral_koornwinderOuterMeasure_map_subtype μ a hapos k ⟨fun x => (a*S.outer (k+1) (m-(k+1))).eval x*(S.outer k (n-k)).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩]
  dsimp only
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Polynomial.eval_mul,pow_succ]
  ring

/-- Adjacent inner labels have a bounded outer bandwidth, controlled by degree(a). -/
theorem multiplicationEntry_y_succ_inner_eq_zero (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ))
    (B : ℕ) (hB : 1 ≤ B) (hadeg : a.natDegree ≤ B+1)
    {n k m : ℕ} (hk : k ≤ n) (hj : k+1 ≤ m)
    (hout : n+B < m ∨ m+B < n) : S.multiplicationEntry 1 n k m (k+1) = 0 := by
  have hapos := ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))
  rcases hout with hout | hout
  · rw [S.multiplicationEntry_y_succ_inner hρ ha]
    have hd : (S.outer k (n-k)).degree < m-(k+1) := by
      rw [Sequence.degree_eq]
      exact_mod_cast (show n-k < m-(k+1) by omega)
    rw [(S.outer_orthogonal (k+1)).integralInner_eq_zero_of_degree_lt
      (hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype hapos) (k+1)) hd, zero_mul]
  · rw [S.multiplicationEntry_y_succ_inner_transfer hρ ha]
    have hd : (a*S.outer (k+1) (m-(k+1))).natDegree < n-k := by
      have he := natDegree_mul_le (p := a) (q := S.outer (k+1) (m-(k+1)))
      rw [Sequence.natDegree_eq] at he
      omega
    rw [(S.outer_orthogonal k).integralInner_eq_zero_of_degree_lt
      (hμ.koornwinderOuterMeasure a (ae_nonneg_eval_map_subtype hapos) k)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd)), zero_mul]

/-- The diagonal-inner case is the only remaining ingredient for outer y bandwidth. -/
theorem multiplicationEntry_y_eq_zero_of_outer_band
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (B : ℕ) (hB : 1 ≤ B) (hadeg : a.natDegree ≤ B+1)
    (hdiag : ∀ n k m, k ≤ n → k ≤ m → n+B < m ∨ m+B < n →
      S.multiplicationEntry 1 n k m k = 0)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : n+B < m ∨ m+B < n) : S.multiplicationEntry 1 n k m j = 0 := by
  by_cases hi : k+1 < j ∨ j+1 < k
  · exact S.multiplicationEntry_y_eq_zero_of_inner_band hρ hν hi
  have hc : k=j ∨ j=k+1 ∨ k=j+1 := by omega
  rcases hc with hc | hc | hc
  · subst j
    exact hdiag n k m hk hj hout
  · subst j
    exact S.multiplicationEntry_y_succ_inner_eq_zero hρ ha hμ B hB hadeg hk hj hout
  · subst k
    rw [S.multiplicationEntry_symm]
    exact S.multiplicationEntry_y_succ_inner_eq_zero hρ ha hμ B hB hadeg hj hk hout.symm

end MvPolynomial.KoornwinderSystem
