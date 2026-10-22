/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.MultiplicationSupport
import Mathlib.Topology.Algebra.Polynomial

/-!
# Banded block banded coordinate multiplication in both cases

A fixed polynomial scale degree gives a fixed block bandwidth. Ordinary scales
allow B=1. These statements apply independently to every compatible modified
system. Reference: Dunkl–Xu, §2.6.1 and multivariate three-term recurrences.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {μ : Measure D} {ν : Measure ℝ} [SFinite μ] [SFinite ν]

/-- With a polynomial scale, the same-inner y pairing is polynomial outer multiplication. -/
theorem multiplicationEntry_y_same_inner_polynomial (c : ℝ[X])
    (S : KoornwinderSystem (c^2) (fun x => c.eval (x : ℝ)) μ ν) (n k m : ℕ) :
    S.multiplicationEntry 1 n k m k =
      Polynomial.integralInner (koornwinderOuterMeasure (c^2) k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure (c^2) k ((Measure.map Subtype.val μ).comap Subtype.val)) (c*S.outer k (n-k)) (S.outer k (m-k))) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (Polynomial.X*S.inner k) (S.inner k)) := by
  rw [S.multiplicationEntry_y (c.continuous.comp continuous_subtype_val) n k m k
    (hi := (S.hasFiniteMoments_polynomial_scale c).integrable_mul _ _)]
  congr 1
  rw [Polynomial.integralInner, integral_koornwinderOuterMeasure_map_subtype μ (c^2)
    (Filter.Eventually.of_forall (fun x => by simp [sq_nonneg])) k ⟨fun x => (c*S.outer k (n-k)).eval x*(S.outer k (m-k)).eval x, by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])⟩]
  dsimp only
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Polynomial.eval_mul,Polynomial.eval_pow]
  have hp (z : ℝ) : z^(2*k+1) = (z^2)^k*z := by rw [pow_succ,pow_mul]
  rw [show k+k+1=2*k+1 by omega, hp]
  ring

/-- Same-inner y entries have the bandwidth of the polynomial scale. -/
theorem multiplicationEntry_y_same_inner_polynomial_eq_zero (c : ℝ[X])
    (S : KoornwinderSystem (c^2) (fun x => c.eval (x : ℝ)) μ ν)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (B : ℕ) (hcdeg : c.natDegree ≤ B)
    {n k m : ℕ} (hk : k ≤ n) (hj : k ≤ m)
    (hout : n+B < m ∨ m+B < n) : S.multiplicationEntry 1 n k m k = 0 := by
  have hz (n m : ℕ) (hn : k ≤ n) (hm : k ≤ m) (ho : n+B < m) :
      S.multiplicationEntry 1 n k m k = 0 := by
    rw [S.multiplicationEntry_y_same_inner_polynomial c]
    have hd : (c*S.outer k (n-k)).natDegree < m-k := by
      have ht := natDegree_mul_le (p := c) (q := S.outer k (n-k))
      rw [Sequence.natDegree_eq] at ht
      omega
    rw [(S.outer_orthogonal k).integralInner_eq_zero_of_degree_lt
      (hμ.koornwinderOuterMeasure (c^2) (Filter.Eventually.of_forall (fun x => by simp [sq_nonneg])) k)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd)), zero_mul]
  rcases hout with hout | hout
  · exact hz n m hk hj hout
  · rw [S.multiplicationEntry_symm]
    exact hz m n hj hk hout

/-- An even inner measure removes the same-inner y coefficient entirely. -/
theorem multiplicationEntry_y_same_inner_even {a : ℝ[X]} {ρ : D → ℝ}
    (S : KoornwinderSystem a ρ μ ν) (hρ : Continuous ρ) [ν.IsNegInvariant]
    (hν : Polynomial.HasFiniteMoments ν) (hpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (n k m : ℕ)
    (hi : Integrable (fun x => eval x (X 1*S.polynomial n k)*eval x (S.polynomial m k))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : S.multiplicationEntry 1 n k m k = 0 := by
  rw [S.multiplicationEntry_y hρ n k m k (hi := hi)]
  have hQ := S.inner_orthogonal.comp_neg_X hν hpos k
  have hXQ : (Polynomial.X*S.inner k).comp (-Polynomial.X) =
      Polynomial.C ((-1 : ℝ)^(k+1))*(Polynomial.X*S.inner k) := by
    simp only [mul_comp,X_comp,hQ,pow_succ,mul_neg_one,map_neg]
    ring
  rw [integralInner_eq_zero_of_opposite_parity hXQ hQ (by omega), mul_zero]

/-- Polynomial-scale systems have fixed y block bandwidth and inner bandwidth one. -/
theorem multiplicationEntry_y_polynomial_support (c : ℝ[X])
    (S : KoornwinderSystem (c^2) (fun x => c.eval (x : ℝ)) μ ν)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (B : ℕ) (hB : 1 ≤ B) (hcdeg : c.natDegree ≤ B) (hadeg : (c^2).natDegree ≤ B+1)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : (k+1 < j ∨ j+1 < k) ∨ n+B < m ∨ m+B < n) :
    S.multiplicationEntry 1 n k m j = 0 := by
  rcases hout with hi | ho
  · exact S.multiplicationEntry_y_eq_zero_of_inner_band (c.continuous.comp continuous_subtype_val) hν hi
  · apply S.multiplicationEntry_y_eq_zero_of_outer_band (c.continuous.comp continuous_subtype_val) (by simp) hμ hν B hB hadeg
      (fun n k m hn hm h => S.multiplicationEntry_y_same_inner_polynomial_eq_zero c hμ B hcdeg hn hm h)
      hk hj ho

/-- Even-inner systems with polynomial squared scale also have fixed y bandwidths. -/
theorem multiplicationEntry_y_even_support {a : ℝ[X]} {ρ : D → ℝ}
    (S : KoornwinderSystem a ρ μ ν) [ν.IsNegInvariant]
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hν : Polynomial.HasFiniteMoments ν)
    (hpos : Polynomial.HasPositiveDefiniteIntegral ν) (hρ : Continuous ρ)
    (ha : ∀ᵐ (x : D) ∂μ, ρ x^2 = a.eval (x : ℝ))
    (B : ℕ) (hB : 1 ≤ B) (hadeg : a.natDegree ≤ B+1)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : (k+1 < j ∨ j+1 < k) ∨ n+B < m ∨ m+B < n) :
    S.multiplicationEntry 1 n k m j = 0 := by
  rcases hout with hi | ho
  · exact S.multiplicationEntry_y_eq_zero_of_inner_band hρ hν hi
  · exact S.multiplicationEntry_y_eq_zero_of_outer_band hρ ha hμ hν B hB hadeg
      (fun n k m _ _ _ => S.multiplicationEntry_y_same_inner_even hρ hν hpos n k m) hk hj ho

end MvPolynomial.KoornwinderSystem
