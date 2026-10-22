/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Parity

import Mathlib.Topology.Algebra.Polynomial

/-!
# Construction of polynomial-scale and square-root-scale systems

Both generalized Koornwinder cases exist under finite moments and positive
polynomial pairings. Only the square-root case requires inner parity.
Reference: Dunkl–Xu, §2.6.1.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {D : Set ℝ}

/-- Assemble the shifted outer sequences around supplied normalized inner data. -/
noncomputable def koornwinderSystemOfLift (a : ℝ[X]) (ρ : D → ℝ) (μ : Measure D) (ν : Measure ℝ)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (ha0 : a ≠ 0) (ha : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ))
    (Q : Polynomial.Sequence ℝ) (hQ : Q.IsOrthogonal ν)
    (hQl : ∀ k, 0 < (Q k).leadingCoeff)
    (hQn : ∀ k, Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (Q k) (Q k)) = 1)
    (L : ℕ → MvPolynomial (Fin 2) ℝ)
    (hL : ∀ k, ∀ᵐ (x : D) ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) (L k) =
      ρ x^k*(Q k).eval z) : KoornwinderSystem a ρ μ ν := by
  have he (k : ℕ) := exists_positive_orthonormal_sequence (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val))
    (hμ.koornwinderOuterMeasure a
      (ae_nonneg_eval_map_subtype ha) k)
    (hpos.koornwinderOuterMeasure hμ a ha0
      (ae_nonneg_eval_map_subtype ha) k)
  choose P hP hPl hPn using he
  exact ⟨ha,P,Q,L,hL,hQ,hP,hQl,hPl,hQn,fun k n => by
    simpa only [Polynomial.integralInner_self] using hPn k n⟩

/-- Generalized Case I: the scale is any nonzero polynomial. -/
noncomputable def polynomialScaleKoornwinderSystem (r : ℝ[X]) (μ : Measure D) (ν : Measure ℝ)
    (hr : r ≠ 0) (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ))
    (hμpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν) :
    KoornwinderSystem (r^2) (fun x : D => r.eval (x : ℝ)) μ ν := by
  choose Q hQ hQl hQn using exists_positive_orthonormal_sequence ν hν hνpos
  refine koornwinderSystemOfLift (r^2) (fun x : D => r.eval (x : ℝ)) μ ν hμ hμpos
    (pow_ne_zero _ hr) (Filter.Eventually.of_forall (fun x => by simp [sq_nonneg]))
    Q hQ hQl (fun k => by simpa only [Polynomial.integralInner_self] using hQn k)
    (fun k => scaledLift r 1 k (Q k)) ?_
  intro k
  apply Filter.Eventually.of_forall
  intro x z
  apply eval_scaledLift r 1 k (Q k) (by simp) (by intro j hj hjq; exact one_dvd _)
  · simp [koornwinderCoordinates]
  · rfl

/-- Generalized Case II: an arbitrary nonnegative polynomial squared scale,
with an even inner measure. -/
noncomputable def sqrtScaleKoornwinderSystem (a : ℝ[X]) (μ : Measure {x : ℝ | 0 ≤ a.eval (x : ℝ)}) (ν : Measure ℝ)
    [ν.IsNegInvariant] (ha0 : a ≠ 0)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hμpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν) :
    KoornwinderSystem a (fun x : {x : ℝ | 0 ≤ a.eval x} => Real.sqrt (a.eval (x : ℝ))) μ ν := by
  choose Q hQ hQl hQn using exists_positive_orthonormal_sequence ν hν hνpos
  refine koornwinderSystemOfLift a (fun x : {x : ℝ | 0 ≤ a.eval x} => Real.sqrt (a.eval (x : ℝ))) μ ν hμ hμpos ha0 (Filter.Eventually.of_forall (fun x => x.property))
    Q hQ hQl (fun k => by simpa only [Polynomial.integralInner_self] using hQn k)
    (fun k => scaledLift a 2 k (Q k)) ?_
  intro k
  apply Filter.Eventually.of_forall
  intro x z
  have hx := x.property
  refine eval_scaledLift a 2 k (Q k) (by simp) ?_ _ _ _ ?_ ?_
  · intro j hj hjq
    have hp : j % 2 = k % 2 := by
      by_contra hn
      exact hjq (hQ.coeff_eq_zero_of_parity hν hνpos k j hn)
    change 2 ∣ k-j
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · simpa only [koornwinderCoordinates, Matrix.cons_val_zero, PNat.val_ofNat] using (Real.sq_sqrt hx).symm
  · rfl

/-- Affine polynomial scales satisfy the ordinary lift-degree bound. -/
theorem totalDegree_polynomialScaleKoornwinderSystem_lift
    (r : ℝ[X]) (μ : Measure D) (ν : Measure ℝ) (hr : r ≠ 0)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hμpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (hdeg : r.natDegree ≤ 1) (k : ℕ) :
    ((polynomialScaleKoornwinderSystem r μ ν hr hμ hμpos hν hνpos).lift k).totalDegree ≤ k := by
  apply totalDegree_scaledLift_le
  exact hdeg

/-- Quadratic squared scales satisfy the ordinary lift-degree bound. -/
theorem totalDegree_sqrtScaleKoornwinderSystem_lift
    (a : ℝ[X]) (μ : Measure {x : ℝ | 0 ≤ a.eval (x : ℝ)}) (ν : Measure ℝ) [ν.IsNegInvariant]
    (ha0 : a ≠ 0)
    (hμ : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ)) (hμpos : Polynomial.HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (hdeg : a.natDegree ≤ 2) (k : ℕ) :
    ((sqrtScaleKoornwinderSystem a μ ν ha0 hμ hμpos hν hνpos).lift k).totalDegree ≤ k := by
  apply totalDegree_scaledLift_le
  exact hdeg

end MvPolynomial
