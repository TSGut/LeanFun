/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Hierarchy
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.FiniteCoordinates

/-! # Padded finite semiclassical hierarchy identities

Reference: Papadopoulos–Gutleb–Slevinsky–Olver, §§3.2 and 3.5.
-/

@[expose] public section
open MeasureTheory Module
namespace Polynomial
variable {t α β : ℝ} (ht : 1 < t) (hα : -1 < α) (hβ : -1 < β)

/-- Finite expansion of a polynomial in semiclassical coordinates. -/
theorem semiclassicalJacobi_repr_map_sum (γ : ℝ) (b : Basis ℕ ℝ ℝ[X])
    (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (p : ℝ[X]) (N : ℕ) (hp : p.natDegree < N) (i : ℕ) :
    b.repr (L p) i = ∑ k : Fin N,
      b.repr (L (semiclassicalJacobiSequence ht hα hβ γ k)) i *
        (semiclassicalJacobiBasis ht hα hβ γ).repr p k :=
  (semiclassicalJacobiSequence_spec ht hα hβ γ).1.repr_map_sum
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ) _ b L p N hp i

/-- Finite Parseval identity for semiclassical polynomials. -/
theorem semiclassicalJacobi_integralInner_eq_sum (γ : ℝ) (p q : ℝ[X])
    (N : ℕ) (hp : p.natDegree < N) :
    integralInner (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ)
      (IntegrablePair.of _ p q) = ∑ k : Fin N,
      (semiclassicalJacobiBasis ht hα hβ γ).repr p k *
      (semiclassicalJacobiBasis ht hα hβ γ).repr q k :=
  (semiclassicalJacobiSequence_spec ht hα hβ γ).1.integralInner_eq_sum_repr
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ) _
    (fun n ↦ by rw [integralInner_self]; exact
      (semiclassicalJacobiSequence_spec ht hα hβ γ).2.2 n) p q N hp

/-- Multiplication pairings use a finite Jacobi section when both inputs fit. -/
theorem semiclassicalJacobi_integralInner_mul_eq_sum (γ : ℝ) (p q u : ℝ[X])
    (N : ℕ) (hp : p.natDegree < N) (hq : q.natDegree < N) :
    integralInner (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ)
      (IntegrablePair.of _ p (u*q)) = ∑ i : Fin N, ∑ j : Fin N,
      (semiclassicalJacobiBasis ht hα hβ γ).repr p i *
      (semiclassicalJacobiBasis ht hα hβ γ).repr (u*semiclassicalJacobiSequence ht hα hβ γ j) i *
      (semiclassicalJacobiBasis ht hα hβ γ).repr q j :=
  (semiclassicalJacobiSequence_spec ht hα hβ γ).1.integralInner_mul_eq_sum_repr
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ) _
    (fun n ↦ by rw [integralInner_self]; exact
      (semiclassicalJacobiSequence_spec ht hα hβ γ).2.2 n) p q u N hp hq

/-- The connection intertwines multiplication, with one extra intermediate mode.
The right product needs no extra mode because conversion does not raise degree. -/
theorem semiclassicalJacobi_padded_intertwining (γ γ' : ℝ) (N : ℕ) :
    (Matrix.of (fun i : Fin N ↦ fun k : Fin (N+1) ↦
      semiclassicalJacobiConnection ht hα hβ γ hα hβ γ' i k)) *
      (Matrix.of (fun k : Fin (N+1) ↦ fun j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ γ k j)) =
    (Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ γ' i j)) *
      (Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiConnection ht hα hβ γ hα hβ γ' i j)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, semiclassicalJacobiConnection, semiclassicalJacobiMatrix,
    Basis.toMatrix_apply, semiclassicalJacobiBasis_apply]
  have hleft := semiclassicalJacobi_repr_map_sum ht hα hβ γ
    (semiclassicalJacobiBasis ht hα hβ γ') LinearMap.id
    (X * semiclassicalJacobiSequence ht hα hβ γ j) (N+1)
    (by have := natDegree_mul_le (p := (X : ℝ[X])) (q := semiclassicalJacobiSequence ht hα hβ γ j)
        simp only [natDegree_X, Sequence.natDegree_eq] at this
        omega) i
  have hright := semiclassicalJacobi_repr_map_sum ht hα hβ γ'
    (semiclassicalJacobiBasis ht hα hβ γ') (LinearMap.mulLeft ℝ X)
    (semiclassicalJacobiSequence ht hα hβ γ j) N (by simp) i
  simp only [LinearMap.id_apply, LinearMap.mulLeft_apply] at hleft hright
  exact hleft.symm.trans hright

/-- The padded intertwining identity gives the Jacobi update using a genuine
finite inverse. The inverse is specified by both inverse equations. -/
theorem semiclassicalJacobi_padded_update (γ : ℝ) (c N : ℕ) :
    ∃ S : Matrix (Fin N) (Fin N) ℝ,
      semiclassicalJacobiRaisingSection ht hα hβ γ c N * S = 1 ∧
      S * semiclassicalJacobiRaisingSection ht hα hβ γ c N = 1 ∧
      Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiMatrix ht hα hβ (γ+c) i j) =
        (Matrix.of (fun i : Fin N ↦ fun k : Fin (N+1) ↦
          semiclassicalJacobiConnection ht hα hβ γ hα hβ (γ+c) i k)) *
        (Matrix.of (fun k : Fin (N+1) ↦ fun j : Fin N ↦
          semiclassicalJacobiMatrix ht hα hβ γ k j)) * S := by
  obtain ⟨u, hu⟩ := semiclassicalJacobiRaisingSection_isUnit ht hα hβ γ c N
  refine ⟨↑u⁻¹, ?_, ?_, ?_⟩
  · rw [← hu]; exact u.mul_inv
  · rw [← hu]; exact u.inv_mul
  · rw [semiclassicalJacobi_padded_intertwining]
    change _ = _ * semiclassicalJacobiRaisingSection ht hα hβ γ c N * _
    rw [← hu, Units.mul_inv_cancel_right]


end Polynomial
