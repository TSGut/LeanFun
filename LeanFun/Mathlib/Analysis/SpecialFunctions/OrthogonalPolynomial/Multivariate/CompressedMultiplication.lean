/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Projection

/-!
# Symmetric compressed polynomial multiplication

Sandwiching multiplication between polynomial projections gives the operator
represented by a finite coordinate matrix. Its square is exact on inputs with
two multiplication degrees of padding.
Reference: Gutleb–Olver–Slevinsky, finite sections of multiplication operators.
-/

@[expose] public section
open MeasureTheory
namespace MvPolynomial
variable {σ : Type*}

/-- Multiplication compressed on both sides by a polynomial truncation. -/
noncomputable def compressedMul (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (u : MvPolynomial σ ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ :=
  T.comp ((LinearMap.mulLeft ℝ u).comp T)

/-- The explicit action of compressed multiplication. -/
theorem compressedMul_apply (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (u p : MvPolynomial σ ℝ) : compressedMul T u p = T (u*T p) := rfl

/-- Symmetric compression preserves symmetry of polynomial multiplication. -/
theorem compressedMul_symmetric (μ : Measure (σ → ℝ))
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hi : ∀ p q, Integrable (fun x => eval x (T p) * eval x q) μ)
    (hT : ∀ p q, integralInner μ (IntegrablePair.of μ (T p) q) =
      integralInner μ (IntegrablePair.of μ p (T q)
        (h := by simpa only [mul_comm] using hi q p)))
    (u p q : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ (compressedMul T u p) q
      (h := hi _ q)) =
      integralInner μ (IntegrablePair.of μ p (compressedMul T u q)
        (h := by simpa only [compressedMul_apply, mul_comm] using hi (u*T q) p)) := by
  have hl := hT (u*T p) q
  have hr := hT p (u*T q)
  simp only [integralInner] at hl hr ⊢
  change (∫ x, eval x (T (u*T p)) * eval x q ∂μ) =
    ∫ x, eval x p * eval x (T (u*T q)) ∂μ
  rw [hl, ← hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [map_mul]; ring)

/-- The square of a compressed multiplication is also symmetric. -/
theorem compressedMul_sq_symmetric (μ : Measure (σ → ℝ))
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hi : ∀ p q, Integrable (fun x => eval x (T p) * eval x q) μ)
    (hT : ∀ p q, integralInner μ (IntegrablePair.of μ (T p) q) =
      integralInner μ (IntegrablePair.of μ p (T q)
        (h := by simpa only [mul_comm] using hi q p)))
    (u p q : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ (((compressedMul T u)^2) p) q
      (h := by
        simpa only [pow_two, Module.End.mul_apply, compressedMul_apply] using
          hi (u*T (T (u*T p))) q)) =
      integralInner μ (IntegrablePair.of μ p (((compressedMul T u)^2) q)
        (h := by
          simpa only [pow_two, Module.End.mul_apply, compressedMul_apply, mul_comm] using
            hi (u*T (T (u*T q))) p)) := by
  have h₁ := compressedMul_symmetric μ T hi hT u (compressedMul T u p) q
  have h₂ := compressedMul_symmetric μ T hi hT u p (compressedMul T u q)
  simpa only [integralInner, IntegrablePair.of, pow_two, Module.End.mul_apply] using h₁.trans h₂

/-- Two padded multiplication steps agree with the full polynomial product. -/
theorem compressedMul_sq_apply_eq (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (N : ℕ) (hT : ∀ p, p.totalDegree ≤ N → T p=p)
    (u p : MvPolynomial σ ℝ) (hp : p.totalDegree+2*u.totalDegree ≤ N) :
    ((compressedMul T u)^2) p = u^2*p := by
  have hp' : p.totalDegree ≤ N := by omega
  have hup : (u*p).totalDegree ≤ N := (totalDegree_mul _ _).trans (by omega)
  have huup : (u*(u*p)).totalDegree ≤ N := by
    have h₁ := totalDegree_mul u (u*p)
    have h₂ := totalDegree_mul u p
    omega
  rw [pow_two]
  change T (u*T (T (u*T p))) = u^2*p
  rw [hT p hp',hT (u*p) hup,hT (u*p) hup,hT (u*(u*p)) huup]
  ring

end MvPolynomial
