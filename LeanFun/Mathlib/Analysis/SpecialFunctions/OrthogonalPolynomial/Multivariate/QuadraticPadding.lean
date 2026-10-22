/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.CompressedMultiplication

/-!
# Two extra degree blocks suffice for quadratic-product leading sections

Each quadratic factor is built from squared compressed coordinate multipliers.
Moving one factor onto the test polynomial reduces the required padding from
four degrees to two. This is an exact leading-section result.
Reference: Gutleb–Olver–Slevinsky, finite sections and polynomial modifications.
-/

@[expose] public section
open MeasureTheory
namespace MvPolynomial

/-- A diagonal coordinate quadratic, including the factors in the disk examples. -/
noncomputable def coordinateQuadratic (a b c : ℝ) : MvPolynomial (Fin 2) ℝ :=
  C a+C b*(X 0)^2+C c*(X 1)^2

/-- The same quadratic formed from finite compressed coordinate multipliers. -/
noncomputable def compressedCoordinateQuadratic
    (T : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ) (a b c : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ :=
  a • LinearMap.id + b • (compressedMul T (X 0))^2 + c • (compressedMul T (X 1))^2

/-- A real quadratic in symmetric compressed coordinates remains symmetric. -/
theorem compressedCoordinateQuadratic_symmetric (μ : Measure (Fin 2 → ℝ))
    (hμ : HasFiniteMoments μ)
    (T : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ)
    (hT : ∀ p q, integralInner μ (IntegrablePair.of μ (T p) q) = integralInner μ (IntegrablePair.of μ p (T q)))
    (a b c : ℝ) (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner μ (IntegrablePair.of μ (compressedCoordinateQuadratic T a b c p) q) =
      integralInner μ (IntegrablePair.of μ p (compressedCoordinateQuadratic T a b c q)) := by
  have hsmul (p q : MvPolynomial (Fin 2) ℝ) (c : ℝ) :=
    integralInner_smul_left μ p q c (h := hμ.integrable_mul _ _)
  conv_rhs => rw [integralInner_comm]
  simp only [compressedCoordinateQuadratic,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.id_apply,integralInner_add_left hμ,hsmul]
  have hx := (compressedMul_sq_symmetric μ T (fun p q => hμ.integrable_mul _ _) hT (X 0) p q).trans
    (integralInner_comm μ p (((compressedMul T (X 0))^2) q))
  have hy := (compressedMul_sq_symmetric μ T (fun p q => hμ.integrable_mul _ _) hT (X 1) p q).trans
    (integralInner_comm μ p (((compressedMul T (X 1))^2) q))
  rw [hx,hy,integralInner_comm μ p q]

/-- Two degrees of padding make the compressed quadratic exact on an input. -/
theorem compressedCoordinateQuadratic_apply_eq
    (T : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (hT : ∀ p, p.totalDegree ≤ N → T p=p)
    (a b c : ℝ) (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree+2 ≤ N) :
    compressedCoordinateQuadratic T a b c p = coordinateQuadratic a b c*p := by
  simp only [compressedCoordinateQuadratic,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.id_apply,
    compressedMul_sq_apply_eq T N hT (X 0) p (by simpa using hp),
    compressedMul_sq_apply_eq T N hT (X 1) p (by simpa using hp)]
  simp only [coordinateQuadratic,MvPolynomial.smul_eq_C_mul]
  ring

/-- The leading pairing of a product of two quadratic factors needs only two
extra degrees, even though the full product has degree four. -/
theorem integralInner_compressed_quadratic_product (μ : Measure (Fin 2 → ℝ))
    (hμ : HasFiniteMoments μ)
    (T : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ)
    (hTs : ∀ p q, integralInner μ (IntegrablePair.of μ (T p) q) = integralInner μ (IntegrablePair.of μ p (T q)))
    (N : ℕ) (hT : ∀ p, p.totalDegree ≤ N+2 → T p=p)
    (a b c d e f : ℝ) (p q : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ N) (hq : q.totalDegree ≤ N) :
    integralInner μ (IntegrablePair.of μ p (compressedCoordinateQuadratic T a b c
      (compressedCoordinateQuadratic T d e f q))) =
      integralInner μ (IntegrablePair.of μ p ((coordinateQuadratic a b c*coordinateQuadratic d e f)*q)) := by
  have hs := compressedCoordinateQuadratic_symmetric μ hμ T hTs a b c p
    (compressedCoordinateQuadratic T d e f q)
  simp only [integralInner] at hs ⊢
  rw [← hs, compressedCoordinateQuadratic_apply_eq T (N+2) hT a b c p (by omega),
    compressedCoordinateQuadratic_apply_eq T (N+2) hT d e f q (by omega)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [map_mul]; ring)

end MvPolynomial
