/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergySolve
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Completeness
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # A weighted L² realization of completed radial Dirichlet energy
The energy identity realizes a polynomial p as sqrt(4/t) times (x(1-x)p)'
in L²((t-x)^(gamma+1) dx). Extending this isometry makes completed energy
vectors concrete derivative classes. This is not yet a physical H₀¹ identification.
Reference: the Dirichlet form of Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 15.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Polynomial.SemiclassicalJacobiEnergy

/-- Weighted L² space of endpoint-weighted radial derivatives. -/
abbrev DerivativeSpace (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :=
  Lp ℝ 2 (semiclassicalJacobiMeasure t 0 0 (γ + 1))

/-- Finite moments for the derivative-space measure. -/
theorem derivativeMeasure_moments (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    HasFiniteMoments (semiclassicalJacobiMeasure t 0 0 (γ + 1)) :=
  hasFiniteMoments_semiclassicalJacobiMeasure (gt_one t) (by norm_num) (by norm_num)

/-- The scaled endpoint-weighted derivative as an L² class. -/
def polynomialDerivative (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    PolynomialSpace t γ →ₗ[ℝ] DerivativeSpace t γ :=
  Real.sqrt (4 / (t : ℝ)) •
    (polynomialToL2 (derivativeMeasure_moments t γ)).comp
      (semiclassicalJacobiABWeightedDerivativeMap.comp (polynomialEquiv t γ).toLinearMap)

/-- The concrete derivative pairing equals the polynomial energy pairing. -/
theorem inner_polynomialDerivative (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (p z : PolynomialSpace t γ) :
    inner ℝ (polynomialDerivative t γ p) (polynomialDerivative t γ z) = inner ℝ p z := by
  simp only [polynomialDerivative, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, real_inner_smul_left, inner_smul_right, inner_polynomialToL2]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by have := gt_one t; positivity)]
  change (4 / (t : ℝ)) * integralInner _ (IntegrablePair.of _ _ _) =
    -integralInner _ (IntegrablePair.of _ (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ (polynomialEquiv t γ p)) (polynomialEquiv t γ z))
  rw [integralInner_semiclassicalJacobi_dirichlet (gt_one t)]
  ring

/-- Endpoint-weighted differentiation is an isometry for the energy norm. -/
def polynomialDerivativeIsometry (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    PolynomialSpace t γ →ₗᵢ[ℝ] DerivativeSpace t γ where
  __ := polynomialDerivative t γ
  norm_map' p := by
    have h := inner_polynomialDerivative t γ p p
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (polynomialDerivative t γ p), norm_nonneg p]

/-- The completed energy space embeds isometrically into concrete weighted L² derivatives. -/
def derivativeRealization (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    Space t γ →ₗᵢ[ℝ] DerivativeSpace t γ := (polynomialDerivativeIsometry t γ).fromCompletion

/-- The completed realization has the prescribed value on polynomial vectors. -/
theorem derivativeRealization_embed (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (p : PolynomialSpace t γ) :
    derivativeRealization t γ (embed t γ p) = polynomialDerivative t γ p :=
  (polynomialDerivativeIsometry t γ).fromCompletion_apply_coe p

/-- The realization is faithful: no two completed energy vectors have the same derivative class. -/
theorem derivativeRealization_injective (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    Function.Injective (derivativeRealization t γ) := (derivativeRealization t γ).injective

/-- The derivative classes arising from completed energy vectors form a closed subspace. -/
theorem isClosed_range_derivativeRealization (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    IsClosed (Set.range (derivativeRealization t γ)) :=
  (derivativeRealization t γ).isometry.isClosedEmbedding.isClosed_range

/-- The realized space is exactly the L² closure of the scaled polynomial derivatives. -/
theorem range_derivativeRealization (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    Set.range (derivativeRealization t γ) = closure (Set.range (polynomialDerivative t γ)) := by
  have he : derivativeRealization t γ '' Set.range (embed t γ) =
      Set.range (polynomialDerivative t γ) := by
    rw [← Set.range_comp]
    congr 1
    funext p
    exact derivativeRealization_embed t γ p
  apply Set.Subset.antisymm
  · have h := (derivativeRealization t γ).continuous.range_subset_closure_image_dense
      (denseRange_embed t γ)
    rwa [he] at h
  · apply closure_minimal _ (isClosed_range_derivativeRealization t γ)
    rintro y ⟨p, rfl⟩
    exact ⟨embed t γ p, derivativeRealization_embed t γ p⟩

/-- The realization preserves the completed energy inner product. -/
theorem inner_derivativeRealization (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (x y : Space t γ) :
    inner ℝ (derivativeRealization t γ x) (derivativeRealization t γ y) = inner ℝ x y :=
  (derivativeRealization t γ).inner_map_map x y

/-- Square-integrable derivative data define a continuous load on the energy completion. -/
def derivativeLoad (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (g : DerivativeSpace t γ) :
    Space t γ →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (DerivativeSpace t γ) g).comp
    (derivativeRealization t γ).toContinuousLinearMap

/-- The derivative-data load is the concrete weighted L² pairing. -/
theorem derivativeLoad_apply (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (g : DerivativeSpace t γ) (x : Space t γ) :
    derivativeLoad t γ g x = inner ℝ g (derivativeRealization t γ x) := rfl

/-- The derivative-data load is bounded by the L² norm of its data. -/
theorem norm_derivativeLoad_le (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (g : DerivativeSpace t γ) :
    ‖derivativeLoad t γ g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro x
  rw [derivativeLoad_apply]
  exact (norm_inner_le_norm g _).trans_eq (by rw [(derivativeRealization t γ).norm_map])

/-- The finite solves are uniformly bounded for every square-integrable derivative datum. -/
theorem norm_coefficients_derivativeLoad_le (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (g : DerivativeSpace t γ) :
    ‖trialEmbed t γ N (coefficients t γ N (derivativeLoad t γ g))‖ ≤ ‖g‖ :=
  (norm_trialEmbed_coefficients_le t γ N _).trans (norm_derivativeLoad_le t γ g)

/-- The finite coefficient solves converge as concrete weighted L² derivative classes. -/
theorem tendsto_derivativeRealization_coefficients (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (ℓ : Space t γ →L[ℝ] ℝ) :
    Tendsto (fun N ↦ derivativeRealization t γ
      (trialEmbed t γ N (coefficients t γ N ℓ))) atTop
        (𝓝 (derivativeRealization t γ (solution t γ ℓ))) :=
  (derivativeRealization t γ).continuous.tendsto _ |>.comp (tendsto_trialEmbed_coefficients t γ ℓ)

end Polynomial.SemiclassicalJacobiEnergy
