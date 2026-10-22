/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Approximation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real orthogonal polynomials in real or complex L²

Scalar extension reuses the real polynomial family and its normalization. It
introduces no second definition of any classical family.
Reference: DLMF 18.2(viii), orthogonal expansions of complex-valued functions.
-/

public section
open MeasureTheory Real
open scoped InnerProductSpace
variable (𝕂 : Type*) [RCLike 𝕂] {μ : Measure ℝ}

/-- Extending real-valued L² classes preserves their inner products. -/
theorem inner_ofReal_compLp (f g : Lp ℝ 2 μ) :
    inner 𝕂 ((@RCLike.ofRealCLM 𝕂 _).compLp f) ((@RCLike.ofRealCLM 𝕂 _).compLp g) =
      (inner ℝ f g : 𝕂) := by
  rw [L2.inner_def, L2.inner_def, ← integral_ofReal]
  apply integral_congr_ae
  filter_upwards [(@RCLike.ofRealCLM 𝕂 _).coeFn_compLp f,
    (@RCLike.ofRealCLM 𝕂 _).coeFn_compLp g] with x hf hg
  simp [hf, hg, RCLike.inner_apply]

/-- Scalar extension preserves the L² norm. -/
theorem norm_ofReal_compLp (f : Lp ℝ 2 μ) :
    ‖(@RCLike.ofRealCLM 𝕂 _).compLp f‖ = ‖f‖ := by
  have h := congrArg RCLike.re (inner_ofReal_compLp 𝕂 f f)
  rw [← norm_sq_eq_re_inner, RCLike.ofReal_re, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg ((@RCLike.ofRealCLM 𝕂 _).compLp f), norm_nonneg f]

namespace Polynomial
variable (hμ : HasFiniteMoments μ)

/-- Real polynomial evaluation as a real-linear map into real or complex L². -/
@[expose] noncomputable def polynomialToL2Scalar : ℝ[X] →ₗ[ℝ] Lp 𝕂 2 μ :=
  ((@RCLike.ofRealCLM 𝕂 _).compLpₗ 2 μ).comp (polynomialToL2 hμ)

/-- An almost-everywhere representative of scalar-extended polynomial evaluation. -/
theorem coe_polynomialToL2Scalar (p : ℝ[X]) :
    polynomialToL2Scalar 𝕂 hμ p =ᵐ[μ] fun x ↦ ((p.eval x : ℝ) : 𝕂) := by
  filter_upwards [(@RCLike.ofRealCLM 𝕂 _).coeFn_compLp (polynomialToL2 hμ p),
    coe_polynomialToL2 hμ p] with x hx hp
  simpa only [polynomialToL2Scalar, LinearMap.comp_apply, ContinuousLinearMap.compLpₗ_apply,
    RCLike.ofRealCLM_apply, hp] using hx

/-- The scalar-extended polynomial inner product with arbitrary L² data is
its integral pairing with the real polynomial. -/
theorem inner_polynomialToL2Scalar_left (p : ℝ[X]) (f : Lp 𝕂 2 μ) :
    inner 𝕂 (polynomialToL2Scalar 𝕂 hμ p) f = ∫ x, f x * ((p.eval x : ℝ) : 𝕂) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2Scalar 𝕂 hμ p] with x hp
  simp [hp, RCLike.inner_apply]

namespace Sequence
variable (P : Sequence ℝ)

/-- Scalar extension of the existing normalized real polynomial vectors. -/
@[expose] noncomputable def normalizedToL2Scalar (n : {n : ℕ // 0 < P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)}) : Lp 𝕂 2 μ :=
  (@RCLike.ofRealCLM 𝕂 _).compLp (P.normalizedToL2 hμ n)

/-- Scalar extension retains the original square-root normalization. -/
theorem normalizedToL2Scalar_eq (n : {n : ℕ // 0 < P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)}) :
    P.normalizedToL2Scalar 𝕂 hμ n =
      (((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ : ℝ) : 𝕂) • polynomialToL2Scalar 𝕂 hμ (P n) := by
  change ((@RCLike.ofRealCLM 𝕂 _).compLpₗ 2 μ)
    ((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ • polynomialToL2 hμ (P n)) = _
  rw [map_smul, RCLike.real_smul_eq_coe_smul (K := 𝕂)]
  rfl

variable {P}

/-- Real orthogonal polynomial normalization remains orthonormal after scalar extension. -/
theorem IsOrthogonal.orthonormal_normalizedToL2Scalar (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) : Orthonormal 𝕂 (fun n ↦ P.normalizedToL2Scalar 𝕂 hμ ⟨n, squaredNorm_pos hpos P n⟩) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [normalizedToL2Scalar, normalizedToL2Scalar, inner_ofReal_compLp,
    orthonormal_iff_ite.mp (hP.orthonormal_normalizedToL2 hμ hpos)]
  split_ifs <;> simp

/-- Scalar-extended polynomial classes of degree at most N belong to the first
N+1 normalized vectors over the enlarged scalar field. -/
theorem polynomialToL2Scalar_mem_span (hpos : HasPositiveDefiniteIntegral μ)
    (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N) :
    polynomialToL2Scalar 𝕂 hμ p ∈ Submodule.span 𝕂
      ((fun n ↦ P.normalizedToL2Scalar 𝕂 hμ ⟨n, squaredNorm_pos hpos P n⟩) '' (Finset.range (N + 1) : Set ℕ)) := by
  have hs := polynomialToL2_mem_span_normalizedToL2 (P := P) hμ hpos N p hp
  clear hp
  change ((@RCLike.ofRealCLM 𝕂 _).compLpₗ 2 μ) (polynomialToL2 hμ p) ∈ _
  generalize polynomialToL2 hμ p = v at hs ⊢
  induction hs using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    exact Submodule.subset_span (Set.mem_image_of_mem _ hi)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add u v _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
  | smul c u _ hu =>
    rw [map_smul, RCLike.real_smul_eq_coe_smul (K := 𝕂)]
    exact Submodule.smul_mem _ _ hu

end Sequence
end Polynomial
