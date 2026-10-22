/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Completeness
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The classical domain of a normalized polynomial coefficient
The polynomial has finite positive squared norm, and the coefficient integrand
is integrable. These are index-local conditions, independent of completeness
or of the existence of moments for other polynomials. Reference: DLMF 18.2(viii).
-/

@[expose] public noncomputable section
open MeasureTheory
namespace Polynomial

/-- Data with an integrable coefficient product and finite positive normalization
for a specified polynomial (DLMF 18.2(viii)). -/
structure IntegralCoefficientInput (𝕂 : Type*) [RCLike 𝕂] (μ : Measure ℝ) (p : ℝ[X]) where
  val : ℝ → 𝕂
  square_integrable : Integrable (fun x ↦ p.eval x ^ 2) μ
  norm_pos : 0 < ∫ x, p.eval x ^ 2 ∂μ
  integrable : Integrable (fun x ↦ val x * ((p.eval x : ℝ) : 𝕂)) μ

/-- The normalization is a genuine finite positive integral. -/
theorem IntegralCoefficientInput.normalization {𝕂 : Type*} [RCLike 𝕂]
    {μ : Measure ℝ} {p : ℝ[X]} (f : IntegralCoefficientInput 𝕂 μ p) :
    Integrable (fun x ↦ p.eval x ^ 2) μ ∧ 0 < ∫ x, p.eval x ^ 2 ∂μ :=
  ⟨f.square_integrable, f.norm_pos⟩

/-- L2 inputs give classical coefficient products for every polynomial when
all moments are finite (DLMF 18.2(viii)). -/
theorem integrable_L2_mul_eval {𝕂 : Type*} [RCLike 𝕂] {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (p : ℝ[X]) (f : Lp 𝕂 2 μ) :
    Integrable (fun x ↦ f x * ((p.eval x : ℝ) : 𝕂)) μ := by
  have hp : MemLp (fun x ↦ ((p.eval x : ℝ) : 𝕂)) 2 μ :=
    (memLp_eval_of_hasFiniteMoments hμ p).ofReal
  exact (Lp.memLp f).integrable_mul hp

/-- L2 data construct a coefficient input under the usual moment and positivity
hypotheses, for any nonzero polynomial (DLMF 18.2(viii)). -/
def IntegralCoefficientInput.ofL2 {𝕂 : Type*} [RCLike 𝕂] {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (p : ℝ[X]) (hp : p ≠ 0) (f : Lp 𝕂 2 μ) : IntegralCoefficientInput 𝕂 μ p where
  val := f
  square_integrable := hμ p
  norm_pos := hpos p hp
  integrable := integrable_L2_mul_eval hμ p f

/-- Constructors preserve the pointwise representative of the L2 data. -/
@[simp] theorem IntegralCoefficientInput.ofL2_val {𝕂 : Type*} [RCLike 𝕂] {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (p : ℝ[X]) (hp : p ≠ 0) (f : Lp 𝕂 2 μ) :
    (ofL2 hμ hpos p hp f).val = f := rfl

/-- Polynomial data supply real coefficient inputs under finite moments and
positive definiteness (DLMF 18.2(viii)). -/
def IntegralCoefficientInput.ofPolynomial {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (p : ℝ[X]) (hp : p ≠ 0) (q : ℝ[X]) : IntegralCoefficientInput ℝ μ p where
  val := fun x ↦ q.eval x
  square_integrable := hμ p
  norm_pos := hpos p hp
  integrable := by simpa using hμ.integrable_mul q p

/-- The polynomial constructor preserves polynomial evaluation. -/
@[simp] theorem IntegralCoefficientInput.ofPolynomial_val {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (p : ℝ[X]) (hp : p ≠ 0) (q : ℝ[X]) :
    (ofPolynomial hμ hpos p hp q).val = fun x ↦ q.eval x := rfl

/-- Scalar extension of real coefficient data preserves the classical domain. -/
def IntegralCoefficientInput.ofReal {μ : Measure ℝ} {p : ℝ[X]}
    (f : IntegralCoefficientInput ℝ μ p) : IntegralCoefficientInput ℂ μ p where
  val := fun x ↦ (f.val x : ℂ)
  square_integrable := f.square_integrable
  norm_pos := f.norm_pos
  integrable := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id,
      id_eq, Complex.ofReal_mul] using (f.integrable.ofReal (𝕜 := ℂ))

/-- Real embedding preserves pointwise values. -/
@[simp] theorem IntegralCoefficientInput.ofReal_val {μ : Measure ℝ} {p : ℝ[X]}
    (f : IntegralCoefficientInput ℝ μ p) :
    f.ofReal.val = fun x ↦ (f.val x : ℂ) := rfl

/-- One common function with classical coefficient data through a finite cutoff.
No conditions are imposed on higher indices (DLMF 18.2(viii)). -/
structure IntegralCoefficientFamilyInput (𝕂 : Type*) [RCLike 𝕂] (μ : Measure ℝ)
    (P : ℕ → ℝ[X]) (N : ℕ) where
  val : ℝ → 𝕂
  square_integrable : ∀ i : Fin (N + 1), Integrable (fun x ↦ (P i).eval x ^ 2) μ
  norm_pos : ∀ i : Fin (N + 1), 0 < ∫ x, (P i).eval x ^ 2 ∂μ
  integrable : ∀ i : Fin (N + 1), Integrable (fun x ↦ val x * (((P i).eval x : ℝ) : 𝕂)) μ

/-- Extract one of the finite input family's coefficients. -/
def IntegralCoefficientFamilyInput.at {𝕂 : Type*} [RCLike 𝕂] {μ : Measure ℝ}
    {P : ℕ → ℝ[X]} {N : ℕ} (f : IntegralCoefficientFamilyInput 𝕂 μ P N)
    (i : Fin (N + 1)) : IntegralCoefficientInput 𝕂 μ (P i) where
  val := f.val
  square_integrable := f.square_integrable i
  norm_pos := f.norm_pos i
  integrable := f.integrable i

/-- L2 data supply finite coefficient families under the explicit usual measure
hypotheses (DLMF 18.2(viii)). -/
def IntegralCoefficientFamilyInput.ofL2 {𝕂 : Type*} [RCLike 𝕂] {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (f : Lp 𝕂 2 μ) (N : ℕ) : IntegralCoefficientFamilyInput 𝕂 μ P N where
  val := f
  square_integrable := fun i ↦ hμ (P i)
  norm_pos := fun i ↦ hpos (P i) (P.ne_zero i)
  integrable := fun i ↦ integrable_L2_mul_eval hμ (P i) f

/-- Every selected coefficient uses the same pointwise function. -/
@[simp] theorem IntegralCoefficientFamilyInput.at_val {𝕂 : Type*} [RCLike 𝕂]
    {μ : Measure ℝ} {P : ℕ → ℝ[X]} {N : ℕ}
    (f : IntegralCoefficientFamilyInput 𝕂 μ P N) (i : Fin (N + 1)) :
    (f.at i).val = f.val := rfl

/-- The L2 finite-family constructor preserves the pointwise representative. -/
@[simp] theorem IntegralCoefficientFamilyInput.ofL2_val {𝕂 : Type*} [RCLike 𝕂]
    {μ : Measure ℝ} (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (f : Lp 𝕂 2 μ) (N : ℕ) :
    (ofL2 hμ hpos P f N).val = f := rfl

/-- Selecting a coefficient commutes with constructing the finite L2 family. -/
@[simp] theorem IntegralCoefficientFamilyInput.ofL2_at {𝕂 : Type*} [RCLike 𝕂]
    {μ : Measure ℝ} (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (f : Lp 𝕂 2 μ) (N : ℕ) (i : Fin (N + 1)) :
    (ofL2 hμ hpos P f N).at i = IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f := rfl

end Polynomial
