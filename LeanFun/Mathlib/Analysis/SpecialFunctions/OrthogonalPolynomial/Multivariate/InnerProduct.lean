/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Tactic.PolynomialIntegrability

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial inner products from measures

The assumptions impose no restriction on the support of the measure.
The inner product core is a construction, not a global instance on polynomials.

References: Dunkl–Xu, Chapter 3, https://dlmf.nist.gov/18.2; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

@[expose] public section

open MeasureTheory

namespace MvPolynomial

variable {σ : Type*}

/-- Finite polynomial moments, expressed as square integrability of all polynomials
(Dunkl–Xu, Chapter 3). -/
def HasFiniteMoments (μ : Measure (σ → ℝ)) : Prop :=
  ∀ p : MvPolynomial σ ℝ, Integrable (fun x => eval x p ^ 2) μ

/-- Strict positivity of the polynomial integral pairing, without a support restriction
(Dunkl–Xu, Chapter 3). -/
structure HasPositiveDefiniteIntegral (μ : Measure (σ → ℝ)) : Prop where
  /-- Every polynomial square has a classical finite integral. -/
  moments : HasFiniteMoments μ
  /-- Nonzero polynomial squares have strictly positive integrals. -/
  positive : ∀ p : MvPolynomial σ ℝ, p ≠ 0 → 0 < ∫ x, eval x p ^ 2 ∂μ

instance : CoeFun (HasPositiveDefiniteIntegral μ)
    (fun _ ↦ ∀ p : MvPolynomial σ ℝ, p ≠ 0 → 0 < ∫ x, eval x p ^ 2 ∂μ) :=
  ⟨fun h ↦ h.positive⟩

/-- Internal bridge: a strictly positive integral certifies its integrability. -/
theorem HasPositiveDefiniteIntegral.of_positive {μ : Measure (σ → ℝ)}
    (h : ∀ p : MvPolynomial σ ℝ, p ≠ 0 → 0 < ∫ x, eval x p ^ 2 ∂μ) :
    HasPositiveDefiniteIntegral μ := by
  refine ⟨?_, h⟩
  intro p
  by_cases hp : p = 0
  · simp [hp]
  · exact Integrable.of_integral_ne_zero (h p hp).ne' 

/-- Finite polynomial moments make all polynomial products integrable
(Dunkl–Xu, Chapter 3). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.integrable_mul [Fintype σ] {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ)
    (p q : MvPolynomial σ ℝ) : Integrable (fun x => eval x p * eval x q) μ := by
  have hp : MemLp (fun x => eval x p) 2 μ :=
    (memLp_two_iff_integrable_sq p.continuous_eval.aestronglyMeasurable).2 (hμ p)
  have hq : MemLp (fun x => eval x q) 2 μ :=
    (memLp_two_iff_integrable_sq q.continuous_eval.aestronglyMeasurable).2 (hμ q)
  exact hp.integrable_mul hq

/-- In particular the measure has finite mass (Dunkl–Xu, Chapter 3). -/
theorem HasFiniteMoments.isFiniteMeasure {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ) :
    IsFiniteMeasure μ := by
  apply (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
  simpa using hμ 1

/-- Positive square integrals are genuine finite integrals. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasPositiveDefiniteIntegral.hasFiniteMoments {μ : Measure (σ → ℝ)}
    (hpos : HasPositiveDefiniteIntegral μ) : HasFiniteMoments μ :=
  hpos.moments

/-- The positive integral value is certified together with finite moments. -/
theorem HasPositiveDefiniteIntegral.integral_sq_pos {μ : Measure (σ → ℝ)}
    (hpos : HasPositiveDefiniteIntegral μ) (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    0 < ∫ x, eval x p ^ 2 ∂μ := hpos.positive p hp

/-- A polynomial pair whose product has a finite integral (Dunkl–Xu, Chapter 3).
No moment condition is imposed on other polynomials. -/
structure IntegrablePair (μ : Measure (σ → ℝ)) where
  left : MvPolynomial σ ℝ
  right : MvPolynomial σ ℝ
  integrable : Integrable (fun x => eval x left * eval x right) μ

/-- Finite moments supply every polynomial pair (Dunkl–Xu, Chapter 3). -/
abbrev HasFiniteMoments.pair [Fintype σ] {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ)
    (p q : MvPolynomial σ ℝ) : IntegrablePair μ := ⟨p, q, hμ.integrable_mul p q⟩

/-- Construct an integrable pair from the available integrability evidence.
The automatically filled argument is a proof, never a default integral value. -/
abbrev IntegrablePair.of (μ : Measure (σ → ℝ)) (p q : MvPolynomial σ ℝ)
    (h : Integrable (fun x => eval x p * eval x q) μ := by
      first
      | solve_by_elim (maxDepth := 4) [MvPolynomial.HasFiniteMoments.integrable_mul]
      | exact MvPolynomial.HasFiniteMoments.integrable_mul
          (MvPolynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)) _ _
      | (simp only [← pow_two]; assumption)
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    IntegrablePair μ := ⟨p, q, h⟩

/-- The finite integral of a bundled polynomial pair (Dunkl–Xu, Chapter 3). -/
noncomputable def integralInner (μ : Measure (σ → ℝ)) (pq : IntegrablePair μ) : ℝ :=
  ∫ x, eval x pq.left * eval x pq.right ∂μ

/-- The pairing is exactly the integral of its integrable product. -/
theorem integralInner_eq_integral (μ : Measure (σ → ℝ)) (pq : IntegrablePair μ) :
    integralInner μ pq = ∫ x, eval x pq.left * eval x pq.right ∂μ := rfl

/-- Symmetry of the polynomial pairing (Dunkl–Xu, Chapter 3). -/
theorem integralInner_comm (μ : Measure (σ → ℝ)) (p q : MvPolynomial σ ℝ)
    {h : Integrable (fun x => eval x p * eval x q) μ} :
    integralInner μ (IntegrablePair.of μ p q) = integralInner μ (IntegrablePair.of μ q p (h := by simpa only [mul_comm] using h)) := by
  simp only [integralInner, mul_comm]

/-- The diagonal pairing is the integral of a square (Dunkl–Xu, Chapter 3). -/
theorem integralInner_self (μ : Measure (σ → ℝ)) (p : MvPolynomial σ ℝ)
    {h : Integrable (fun x => eval x p * eval x p) μ} :
    integralInner μ (IntegrablePair.of μ p p) = ∫ x, eval x p ^ 2 ∂μ := by
  simp only [integralInner, pow_two]

/-- Additivity of the integral pairing (Dunkl–Xu, Chapter 3). -/
theorem integralInner_add_left [Fintype σ] {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ)
    (p q r : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ (p + q) r) = integralInner μ (IntegrablePair.of μ p r) + integralInner μ (IntegrablePair.of μ q r) := by
  simp only [integralInner, map_add, add_mul]
  exact integral_add (hμ.integrable_mul p r) (hμ.integrable_mul q r)

/-- Scalar linearity of the integral pairing (Dunkl–Xu, Chapter 3). -/
theorem integralInner_smul_left (μ : Measure (σ → ℝ)) (p q : MvPolynomial σ ℝ) (a : ℝ)
    {h : Integrable (fun x => eval x p * eval x q) μ} :
    integralInner μ (IntegrablePair.of μ (a • p) q (h := by simpa only [smul_eq_C_mul, map_mul, eval_C, mul_assoc] using h.const_mul a)) = a * integralInner μ (IntegrablePair.of μ p q) := by
  simp only [integralInner, smul_eq_C_mul, map_mul, eval_C, mul_assoc, integral_const_mul]

/-- Pairing with zero vanishes (Dunkl–Xu, Chapter 3). -/
@[simp] theorem integralInner_zero_left (μ : Measure (σ → ℝ)) (p : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ 0 p (h := by simp)) = 0 := by simp [integralInner]

/-- Subtraction in the first slot (Dunkl–Xu, Chapter 3). -/
theorem integralInner_sub_left [Fintype σ] {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ)
    (p q r : MvPolynomial σ ℝ) :
    integralInner μ (IntegrablePair.of μ (p - q) r) = integralInner μ (IntegrablePair.of μ p r) - integralInner μ (IntegrablePair.of μ q r) := by
  simp only [integralInner, map_sub, sub_mul]
  exact integral_sub (hμ.integrable_mul p r) (hμ.integrable_mul q r)

/-- Vanishing of a squared norm forces the polynomial to vanish
(Dunkl–Xu, Chapter 3). -/
theorem HasPositiveDefiniteIntegral.eq_zero_of_integralInner_self_eq_zero {μ : Measure (σ → ℝ)}
    (hμ : HasPositiveDefiniteIntegral μ) {p : MvPolynomial σ ℝ}
    {h : Integrable (fun x => eval x p * eval x p) μ} (hp : integralInner μ (IntegrablePair.of μ p p) = 0) : p = 0 := by
  by_contra hpne
  have := hμ p hpne
  rw [← integralInner_self μ p (h := h), hp] at this
  exact (lt_irrefl _ this)

/-- The polynomial integral pairing defines an inner product core under the agreed
moment and positivity hypotheses (Dunkl–Xu, Chapter 3).
Install the resulting norm and inner product only locally, since they depend on `μ`. -/
@[instance_reducible]
noncomputable def integralInnerProductCore [Fintype σ] (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) : InnerProductSpace.Core ℝ (MvPolynomial σ ℝ) where
  inner := fun p q => integralInner μ (hμ.pair p q)
  conj_inner_symm p q := by simpa using integralInner_comm μ q p (h := hμ.integrable_mul q p)
  re_inner_nonneg p := by
    change 0 ≤ integralInner μ (IntegrablePair.of μ p p)
    rw [integralInner_self]
    exact integral_nonneg (fun _ => sq_nonneg _)
  add_left := integralInner_add_left hμ
  smul_left p q a := by simpa using integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)
  definite _ hp := hpos.eq_zero_of_integralInner_self_eq_zero hp

/-- Moving a polynomial multiplier across the pairing preserves integrability. -/
theorem integralInner_mul_left_right (μ : Measure (σ → ℝ))
    (u p q : MvPolynomial σ ℝ)
    {h : Integrable (fun x => eval x (u * p) * eval x q) μ} :
    integralInner μ (IntegrablePair.of μ (u * p) q) =
      integralInner μ (IntegrablePair.of μ p (u * q) (h := by
        convert h using 1
        ext x
        simp only [map_mul]
        ring)) := by
  unfold integralInner
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul]
  ring

/-- The polynomial integral pairing as a bilinear form, using only finite moments. -/
noncomputable def integralBilinForm {σ : Type*} [Fintype σ]
    (μ : Measure (σ → ℝ)) (hμ : HasFiniteMoments μ) :
    LinearMap.BilinForm ℝ (MvPolynomial σ ℝ) where
  toFun p :=
    { toFun := fun q => integralInner μ (hμ.pair p q)
      map_add' := fun q r => by
        rw [integralInner_comm μ p (q + r), integralInner_add_left hμ,
          integralInner_comm μ q p, integralInner_comm μ r p]
      map_smul' := fun a q => by
        rw [integralInner_comm μ p (a • q), integralInner_smul_left,
          integralInner_comm μ q p]
        all_goals first | rfl | exact hμ.integrable_mul _ _ }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    exact integralInner_add_left hμ p q r
  map_smul' a p := by
    apply LinearMap.ext
    intro q
    exact integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)

end MvPolynomial
