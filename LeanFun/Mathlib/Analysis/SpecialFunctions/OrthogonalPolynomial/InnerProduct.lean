/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Tactic.PolynomialIntegrability

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial inner products from measures

The assumptions impose no restriction on the support of the measure.
The inner product core is a construction, not a global instance on polynomials.

References: DLMF 18.2(i), https://dlmf.nist.gov/18.2; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

@[expose] public section

open MeasureTheory

namespace Polynomial

/-- Finite polynomial moments, expressed as square integrability of all polynomials
(DLMF 18.2(i), Szegő, Chapter 3). -/
def HasFiniteMoments (μ : Measure ℝ) : Prop :=
  ∀ p : ℝ[X], Integrable (fun x => p.eval x ^ 2) μ

/-- Strict positivity of the polynomial integral pairing, without a support restriction
(DLMF 18.2(i), Szegő, Chapter 3). -/
structure HasPositiveDefiniteIntegral (μ : Measure ℝ) : Prop where
  /-- Every polynomial square has a classical finite integral. -/
  moments : HasFiniteMoments μ
  /-- Nonzero polynomial squares have strictly positive integrals. -/
  positive : ∀ p : ℝ[X], p ≠ 0 → 0 < ∫ x, p.eval x ^ 2 ∂μ

instance : CoeFun (HasPositiveDefiniteIntegral μ)
    (fun _ ↦ ∀ p : ℝ[X], p ≠ 0 → 0 < ∫ x, p.eval x ^ 2 ∂μ) :=
  ⟨fun h ↦ h.positive⟩

/-- Internal bridge: a strictly positive integral certifies its integrability. -/
theorem HasPositiveDefiniteIntegral.of_positive {μ : Measure ℝ}
    (h : ∀ p : ℝ[X], p ≠ 0 → 0 < ∫ x, p.eval x ^ 2 ∂μ) :
    HasPositiveDefiniteIntegral μ := by
  refine ⟨?_, h⟩
  intro p
  by_cases hp : p = 0
  · simp [hp]
  · exact Integrable.of_integral_ne_zero (h p hp).ne' 

/-- Finite polynomial moments make all polynomial products integrable
(DLMF 18.2(i), Szegő, Chapter 3). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.integrable_mul {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (p q : ℝ[X]) : Integrable (fun x => p.eval x * q.eval x) μ := by
  have hp : MemLp (fun x => p.eval x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (hμ p)
  have hq : MemLp (fun x => q.eval x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (hμ q)
  exact hp.integrable_mul hq

/-- An orthogonal polynomial sequence supplies all polynomial moments.
This implication does not require positivity (DLMF 18.2(i)). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem Sequence.IsOrthogonal.hasFiniteMoments {μ : Measure ℝ}
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) : HasFiniteMoments μ := by
  intro p
  have hm : p ∈ Submodule.span ℝ (Set.range P) := by
    rw [P.span (fun i => P.isUnit_leadingCoeff i)]
    trivial
  have hp : MemLp (fun x => p.eval x) 2 μ := by
    induction hm using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      exact (memLp_two_iff_integrable_sq (by fun_prop)).2 (hP.integrable_sq n)
    | zero => simp
    | add p q _ _ hp hq => simpa only [eval_add, Pi.add_def] using hp.add hq
    | smul a p _ hp => simpa only [eval_smul, Pi.smul_def] using hp.const_smul a
  exact (memLp_two_iff_integrable_sq (by fun_prop)).1 hp

/-- In particular the measure has finite mass (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem HasFiniteMoments.isFiniteMeasure {μ : Measure ℝ} (hμ : HasFiniteMoments μ) :
    IsFiniteMeasure μ := by
  apply (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
  simpa using hμ 1

/-- Positive square integrals are genuine finite integrals. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasPositiveDefiniteIntegral.hasFiniteMoments {μ : Measure ℝ}
    (hpos : HasPositiveDefiniteIntegral μ) : HasFiniteMoments μ :=
  hpos.moments

/-- The positive integral value is certified together with finite moments. -/
theorem HasPositiveDefiniteIntegral.integral_sq_pos {μ : Measure ℝ}
    (hpos : HasPositiveDefiniteIntegral μ) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < ∫ x, p.eval x ^ 2 ∂μ := hpos.positive p hp

/-- A polynomial pair whose product has a finite integral (DLMF 18.2(i)).
No moment condition is imposed on other polynomials. -/
structure IntegrablePair (μ : Measure ℝ) where
  left : ℝ[X]
  right : ℝ[X]
  integrable : Integrable (fun x => left.eval x * right.eval x) μ

/-- Finite moments supply every polynomial pair (DLMF 18.2(i)). -/
abbrev HasFiniteMoments.pair {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (p q : ℝ[X]) : IntegrablePair μ := ⟨p, q, hμ.integrable_mul p q⟩

/-- Construct an integrable pair from the available integrability evidence.
The automatically filled argument is a proof, never a default integral value. -/
abbrev IntegrablePair.of (μ : Measure ℝ) (p q : ℝ[X])
    (h : Integrable (fun x => p.eval x * q.eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact Polynomial.HasFiniteMoments.integrable_mul
          (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)) _ _
      | (simp only [← pow_two]; assumption)
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    IntegrablePair μ := ⟨p, q, h⟩

/-- The finite integral of a bundled polynomial pair (DLMF 18.2(i)). -/
noncomputable def integralInner (μ : Measure ℝ) (pq : IntegrablePair μ) : ℝ :=
  ∫ x, pq.left.eval x * pq.right.eval x ∂μ

/-- The pairing is exactly the integral of its integrable product. -/
theorem integralInner_eq_integral (μ : Measure ℝ) (pq : IntegrablePair μ) :
    integralInner μ pq = ∫ x, pq.left.eval x * pq.right.eval x ∂μ := rfl

/-- Symmetry of the polynomial pairing (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_comm (μ : Measure ℝ) (p q : ℝ[X])
    {h : Integrable (fun x => p.eval x * q.eval x) μ} :
    integralInner μ (IntegrablePair.of μ p q) = integralInner μ (IntegrablePair.of μ q p (h := by simpa only [mul_comm] using h)) := by
  simp only [integralInner, mul_comm]

/-- The diagonal pairing is the integral of a square (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_self (μ : Measure ℝ) (p : ℝ[X])
    {h : Integrable (fun x => p.eval x * p.eval x) μ} :
    integralInner μ (IntegrablePair.of μ p p) = ∫ x, p.eval x ^ 2 ∂μ := by
  simp only [integralInner, pow_two]

/-- Additivity of the integral pairing (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_add_left {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (p q r : ℝ[X]) :
    integralInner μ (IntegrablePair.of μ (p + q) r) = integralInner μ (IntegrablePair.of μ p r) + integralInner μ (IntegrablePair.of μ q r) := by
  simp only [integralInner, eval_add, add_mul]
  exact integral_add (hμ.integrable_mul p r) (hμ.integrable_mul q r)

/-- Scalar linearity of the integral pairing (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_smul_left (μ : Measure ℝ) (p q : ℝ[X]) (a : ℝ)
    {h : Integrable (fun x => p.eval x * q.eval x) μ} :
    integralInner μ (IntegrablePair.of μ (a • p) q (h := by simpa only [eval_smul, smul_eq_mul, mul_assoc] using h.const_mul a)) = a * integralInner μ (IntegrablePair.of μ p q) := by
  simp only [integralInner, eval_smul, smul_eq_mul, mul_assoc, integral_const_mul]

/-- Pairing with zero vanishes (DLMF 18.2(i), Szegő, Chapter 3). -/
@[simp] theorem integralInner_zero_left (μ : Measure ℝ) (p : ℝ[X]) :
    integralInner μ (IntegrablePair.of μ 0 p (h := by simp)) = 0 := by simp [integralInner]

/-- Subtraction in the first slot (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_sub_left {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (p q r : ℝ[X]) :
    integralInner μ (IntegrablePair.of μ (p - q) r) = integralInner μ (IntegrablePair.of μ p r) - integralInner μ (IntegrablePair.of μ q r) := by
  simp only [integralInner, eval_sub, sub_mul]
  exact integral_sub (hμ.integrable_mul p r) (hμ.integrable_mul q r)

/-- Vanishing of a squared norm forces the polynomial to vanish
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem HasPositiveDefiniteIntegral.eq_zero_of_integralInner_self_eq_zero {μ : Measure ℝ}
    (hμ : HasPositiveDefiniteIntegral μ) {p : ℝ[X]}
    {h : Integrable (fun x => p.eval x * p.eval x) μ} (hp : integralInner μ (IntegrablePair.of μ p p) = 0) : p = 0 := by
  by_contra hpne
  have := hμ p hpne
  rw [← integralInner_self μ p (h := h), hp] at this
  exact (lt_irrefl _ this)

/-- The polynomial integral pairing defines an inner product core under the agreed
moment and positivity hypotheses (DLMF 18.2(i), Szegő, Chapter 3).
Install the resulting norm and inner product only locally, since they depend on `μ`. -/
@[instance_reducible]
noncomputable def integralInnerProductCore (μ : Measure ℝ) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) : InnerProductSpace.Core ℝ ℝ[X] where
  inner := fun p q => integralInner μ (hμ.pair p q)
  conj_inner_symm p q := by simpa using integralInner_comm μ q p (h := hμ.integrable_mul q p)
  re_inner_nonneg p := by
    change 0 ≤ integralInner μ (IntegrablePair.of μ p p)
    rw [integralInner_self]
    exact integral_nonneg (fun _ => sq_nonneg _)
  add_left := integralInner_add_left hμ
  smul_left p q a := by simpa using integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)
  definite _ hp := hpos.eq_zero_of_integralInner_self_eq_zero hp

end Polynomial
