/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Measure

/-!
# Separated modifications of Cartesian disk measures

An inner modification of degree at most 2l is accompanied by the outer
polynomial (1-x²)^l h(x). The pairing-transfer identity is the mechanism behind
bounded support inside degree blocks.
Reference: Dunkl–Xu, Cartesian constructions; Gutleb–Olver–Slevinsky,
polynomial measure modification.
-/

@[expose] public section
open MeasureTheory Set
namespace Polynomial

/-- The outer factor required by a polynomially separated disk modification. -/
noncomputable def diskModificationWeight (h : ℝ[X]) (l : ℕ) : ℝ[X] := (1-X^2)^l*h

/-- Modify an outer source on the full nonnegative locus of its polynomial density. -/
noncomputable def diskOuterModification (h : ℝ[X]) (l : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ (diskModificationWeight h l).eval x}) : Measure ℝ :=
  polynomialDensityMeasure (diskModificationWeight h l) μ

/-- Values on measurable sets are the nonnegative polynomial-density integrals. -/
theorem diskOuterModification_apply (h : ℝ[X]) (l : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ (diskModificationWeight h l).eval x})
    {s : Set ℝ} (hs : MeasurableSet s) :
    diskOuterModification h l μ s = ∫⁻ x in Subtype.val ⁻¹' s,
      ENNReal.ofNNReal (NNReal.mk ((diskModificationWeight h l).eval (x : ℝ)) x.property) ∂μ :=
  polynomialDensityMeasure_apply _ μ hs

/-- Nonnegative outer factors give nonnegative modified weights on the strip. -/
theorem diskModificationWeight_nonneg {μ : Measure ℝ}
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h : ℝ[X])
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (l : ℕ) :
    ∀ᵐ x ∂μ, 0 ≤ (diskModificationWeight h l).eval x := by
  filter_upwards [hx,hh] with x hx hh
  simp only [diskModificationWeight, eval_mul, eval_pow, eval_sub, eval_one, eval_X]
  exact mul_nonneg (pow_nonneg (by nlinarith [hx.1,hx.2]) _) hh

/-- A nonzero outer factor gives a nonzero modification polynomial. -/
theorem diskModificationWeight_ne_zero {h : ℝ[X]} (hh : h ≠ 0) (l : ℕ) :
    diskModificationWeight h l ≠ 0 := by
  apply mul_ne_zero _ hh
  apply pow_ne_zero
  intro he
  have := congrArg (fun p : ℝ[X] => p.eval 0) he
  simp at this

/-- Outer modifications retain the support condition. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem ae_mem_diskOuterModification {μ : Measure ℝ}
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h : ℝ[X]) (l : ℕ) :
    ∀ᵐ x ∂diskOuterModification h l (μ.comap Subtype.val), x ∈ Icc (-1 : ℝ) 1 := by
  exact (polynomialDensityMeasure_comap_absolutelyContinuous
    (diskModificationWeight h l) μ).ae_le hx

/-- Finite moments survive the separated outer modification. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.diskOuterModification {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h : ℝ[X])
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (l : ℕ) :
    HasFiniteMoments (diskOuterModification h l (μ.comap Subtype.val)) := by
  exact hμ.polynomialDensityMeasure _ (diskModificationWeight_nonneg hx h hh l)

/-- Strict positivity survives a nonzero separated outer modification. -/
theorem HasPositiveDefiniteIntegral.diskOuterModification {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h : ℝ[X]) (hh0 : h ≠ 0)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (l : ℕ) :
    HasPositiveDefiniteIntegral (diskOuterModification h l (μ.comap Subtype.val)) := by
  exact hpos.polynomialDensityMeasure hμ _ (diskModificationWeight_ne_zero hh0 l)
    (diskModificationWeight_nonneg hx h hh l)

/-- An even outer factor preserves evenness of the modified measure. -/
theorem isNegInvariant_diskOuterModification (μ : Measure ℝ) [μ.IsNegInvariant]
    (h : ℝ[X]) (hh : ∀ x, h.eval (-x) = h.eval x) (l : ℕ) :
    (diskOuterModification h l (μ.comap Subtype.val)).IsNegInvariant := by
  apply isNegInvariant_polynomialDensityMeasure_comap
  intro x
  simp [diskModificationWeight, hh]

/-- Moving an even inner-degree gap through the modified pairing leaves a
polynomial of uniformly bounded degree in the original outer measure. -/
theorem integralInner_diskOuterModification_transfer {μ : Measure ℝ}
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h : ℝ[X])
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (p q : ℝ[X]) (l j k r : ℕ)
    (hr : r ≤ l) (hk : k=j+2*r)
    (hi : Integrable (fun x => ((1-X^2)^r*p).eval x*q.eval x)
      (diskOuterMeasure j ((diskOuterModification h l (μ.comap Subtype.val)).comap Subtype.val)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => p.eval x*((((1-X^2)^(l-r)*h)*q).eval x))
      (diskOuterMeasure k (μ.comap Subtype.val)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (diskOuterMeasure j ((diskOuterModification h l (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure j ((diskOuterModification h l (μ.comap Subtype.val)).comap Subtype.val)) ((1-X^2)^r*p) q) =
      integralInner (diskOuterMeasure k (μ.comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k (μ.comap Subtype.val)) p (((1-X^2)^(l-r)*h)*q)) := by
  have hx' := ae_mem_diskOuterModification hx h l
  have hu : ∀ᵐ x ∂diskOuterModification h l (μ.comap Subtype.val),
      0 ≤ ((1-X^2 : ℝ[X])^j).eval x := by
    filter_upwards [hx'] with x hx
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [hx.1,hx.2]) j
  have hi' : Integrable (fun x => (1-x^2)^j * (((1-X^2)^r*p).eval x*q.eval x))
      (diskOuterModification h l (μ.comap Subtype.val)) := by
    simpa only [eval_pow, eval_sub, eval_one, eval_X] using
      (integrable_polynomialDensityMeasure_comap_iff ((1-X^2)^j) hu _).mp hi
  simp only [integralInner]
  erw [integral_diskOuterMeasure _ hx' j ⟨_, hi⟩,
    integral_polynomialDensityMeasure_comap _ (diskModificationWeight_nonneg hx h hh l) ⟨_, hi'⟩,
    integral_diskOuterMeasure μ hx k ⟨_, hj⟩]
  dsimp only
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [diskModificationWeight, eval_mul, eval_pow, eval_sub, eval_one, eval_X]
  calc
    _ = (1-x^2)^(l+j+r) * (h.eval x*p.eval x*q.eval x) := by
      rw [pow_add, pow_add]
      ring
    _ = (1-x^2)^(k+(l-r)) * (h.eval x*p.eval x*q.eval x) := by
      congr 2
      omega
    _ = _ := by rw [pow_add]; ring

end Polynomial
