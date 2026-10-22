/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Moments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Normalization
public import LeanFun.Mathlib.Algebra.MvPolynomial.ScaledLift
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Separated Koornwinder polynomial systems

The first label is outer degree plus inner degree, not necessarily total degree.
A polynomial inner lift records the geometry without imposing ordinary-degree
restrictions. Reference: Dunkl–Xu, §2.6.1.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Normalized separated data with polynomial inner lifts. -/
structure KoornwinderSystem {D : Set ℝ} (a : ℝ[X]) (ρ : D → ℝ) (μ : Measure D) (ν : Measure ℝ) where
  /-- The squared scale is nonnegative on the outer source. -/
  scale_nonneg : ∀ᵐ x : D ∂μ, 0 ≤ a.eval (x : ℝ)
  /-- One outer sequence for each inner degree. -/
  outer : ℕ → Polynomial.Sequence ℝ
  /-- The common inner sequence. -/
  inner : Polynomial.Sequence ℝ
  /-- A division-free polynomial realization of each scaled inner member. -/
  lift : ℕ → MvPolynomial (Fin 2) ℝ
  /-- The lift realizes the separated expression on the outer measure. -/
  lift_eval : ∀ k, ∀ᵐ x ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) (lift k) =
    ρ x^k * (inner k).eval z
  /-- Orthogonality of the inner sequence. -/
  inner_orthogonal : inner.IsOrthogonal ν
  /-- Orthogonality in each shifted outer measure. -/
  outer_orthogonal : ∀ k, (outer k).IsOrthogonal (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val))
  /-- Positive inner leading coefficients fix orientation. -/
  inner_leadingCoeff_pos : ∀ k, 0 < (inner k).leadingCoeff
  /-- Positive outer leading coefficients fix orientation. -/
  outer_leadingCoeff_pos : ∀ k n, 0 < (outer k n).leadingCoeff
  /-- Inner squared norms are one. -/
  inner_norm : ∀ k, Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (inner k) (inner k)) = 1
  /-- Outer squared norms are one. -/
  outer_norm : ∀ k n, Polynomial.integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (outer k n) (outer k n)) = 1

namespace KoornwinderSystem
variable {D : Set ℝ} {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}

/-- The inner orthogonal sequence supplies every inner moment. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_inner (S : KoornwinderSystem a ρ μ ν) : Polynomial.HasFiniteMoments ν :=
  S.inner_orthogonal.hasFiniteMoments

/-- The degree-zero outer sequence supplies every outer moment. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_outer (S : KoornwinderSystem a ρ μ ν) : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ) := by
  simpa only [koornwinderOuterMeasure_zero] using (S.outer_orthogonal 0).hasFiniteMoments

/-- A polynomial squared scale gives all moments of a separated system. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments (S : KoornwinderSystem a ρ μ ν) (hρ : Continuous ρ)
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) :
    MvPolynomial.HasFiniteMoments (koornwinderMeasure ρ μ ν) :=
  hasFiniteMoments_koornwinderMeasure S.hasFiniteMoments_outer S.hasFiniteMoments_inner hρ a ha

variable (S : KoornwinderSystem a ρ μ ν)

/-- The polynomial at separated labels (n,k), with outer degree n-k. -/
noncomputable def polynomial (n k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (S.outer k (n-k)).eval₂ C (X 0) * S.lift k

/-- The separated evaluation identity holds almost everywhere in the outer factor. -/
theorem eval_polynomial (n k : ℕ) :
    ∀ᵐ x ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) (S.polynomial n k) =
      (S.outer k (n-k)).eval (x : ℝ) * ρ x^k * (S.inner k).eval z := by
  filter_upwards [S.lift_eval k] with x hx
  intro z
  rw [polynomial, map_mul, hx z, eval_eval₂_C_X]
  simp [koornwinderCoordinates, mul_assoc]

/-- A bound on the inner lift yields the ordinary total-degree bound. -/
theorem totalDegree_polynomial_le (hlift : ∀ k, (S.lift k).totalDegree ≤ k)
    {n k : ℕ} (hk : k ≤ n) : (S.polynomial n k).totalDegree ≤ n := by
  unfold polynomial
  have h := totalDegree_mul ((S.outer k (n-k)).eval₂ C (X 0)) (S.lift k)
  have he := totalDegree_eval₂_C_X_le (S.outer k (n-k)) (0 : Fin 2)
  rw [Sequence.natDegree_eq] at he
  have := hlift k
  omega

/-- An integrable outer factor gives an integrable separated polynomial product. -/
theorem integrable_polynomial_mul [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (n k m j : ℕ)
    (hi : Integrable (fun x : D => (S.outer k (n-k)).eval (x : ℝ) *
      (S.outer j (m-j)).eval (x : ℝ) * ρ x^(k+j)) μ) :
    Integrable (fun v => eval v (S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
  rw [koornwinderMeasure, integrable_map_measure
    (show AEStronglyMeasurable (fun v => eval v (S.polynomial n k) *
      eval v (S.polynomial m j)) _ from
      ((S.polynomial n k).continuous_eval.mul (S.polynomial m j).continuous_eval).aestronglyMeasurable)
    (continuous_koornwinderCoordinates hρ).measurable.aemeasurable]
  apply (hi.mul_prod (S.inner_orthogonal.integrable k j)).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial n k),
    Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial m j)] with v hv hw
  dsimp only [Function.comp_apply]
  rw [hv v.2, hw v.2, pow_add]
  ring

/-- The shifted outer orthogonality supplies the matching-label outer integrability. -/
theorem integrable_outer_product (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ))
    (n m k : ℕ) :
    Integrable (fun x : D => (S.outer k (n-k)).eval (x : ℝ) *
      (S.outer k (m-k)).eval (x : ℝ) * ρ x^(k+k)) μ := by
  have hi := (S.outer_orthogonal k).integrable (n-k) (m-k)
  have hapos : ∀ᵐ x ∂Measure.map Subtype.val μ, 0 ≤ (a^k).eval x := by
    filter_upwards [ae_nonneg_eval_map_subtype S.scale_nonneg] with x hx
    simpa only [Polynomial.eval_pow] using pow_nonneg hx k
  have hw := (integrable_polynomialDensityMeasure_comap_iff (a^k) hapos _).mp hi
  have hi' := (integrable_map_measure
    ((a^k).continuous.mul ((S.outer k (n-k)).continuous.mul
      (S.outer k (m-k)).continuous)).aestronglyMeasurable
    measurable_subtype_coe.aemeasurable).mp hw
  apply hi'.congr
  filter_upwards [ha] with x hx
  simp only [Function.comp_apply, Polynomial.eval_pow, Pi.mul_apply]
  rw [← hx, show k+k=2*k by omega, pow_mul]
  ring

/-- The separated scale relation gives integrability of every polynomial pair in the system. -/
theorem integrable_polynomial_mul_of_scale [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) (n k m j : ℕ) :
    Integrable (fun v => eval v (S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
  have hs (n k : ℕ) : MemLp (fun v => eval v (S.polynomial n k)) 2
      (koornwinderMeasure ρ μ ν) := by
    apply (memLp_two_iff_integrable_sq (S.polynomial n k).continuous_eval.aestronglyMeasurable).2
    simpa only [pow_two] using S.integrable_polynomial_mul hρ n k n k
      (S.integrable_outer_product ha n n k)
  exact (hs n k).integrable_mul (hs m j)

/-- Products of separated members factor into one-dimensional pairings. -/
theorem integralInner_polynomial [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (n k m j : ℕ)
    (hi : Integrable (fun x : D => (S.outer k (n-k)).eval (x : ℝ) *
      (S.outer j (m-j)).eval (x : ℝ) * ρ x^(k+j)) μ) :
    integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial n k) (S.polynomial m j)
      (h := S.integrable_polynomial_mul hρ n k m j hi)) =
      (∫ x, (S.outer k (n-k)).eval (x : ℝ) * (S.outer j (m-j)).eval (x : ℝ) * ρ x^(k+j) ∂μ) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (S.inner k) (S.inner j)
          (h := S.inner_orthogonal.integrable k j)) := by
  have he := (koornwinderMeasure_integral
    (KoornwinderMeasureInput.ofContinuous μ ν hρ)
    ⟨fun v ↦ eval v (S.polynomial n k*S.polynomial m j), by simpa only [map_mul] using S.integrable_polynomial_mul hρ n k m j hi⟩).2
  simp only [map_mul] at he
  rw [integralInner, he, Polynomial.integralInner, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial n k),
    Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial m j)] with v hv hw
  rw [hv v.2, hw v.2, pow_add]
  ring

/-- Equal inner labels identify the shifted outer pairing. -/
theorem integralInner_polynomial_same_inner [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) (n m k : ℕ) :
    integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial n k) (S.polynomial m k)
      (h := S.integrable_polynomial_mul_of_scale hρ ha n k m k)) =
      Polynomial.integralInner (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (Polynomial.IntegrablePair.of (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) (S.outer k (n-k)) (S.outer k (m-k))
        (h := (S.outer_orthogonal k).integrable _ _)) := by
  rw [S.integralInner_polynomial hρ n k m k (S.integrable_outer_product ha n m k), S.inner_norm, mul_one,
    Polynomial.integralInner, integral_koornwinderOuterMeasure (Measure.map Subtype.val μ) a
      ((ae_map_iff measurable_subtype_coe.aemeasurable
        (measurableSet_le measurable_const a.continuous.measurable)).mpr
          (ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x)))) k
      ⟨_, (S.outer_orthogonal k).integrable (n-k) (m-k)⟩]
  dsimp only
  have he := integral_map (μ := μ) measurable_subtype_coe.aemeasurable
    (((a.continuous.pow k).mul
      ((S.outer k (n-k)).continuous.mul (S.outer k (m-k)).continuous)).aestronglyMeasurable)
  simp only [Pi.mul_apply, Pi.pow_apply] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [show k+k=2*k by omega, pow_mul, hx]
  ring

/-- Mixed outer factors are integrable by Cauchy--Schwarz. -/
theorem integrable_mixed_outer_product (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ))
    (hρ : Continuous ρ) (n k m j : ℕ) :
    Integrable (fun x : D => (S.outer k (n-k)).eval (x : ℝ) *
      (S.outer j (m-j)).eval (x : ℝ) * ρ x^(k+j)) μ := by
  have hs (n k : ℕ) : MemLp (fun x : D => (S.outer k (n-k)).eval (x : ℝ) * ρ x^k) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      ((((S.outer k (n-k)).continuous.comp continuous_subtype_val).mul (hρ.pow k)).aestronglyMeasurable)).2
    convert S.integrable_outer_product ha n n k using 1
    ext x
    simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  convert (hs n k).integrable_mul (hs m j) using 1
  ext x
  simp only [Pi.mul_apply, pow_add]
  ring

/-- Distinct valid separated labels are orthogonal. -/
theorem integralInner_polynomial_eq_zero [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) {n k m j : ℕ}
    (hk : k ≤ n) (hj : j ≤ m) (hne : (n,k) ≠ (m,j)) :
    integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial n k) (S.polynomial m j)
      (h := S.integrable_polynomial_mul_of_scale hρ ha n k m j)) = 0 := by
  by_cases hkj : k=j
  · subst j
    rw [S.integralInner_polynomial_same_inner hρ ha]
    exact (S.outer_orthogonal k).orthogonal _ _ (by intro h; apply hne; congr 1; omega)
  · rw [S.integralInner_polynomial hρ n k m j
        (S.integrable_mixed_outer_product ha hρ n k m j),
      show Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (S.inner k) (S.inner j)
          (h := S.inner_orthogonal.integrable k j)) = 0 from
        S.inner_orthogonal.orthogonal k j hkj, mul_zero]

/-- Each separated member has unit squared norm. -/
theorem integralInner_polynomial_self [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) (n k : ℕ) :
    integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (S.polynomial n k) (S.polynomial n k)
      (h := S.integrable_polynomial_mul_of_scale hρ ha n k n k)) = 1 := by
  rw [S.integralInner_polynomial_same_inner hρ ha, S.outer_norm]

end KoornwinderSystem
/-- Every shifted outer family supplies its polynomial moments (Dunkl–Xu, §2.6.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem KoornwinderSystem.hasFiniteMoments_shifted_outer
    {D : Set ℝ} {a : Polynomial ℝ} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (k : ℕ) :
    Polynomial.HasFiniteMoments (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) :=
  (S.outer_orthogonal k).hasFiniteMoments

/-- Polynomial scales supply all separated moments (Dunkl–Xu, §2.6.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem KoornwinderSystem.hasFiniteMoments_polynomial_scale
    {D : Set ℝ} {μ : Measure D} {ν : Measure ℝ} (c : Polynomial ℝ)
    (S : KoornwinderSystem (c^2) (fun x : D => c.eval (x : ℝ)) μ ν) :
    MvPolynomial.HasFiniteMoments (koornwinderMeasure (fun x : D => c.eval (x : ℝ)) μ ν) :=
  S.hasFiniteMoments (c.continuous.comp continuous_subtype_val) (by simp)

end MvPolynomial
