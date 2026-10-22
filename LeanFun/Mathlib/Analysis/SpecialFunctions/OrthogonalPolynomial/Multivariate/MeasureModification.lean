/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.PolynomialDensityMeasure
public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramFactorBandwidth
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Polynomial modification of multivariate measures

A nonnegative polynomial density turns the modified Gram pairing into the
original pairing with polynomial multiplication. Statements use exact polynomial
algebra and finitely supported coefficients; no infinite operator assumptions
or same-size truncation identities are introduced.

Reference: Gutleb–Olver–Slevinsky, measure modifications, Lemma 2.8 and Section 5.
-/

public section
open MeasureTheory Module
open scoped NNReal ENNReal
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] {μ : Measure (σ → ℝ)}

/-- Multiplying a measure by a nonnegative polynomial preserves finite moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.withDensity_polynomial (hμ : HasFiniteMoments μ)
    (u : MvPolynomial σ ℝ) (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u) :
    HasFiniteMoments (polynomialDensityMeasure u (μ.comap Subtype.val)) := by
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension u
  rw [he]
  intro p
  rw [integrable_withDensity_iff_integrable_smul' hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply (hμ.integrable_mul (u * p) p).congr
  filter_upwards [hu] with x hx
  rw [hwval x hx]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, map_mul, pow_two]
  ring

/-- Integrability is transported with a nonnegative polynomial density. -/
theorem integrable_mul_withDensity_polynomial_iff (u p q : MvPolynomial σ ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u) :
    Integrable (fun x => eval x p * eval x q)
        (polynomialDensityMeasure u (μ.comap Subtype.val)) ↔
      Integrable (fun x => eval x (u * p) * eval x q) μ := by
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension u
  rw [he, integrable_withDensity_iff_integrable_smul' hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integrable_congr
  filter_upwards [hu] with x hx
  rw [hwval x hx]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, map_mul, mul_assoc]

/-- The modified pairing is polynomial multiplication in the original pairing. -/
theorem integralInner_withDensity_polynomial (u p q : MvPolynomial σ ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u)
    {hpq : Integrable (fun x => eval x (u * p) * eval x q) μ} :
    integralInner (polynomialDensityMeasure u (μ.comap Subtype.val))
      (IntegrablePair.of _ p q (h := (integrable_mul_withDensity_polynomial_iff u p q hu).2 hpq)) =
      integralInner μ (IntegrablePair.of μ (u * p) q) := by
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension u
  change (∫ x, eval x p * eval x q ∂polynomialDensityMeasure u (μ.comap Subtype.val)) =
    ∫ x, eval x (u*p) * eval x q ∂μ
  rw [he, integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hwval x hx]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, map_mul]
  ring

/-- A nonzero nonnegative polynomial modification preserves strict positivity
of the polynomial pairing, even if its density vanishes on part of the support. -/
theorem HasPositiveDefiniteIntegral.withDensity_polynomial
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (u : MvPolynomial σ ℝ) (hu0 : u ≠ 0) (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u) :
    HasPositiveDefiniteIntegral (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  rw [← integralInner_self _ p
    (h := (hμ.withDensity_polynomial u hu).integrable_mul p p),
    integralInner_withDensity_polynomial u p p hu (hpq := hμ.integrable_mul _ _)]
  have hi := hμ.integrable_mul (u * p) p
  have hn : 0 ≤ᵐ[μ] fun x => eval x (u * p) * eval x p := by
    filter_upwards [hu] with x hx
    change 0 ≤ eval x (u * p) * eval x p
    simpa only [map_mul, mul_assoc, ← pow_two] using mul_nonneg hx (sq_nonneg (eval x p))
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro heq
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp heq.symm
  have hup : integralInner μ (IntegrablePair.of μ (u * p) (u * p)) = 0 := by
    unfold integralInner
    calc
      _ = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae (by
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply, map_mul] at hx ⊢
        rcases mul_eq_zero.mp hx with h | h
        · rw [h, zero_mul]
        · simp [h])
      _ = 0 := integral_zero _ _
  exact (mul_ne_zero hu0 hp) (hpos.eq_zero_of_integralInner_self_eq_zero hup)

/-- The modified finite Gram matrix consists of exact multiplication pairings;
this holds on arbitrary multivariate polynomial families. -/
theorem integralGram_withDensity_polynomial {n : ℕ}
    (u : MvPolynomial σ ℝ) (P : Fin n → MvPolynomial σ ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u)
    (hi : ∀ i j, Integrable (fun x => eval x (u*P i)*eval x (P j)) μ := by
      intro i j
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralGram (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) P
      (hP := fun i j => (integrable_mul_withDensity_polynomial_iff u (P i) (P j) hu).2 (hi i j)) =
      fun i j => integralInner μ (IntegrablePair.of μ (u * P i) (P j)) := by
  ext i j
  exact integralInner_withDensity_polynomial u (P i) (P j) hu (hpq := hi i j)

/-- A degree-$d$ modification has no Gram entries between polynomial degree
blocks separated by more than $d$. This does not assert sparsity within blocks. -/
theorem integralInner_withDensity_eq_zero_of_degree
    {ι : Type*} (P : ι → MvPolynomial σ ℝ) (degree : ι → ℕ)
    (hdegree : ∀ i, (P i).totalDegree ≤ degree i)
    (horth : ∀ i q, q.totalDegree < degree i →
      ∃ hi : Integrable (fun x => eval x q * eval x (P i)) μ,
        integralInner μ (IntegrablePair.of μ q (P i) hi) = 0)
    (u : MvPolynomial σ ℝ) (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u) (i j : ι)
    (hij : degree j + u.totalDegree < degree i ∨
      degree i + u.totalDegree < degree j) :
    integralInner (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (IntegrablePair.of (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (P i) (P j) (h := by
      apply (integrable_mul_withDensity_polynomial_iff u (P i) (P j) hu).2
      rcases hij with hij | hij
      · have hd : (u*P j).totalDegree < degree i := by
          have := totalDegree_mul u (P j)
          have := hdegree j
          omega
        obtain ⟨hi, _⟩ := horth i (u*P j) hd
        simpa only [map_mul, mul_comm, mul_left_comm, mul_assoc] using hi
      · have hd : (u*P i).totalDegree < degree j := by
          have := totalDegree_mul u (P i)
          have := hdegree i
          omega
        exact (horth j (u*P i) hd).choose)) = 0 := by
  rcases hij with hij | hij
  · have hd : (u*P j).totalDegree < degree i := by
      have := totalDegree_mul u (P j)
      have := hdegree j
      omega
    obtain ⟨hi, hz⟩ := horth i (u*P j) hd
    rw [integralInner_comm, integralInner_withDensity_polynomial u (P j) (P i) hu (hpq := hi)]
    exact hz
  · have hd : (u*P i).totalDegree < degree j := by
      have := totalDegree_mul u (P i)
      have := hdegree i
      omega
    obtain ⟨hi, hz⟩ := horth j (u*P i) hd
    rw [integralInner_withDensity_polynomial u (P i) (P j) hu (hpq := hi)]
    exact hz

/-- The positive Cholesky factor of a polynomially modified Gram matrix is
banded by total degree. Additional zeros inside those blocks are a separate issue. -/
theorem gram_factor_eq_zero_of_degree {n : ℕ}
    (P : Fin n → MvPolynomial σ ℝ) (degree : Fin n → ℕ)
    (hmon : Monotone degree) (hdegree : ∀ i, (P i).totalDegree ≤ degree i)
    (horth : ∀ i q, q.totalDegree < degree i →
      ∃ hi : Integrable (fun x => eval x q * eval x (P i)) μ,
        integralInner μ (IntegrablePair.of μ q (P i) hi) = 0)
    (u : MvPolynomial σ ℝ) (hu : ∀ᵐ x ∂μ, 0 ≤ eval x u)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsUpperTriangular)
    (hp : ∀ i, 0 < R i i)
    (hi : ∀ i j, Integrable (fun x => eval x (P i)*eval x (P j))
      (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    (hg : integralGram (MvPolynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) P (hP := hi) =
      R.transpose * R) :
    ∀ i j, degree i + u.totalDegree < degree j → R i j = 0 := by
  apply hR.eq_zero_of_transpose_mul_self_degree_band (fun i => ne_of_gt (hp i))
    degree hmon u.totalDegree
  intro i j hij
  rw [← hg]
  exact integralInner_withDensity_eq_zero_of_degree P degree hdegree horth u hu i j (Or.inr hij)

omit [Fintype σ] in
/-- Conversion intertwines multiplication on finitely supported polynomial
coefficients. The bases may have arbitrary index sets and need not be orthogonal. -/
theorem coefficientMap_mul_intertwining {ι κ : Type*}
    (p : Basis ι ℝ (MvPolynomial σ ℝ)) (q : Basis κ ℝ (MvPolynomial σ ℝ))
    (u : MvPolynomial σ ℝ) :
    (p.coefficientMap q LinearMap.id).comp
        (p.coefficientMap p (LinearMap.mulLeft ℝ u)) =
      (q.coefficientMap q (LinearMap.mulLeft ℝ u)).comp
        (p.coefficientMap q LinearMap.id) := by
  rw [Basis.coefficientMap_comp, Basis.coefficientMap_comp]
  simp

end MvPolynomial
