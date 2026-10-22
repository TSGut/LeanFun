/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System
public import LeanFun.Mathlib.MeasureTheory.Integral.ProductReflection

/-! # Reflection sectors of modified Cartesian disk Gram matrices
Even modifications preserve both inner and outer parity sectors. This applies
to disconnected even outer measures as well as the standard disk weight.
Reference: Dunkl--Xu, Cartesian systems; symmetry of orthogonal polynomials.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ} (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)

/-- Reflecting the inner coordinate gives the inner-degree parity sign. -/
theorem eval_polynomial_neg_inner (n k : ℕ) (x z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x, -z)) (S.polynomial n k) =
      (-1 : ℝ) ^ k * eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x, z)) (S.polynomial n k) := by
  have hp := congrArg (fun p : ℝ[X] ↦ p.eval z)
    (comp_neg_X_eq_of_coeff_parity k (S.inner_parity k))
  have he : (S.inner k).eval (-z) = (-1 : ℝ) ^ k * (S.inner k).eval z := by simpa using hp
  rw [polynomial, eval_cartesianDiskPolynomial _ _ _ (by simp) (S.inner_parity k) _ _ hx,
    eval_cartesianDiskPolynomial _ _ _ (by simp) (S.inner_parity k) _ _ hx, he]
  ring

/-- Reflecting the outer coordinate gives the outer-degree parity sign. -/
theorem eval_polynomial_neg_outer [μ.IsNegInvariant]
    (hxμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (n k : ℕ) (x z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (-x, z)) (S.polynomial n k) =
      (-1 : ℝ) ^ (n - k) * eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x, z)) (S.polynomial n k) := by
  let := isNegInvariant_diskOuterMeasure μ k
  have hp := congrArg (fun p : ℝ[X] ↦ p.eval x)
    ((S.outer_orthogonal_real k).comp_neg_X (hμ.diskOuterMeasure hxμ k)
      (hpos.diskOuterMeasure hμ hxμ k) (n - k))
  have he : (S.outer k (n - k)).eval (-x) =
      (-1 : ℝ) ^ (n - k) * (S.outer k (n - k)).eval x := by simpa using hp
  have hnx : -x ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  rw [polynomial, eval_cartesianDiskPolynomial _ _ _ (by simp) (S.inner_parity k) _ _ hnx,
    eval_cartesianDiskPolynomial _ _ _ (by simp) (S.inner_parity k) _ _ hx, he, neg_sq]
  ring

private theorem parity_sign_mul {n m : ℕ} (hnm : n % 2 ≠ m % 2) :
    (-1 : ℝ) ^ n * (-1 : ℝ) ^ m = -1 := by
  rw [neg_one_pow_eq_pow_mod_two n, neg_one_pow_eq_pow_mod_two m]
  have h : (n % 2 = 0 ∧ m % 2 = 1) ∨ (n % 2 = 1 ∧ m % 2 = 0) := by omega
  rcases h with ⟨hn, hm⟩ | ⟨hn, hm⟩ <;> simp [hn, hm]

/-- An inner-even polynomial modification cannot couple opposite inner parities. -/
theorem integralInner_mul_polynomial_eq_zero_of_inner_parity [SFinite ν]
    [ν.IsNegInvariant] (hxμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (u : MvPolynomial (Fin 2) ℝ)
    (hu : ∀ (x : Icc (-1 : ℝ) 1) z,
      eval (diskCoordinates (x,-z)) u = eval (diskCoordinates (x,z)) u)
    (n k m j : ℕ) (hkj : k % 2 ≠ j % 2) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (u * S.polynomial n k) (S.polynomial m j)) = 0 := by
  have hpair : Integrable (fun v => eval v (u*S.polynomial n k) *
      eval v (S.polynomial m j)) (cartesianDiskMeasure (μ.comap Subtype.val)
        (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)) := by
    aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])
  have hi := cartesianDiskMeasure_integral (μ.comap Subtype.val)
    (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)
    ⟨fun v => eval v (u*S.polynomial n k)*eval v (S.polynomial m j), hpair⟩
  simp only [map_mul] at hi
  simp only [integralInner, map_mul]
  rw [hi.2]
  let F : Icc (-1 : ℝ) 1 × ℝ → ℝ := fun v => eval (diskCoordinates v) u *
    eval (diskCoordinates v) (S.polynomial n k) *
      eval (diskCoordinates v) (S.polynomial m j)
  change (∫ v, F v ∂(μ.comap Subtype.val).prod ν) = 0
  let e := (MeasurableEquiv.refl (Icc (-1 : ℝ) 1)).prodCongr (MeasurableEquiv.neg ℝ)
  have hm : Measure.map e ((μ.comap Subtype.val).prod ν) =
      (μ.comap Subtype.val).prod ν := by
    change Measure.map (Prod.map id Neg.neg) ((μ.comap Subtype.val).prod ν) = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_neg,
      Measure.map_id, Measure.map_neg_eq_self]
  have hF : (fun v => F (e v)) =ᵐ[(μ.comap Subtype.val).prod ν] fun v => -F v := by
    filter_upwards [] with v
    change eval (diskCoordinates (v.1,-v.2)) u *
      eval (diskCoordinates (v.1,-v.2)) (S.polynomial n k) *
        eval (diskCoordinates (v.1,-v.2)) (S.polynomial m j) = -F v
    erw [hu v.1 v.2, S.eval_polynomial_neg_inner n k (v.1 : ℝ) v.2 v.1.property,
      S.eval_polynomial_neg_inner m j (v.1 : ℝ) v.2 v.1.property]
    calc
      _ = ((-1 : ℝ)^k*(-1 : ℝ)^j)*F v := by dsimp [F,diskCoordinates]; ring
      _ = _ := by rw [parity_sign_mul hkj]; ring
  have he := integral_map_equiv (μ := (μ.comap Subtype.val).prod ν) e F
  rw [hm, integral_congr_ae hF, integral_neg] at he
  linarith

/-- An outer-even polynomial modification cannot couple opposite outer parities. -/
theorem integralInner_mul_polynomial_eq_zero_of_outer_parity [SFinite ν]
    [μ.IsNegInvariant] (hxμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (u : MvPolynomial (Fin 2) ℝ)
    (hu : ∀ (x : Icc (-1 : ℝ) 1) z,
      eval (![-(x : ℝ), Real.sqrt (1-(-(x : ℝ))^2)*z]) u =
        eval (diskCoordinates (x,z)) u)
    (n k m j : ℕ) (hnm : (n - k) % 2 ≠ (m - j) % 2) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (u * S.polynomial n k) (S.polynomial m j)) = 0 := by
  have hpair : Integrable (fun v => eval v (u*S.polynomial n k) *
      eval v (S.polynomial m j)) (cartesianDiskMeasure (μ.comap Subtype.val)
        (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)) := by
    aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])
  have hi := cartesianDiskMeasure_integral (μ.comap Subtype.val)
    (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)
    ⟨fun v => eval v (u*S.polynomial n k)*eval v (S.polynomial m j), hpair⟩
  simp only [map_mul] at hi
  simp only [integralInner, map_mul]
  rw [hi.2]
  let F : Icc (-1 : ℝ) 1 × ℝ → ℝ := fun v => eval (diskCoordinates v) u *
    eval (diskCoordinates v) (S.polynomial n k) *
      eval (diskCoordinates v) (S.polynomial m j)
  change (∫ v, F v ∂(μ.comap Subtype.val).prod ν) = 0
  let negX (x : Icc (-1 : ℝ) 1) : Icc (-1 : ℝ) 1 :=
    ⟨-(x : ℝ), by constructor <;> linarith [x.property.1,x.property.2]⟩
  have hn : Continuous negX := by dsimp [negX]; fun_prop
  let e : Icc (-1 : ℝ) 1 ≃ᵐ Icc (-1 : ℝ) 1 :=
    { toEquiv :=
        { toFun := negX
          invFun := negX
          left_inv := by
            intro x
            apply Subtype.ext
            change -(-(x : ℝ)) = (x : ℝ)
            simp
          right_inv := by
            intro x
            apply Subtype.ext
            change -(-(x : ℝ)) = (x : ℝ)
            simp }
      measurable_toFun := hn.measurable
      measurable_invFun := hn.measurable }

  have hem : Measure.map e (μ.comap Subtype.val) = μ.comap Subtype.val := by
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    erw [Measure.map_map measurable_subtype_coe e.measurable]
    change Measure.map (fun x : Icc (-1 : ℝ) 1 => -(x : ℝ)) (μ.comap Subtype.val) =
      Measure.map Subtype.val (μ.comap Subtype.val)
    erw [← Measure.map_map measurable_neg measurable_subtype_coe]
    simp only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hxμ, Measure.map_neg_eq_self]
  let ep := e.prodCongr (MeasurableEquiv.refl ℝ)
  have hm : Measure.map ep ((μ.comap Subtype.val).prod ν) =
      (μ.comap Subtype.val).prod ν := by
    change Measure.map (Prod.map e id) ((μ.comap Subtype.val).prod ν) = _
    rw [← Measure.map_prod_map _ _ e.measurable measurable_id, hem, Measure.map_id]
  have hF : (fun v => F (ep v)) =ᵐ[(μ.comap Subtype.val).prod ν] fun v => -F v := by
    filter_upwards [] with v
    change eval (![-(v.1 : ℝ), Real.sqrt (1-(-(v.1 : ℝ))^2)*v.2]) u *
      eval (![-(v.1 : ℝ), Real.sqrt (1-(-(v.1 : ℝ))^2)*v.2]) (S.polynomial n k) *
        eval (![-(v.1 : ℝ), Real.sqrt (1-(-(v.1 : ℝ))^2)*v.2]) (S.polynomial m j) = -F v
    erw [hu v.1 v.2, S.eval_polynomial_neg_outer hxμ hμ hpos n k (v.1 : ℝ) v.2 v.1.property,
      S.eval_polynomial_neg_outer hxμ hμ hpos m j (v.1 : ℝ) v.2 v.1.property]
    calc
      _ = ((-1 : ℝ)^(n-k)*(-1 : ℝ)^(m-j))*F v := by dsimp [F,diskCoordinates]; ring
      _ = _ := by rw [parity_sign_mul hnm]; ring
  have he := integral_map_equiv (μ := (μ.comap Subtype.val).prod ν) ep F
  rw [hm, integral_congr_ae hF, integral_neg] at he
  linarith

end MvPolynomial.CartesianDiskSystem
