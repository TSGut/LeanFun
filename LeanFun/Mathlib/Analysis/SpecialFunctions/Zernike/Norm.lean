/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Density
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.NormBounds

/-! # Standard norms and positive normalization of real Zernike modes
Reference: DLMF 18.37.1–2 and the orthonormal real convention in
MultivariateOrthogonalPolynomials.jl, disk.jl.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- The standard measure pairing is the auxiliary pairing times its explicit mass correction. -/
theorem integralInner_zernikeMeasure (a b : ℝ) (p q : MvPolynomial (Fin 2) ℝ)
    (hi : Integrable (fun x => eval x p*eval x q) (zernikeMeasure a b) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => eval x p*eval x q) (zernikeProductMeasure a b) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (zernikeMeasure a b) (IntegrablePair.of (zernikeMeasure a b) p q) =
      ((2 : ℝ)^(a+b+2))⁻¹ * integralInner (zernikeProductMeasure a b) (IntegrablePair.of (zernikeProductMeasure a b) p q) := by
  exact integral_zernikeMeasure a b ⟨_,hj⟩

/-- The precise standard squared norm, with the angular constant handled separately. -/
theorem integral_sq_zernikeMode {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k m : ℕ) :
    ∫ v, (eval v (zernikeMode s a b k m))^2 ∂zernikeMeasure a b =
      ((2 : ℝ)^(a+b+2))⁻¹ * (((2 : ℝ)^m)⁻¹ *
        (∫ x, (jacobi b (a+m) k).eval x^2 ∂jacobiMeasure b (a+m)) *
          zernikeAngularNormSq s m) := by
  rw [← integralInner_self _ _ (h := (hasFiniteMoments_zernikeMeasure ha hb).integrable_mul _ _),
    integralInner_zernikeMeasure a b _ _
      (hi := (hasFiniteMoments_zernikeMeasure ha hb).integrable_mul _ _)
      (hj := (hasFiniteMoments_zernikeProductMeasure ha hb).integrable_mul _ _),
    integralInner_zernikeMode_same_angular ha hb, Polynomial.integralInner_self]

/-- Every retained real angular mode has positive norm. The zero sine mode is excluded. -/
theorem integral_sq_zernikeMode_pos {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k m : ℕ) (hm : s=true → m≠0) :
    0 < ∫ v, (eval v (zernikeMode s a b k m))^2 ∂zernikeMeasure a b := by
  rw [integral_sq_zernikeMode ha hb]
  have hj := integral_sq_jacobi_pos hb
    (show -1 < a+(m : ℝ) by have := Nat.cast_nonneg (α := ℝ) m; linarith) k
  have hang : 0 < zernikeAngularNormSq s m := by
    cases s <;> simp only [zernikeAngularNormSq, Bool.false_eq_true, ↓reduceIte] at *
    · split <;> positivity
    · simp [hm, Real.pi_pos]
  positivity

/-- Orthogonality of all distinct retained real modes in the standard disk measure. -/
theorem integralInner_zernikeMode_eq_zero {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    {s t : Bool} {k m l n : ℕ} (hne : (s,k,m) ≠ (t,l,n)) :
    integralInner (zernikeMeasure a b) (IntegrablePair.of (zernikeMeasure a b) (zernikeMode s a b k m) (zernikeMode t a b l n)) = 0 := by
  rw [integralInner_zernikeMeasure a b _ _
    (hi := (hasFiniteMoments_zernikeMeasure ha hb).integrable_mul _ _)
    (hj := (hasFiniteMoments_zernikeProductMeasure ha hb).integrable_mul _ _)]
  by_cases hs : s=t
  · subst t
    by_cases hm : m=n
    · subst n
      rw [integralInner_zernikeMode_eq_zero_of_radial ha hb s (by aesop) m, mul_zero]
    · rw [integralInner_zernikeMode_eq_zero_of_angular ha hb (Or.inr hm), mul_zero]
  · rw [integralInner_zernikeMode_eq_zero_of_angular ha hb (Or.inl hs), mul_zero]

/-- Classical finite-square input for a real Zernike mode (DLMF 18.37). -/
structure ZernikeModeNormInput (s : Bool) (a b : ℝ) (k m : ℕ) : Prop where
  integrable : Integrable (fun v => (eval v (zernikeMode s a b k m))^2) (zernikeMeasure a b)

/-- Classical positive normalization data for a real Zernike mode (DLMF 18.37). -/
structure ZernikeModeNormalizationInput (s : Bool) (a b : ℝ) (k m : ℕ)
    : Prop extends ZernikeModeNormInput s a b k m where
  positive : 0 < ∫ v, (eval v (zernikeMode s a b k m))^2 ∂zernikeMeasure a b

/-- The full integrable parameter range supplies every finite mode norm. -/
theorem ZernikeModeNormInput.of_parameters {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k m : ℕ) : ZernikeModeNormInput s a b k m :=
  ⟨hasFiniteMoments_zernikeMeasure ha hb _⟩

/-- Retained real modes have positive classical normalization. -/
theorem ZernikeModeNormalizationInput.of_parameters {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k m : ℕ) (hm : s=true → m≠0) : ZernikeModeNormalizationInput s a b k m :=
  ⟨ZernikeModeNormInput.of_parameters ha hb s k m, integral_sq_zernikeMode_pos ha hb s k m hm⟩

/-- The nonnegative square-integral norm on its full classical domain. -/
noncomputable def zernikeModeNorm (s : Bool) (a b : ℝ) (k m : ℕ)
    (_d : ZernikeModeNormInput s a b k m) : ℝ :=
  Real.sqrt (∫ v, (eval v (zernikeMode s a b k m))^2 ∂zernikeMeasure a b)

/-- Normalize a positive-norm mode without changing either angular phase. -/
noncomputable def normalizedZernikeMode (s : Bool) (a b : ℝ) (k m : ℕ)
    (d : ZernikeModeNormalizationInput s a b k m) : MvPolynomial (Fin 2) ℝ :=
  (zernikeModeNorm s a b k m d.toZernikeModeNormInput)⁻¹ • zernikeMode s a b k m

/-- Squaring the classical norm recovers the square integral. -/
theorem zernikeModeNorm_sq (s : Bool) (a b : ℝ) (k m : ℕ)
    (d : ZernikeModeNormInput s a b k m) :
    (zernikeModeNorm s a b k m d)^2 =
      ∫ v, (eval v (zernikeMode s a b k m))^2 ∂zernikeMeasure a b :=
  Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))

/-- Every retained normalized mode has unit squared norm. -/
theorem integral_sq_normalizedZernikeMode {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k m : ℕ) (hm : s=true → m≠0) :
    ∫ v, (eval v (normalizedZernikeMode s a b k m
      (ZernikeModeNormalizationInput.of_parameters ha hb s k m hm)))^2 ∂zernikeMeasure a b = 1 := by
  have hp := integral_sq_zernikeMode_pos ha hb s k m hm
  have hM := hasFiniteMoments_zernikeMeasure ha hb
  rw [← integralInner_self _ _ (h := hM.integrable_mul _ _)]
  dsimp only [normalizedZernikeMode]
  rw [integralInner_smul_left (h := hM.integrable_mul _ _),
    integralInner_comm, integralInner_smul_left (h := hM.integrable_mul _ _), integralInner_self]
  dsimp [zernikeModeNorm]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']

end MvPolynomial
