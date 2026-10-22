/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalShift
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.IntegerModes
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Angular separation and orthogonality of real Zernike modes
The auxiliary polar measure retains the Jacobi mass. Its radial shift contributes
2^(-m), with angular norms 2*pi for the constant and pi for positive frequencies.
Reference: DLMF 18.37.1–2, expressed in real sine/cosine modes.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- A real angular mode: false is cosine, true is sine. -/
noncomputable def zernikeAngular (s : Bool) (m : ℕ) (θ : ℝ) : ℝ :=
  if s then Real.sin (m*θ) else Real.cos (m*θ)

/-- Uniform access to the two real Cartesian polynomial modes. -/
noncomputable def zernikeMode (s : Bool) (a b : ℝ) (k m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  if s then zernikeSin a b k m else zernikeCos a b k m

/-- Squared angular norm, including the identically zero sine mode. -/
noncomputable def zernikeAngularNormSq (s : Bool) (m : ℕ) : ℝ :=
  if s then (if m=0 then 0 else Real.pi) else (if m=0 then 2*Real.pi else Real.pi)

/-- Angular orthogonality on a full turn, with both constant-mode conventions explicit. -/
theorem integral_zernikeAngular_mul (s t : Bool) (m n : ℕ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, zernikeAngular s m θ*zernikeAngular t n θ =
      if s=t ∧ m=n then zernikeAngularNormSq s m else 0 := by
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
  cases s <;> cases t
  · simpa [zernikeAngular, zernikeAngularNormSq] using Real.integral_cos_mode_mul_cos_mode m n
  · simp only [zernikeAngular, Bool.false_eq_true, ↓reduceIte]
    simp_rw [mul_comm (Real.cos _) (Real.sin _)]
    exact Real.integral_sin_mode_mul_cos_mode n m
  · simp [zernikeAngular, Real.integral_sin_mode_mul_cos_mode]
  · rw [show (fun θ ↦ zernikeAngular true m θ*zernikeAngular true n θ) =
        (fun θ ↦ Real.sin (m*θ)*Real.sin (n*θ)) from rfl,
        Real.integral_sin_mode_mul_sin_mode]
    by_cases h : m=n <;> by_cases hm : m=0 <;> simp [h, hm, zernikeAngularNormSq]

/-- Evaluation at every classical squared radius separates into radial and angular factors. -/
theorem eval_zernikeMode_coordinates (s : Bool) (a b : ℝ) (k m : ℕ)
    (r : NNReal) (θ : ℝ) :
    eval (zernikeCoordinates (r,θ)) (zernikeMode s a b k m) =
      (shiftedJacobi b (a+m) k).eval (r : ℝ) * Real.sqrt (r : ℝ)^m * zernikeAngular s m θ := by
  cases s <;> simp [zernikeMode, zernikeCoordinates, eval_zernikeCos_polar,
    eval_zernikeSin_polar, eval_shiftedJacobi, zernikeAngular]

/-- Every pairing separates into one radial integral and one angular pairing. -/
theorem integralInner_zernikeMode_separated {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s t : Bool) (k m l n : ℕ) :
    integralInner (zernikeProductMeasure a b) (IntegrablePair.of (zernikeProductMeasure a b)
      (zernikeMode s a b k m) (zernikeMode t a b l n)) =
      (∫ r : NNReal, (shiftedJacobi b (a+m) k).eval (r : ℝ) *
        (shiftedJacobi b (a+n) l).eval (r : ℝ) * Real.sqrt (r : ℝ)^(m+n)
        ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a)) *
      (if s=t ∧ m=n then zernikeAngularNormSq s m else 0) := by
  let := isFiniteMeasure_unitJacobiMeasure hb ha
  simp only [integralInner]
  change (∫ v, eval v (zernikeMode s a b k m) * eval v (zernikeMode t a b l n)
    ∂Measure.map zernikeCoordinates
      ((Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)))) = _
  have hc : Continuous (fun v ↦ eval v (zernikeMode s a b k m) * eval v (zernikeMode t a b l n)) :=
    (zernikeMode s a b k m).continuous_eval.mul (zernikeMode t a b l n).continuous_eval
  rw [integral_map continuous_zernikeCoordinates.measurable.aemeasurable hc.aestronglyMeasurable,
    ← integral_zernikeAngular_mul, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [eval_zernikeMode_coordinates, eval_zernikeMode_coordinates, pow_add]
  ring

/-- Different angular sectors are orthogonal independently of their radial degrees. -/
theorem integralInner_zernikeMode_eq_zero_of_angular {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    {s t : Bool} {k m l n : ℕ} (h : s ≠ t ∨ m ≠ n) :
    integralInner (zernikeProductMeasure a b) (IntegrablePair.of (zernikeProductMeasure a b) (zernikeMode s a b k m) (zernikeMode t a b l n)) = 0 := by
  rw [integralInner_zernikeMode_separated ha hb]
  have hn : ¬ (s=t ∧ m=n) := by tauto
  simp [hn]

/-- Within one angular sector, the radial pairing is exactly a shifted Jacobi pairing. -/
theorem integralInner_zernikeMode_same_angular {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) (k l m : ℕ) :
    integralInner (zernikeProductMeasure a b) (IntegrablePair.of (zernikeProductMeasure a b) (zernikeMode s a b k m) (zernikeMode s a b l m)) =
      ((2 : ℝ)^m)⁻¹ * Polynomial.integralInner (jacobiMeasure b (a+m)) (Polynomial.IntegrablePair.of (jacobiMeasure b (a+m)) (jacobi b (a+m) k) (jacobi b (a+m) l) (h := (hasFiniteMoments_jacobiMeasure hb (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).integrable_mul _ _)) * zernikeAngularNormSq s m := by
  rw [integralInner_zernikeMode_separated ha hb]
  simp only [and_self, ↓reduceIte]
  congr 1
  rw [← integralInner_shiftedJacobi b (a+m) k l
      (hi := (hasFiniteMoments_jacobiMeasure hb (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).integrable_mul _ _),
    Polynomial.integralInner,
    ← (integral_pow_unitJacobiMeasure_integrable b a m ⟨_,
      (hasFiniteMoments_unitJacobiMeasure hb
        (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).integrable_mul _ _⟩
      (by dsimp only; fun_prop)).2]
  calc
    _ = ∫ r : NNReal, (r : ℝ)^m *
        ((shiftedJacobi b (a+m) k).eval (r : ℝ) * (shiftedJacobi b (a+m) l).eval (r : ℝ))
        ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a) := by
      apply integral_congr_ae
      filter_upwards [] with r
      have hs : Real.sqrt (r : ℝ)^(m+m) = (r : ℝ)^m := by
        calc
          _ = (Real.sqrt (r : ℝ)^2)^m := by
            rw [← pow_mul]
            congr 1
            omega
          _ = _ := congrArg (fun x : ℝ ↦ x^m) (Real.sq_sqrt r.property)
      rw [hs]
      ring
    _ = _ := by
      change (∫ r : Ici (0 : ℝ), (r : ℝ)^m *
        ((shiftedJacobi b (a+m) k).eval (r : ℝ) * (shiftedJacobi b (a+m) l).eval (r : ℝ))
        ∂Measure.comap Subtype.val (unitJacobiMeasure b a)) = _
      rw [integral_subtype_comap (μ := unitJacobiMeasure b a) measurableSet_Ici
          (fun r : ℝ ↦ r^m * ((shiftedJacobi b (a+m) k).eval r * (shiftedJacobi b (a+m) l).eval r))]
      have hs : (unitJacobiMeasure b a).restrict (Ici (0 : ℝ)) = unitJacobiMeasure b a :=
        Measure.restrict_eq_self_of_ae_mem
          ((ae_mem_Icc_unitJacobiMeasure b a).mono (fun _ hx ↦ hx.1))
      rw [hs]

/-- Distinct radial degrees in the same angular sector are orthogonal. -/
theorem integralInner_zernikeMode_eq_zero_of_radial {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (s : Bool) {k l : ℕ} (hkl : k ≠ l) (m : ℕ) :
    integralInner (zernikeProductMeasure a b) (IntegrablePair.of (zernikeProductMeasure a b) (zernikeMode s a b k m) (zernikeMode s a b l m)) = 0 := by
  rw [integralInner_zernikeMode_same_angular ha hb, Polynomial.integralInner,
    integral_mul_jacobi_eq_zero hb (by have := Nat.cast_nonneg (α := ℝ) m; linarith) hkl]
  simp

end MvPolynomial
