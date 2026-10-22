/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusGreen
import Mathlib.Tactic.LinearCombination

/-! # Radial divergence on the annulus
The polynomial divergence of the radial vector field has only a constant-sector
boundary flux. This supplies a mode-independent Poincaré estimate for the annular
Dirichlet trials of Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace MvPolynomial

/-- The Euler derivative in the two Cartesian variables. -/
def diskEuler : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ :=
  (LinearMap.mulLeft ℝ (X 0)).comp (pderiv 0).toLinearMap +
    (LinearMap.mulLeft ℝ (X 1)).comp (pderiv 1).toLinearMap

/-- The Euler derivative obeys the product rule. -/
theorem diskEuler_mul (p z : MvPolynomial (Fin 2) ℝ) :
    diskEuler (p*z) = diskEuler p*z+p*diskEuler z := by
  simp [diskEuler]
  ring

/-- Euler differentiation preserves radial angular sectors. -/
theorem diskEuler_diskRadialLift (u : Bool) (p : Polynomial ℝ) (m : ℕ) :
    diskEuler (diskRadialLift u p m) =
      diskRadialLift u (2*Polynomial.X*p.derivative+(m : Polynomial ℝ)*p) m := by
  have h (z : MvPolynomial (Fin 2) ℝ)
      (hz : X 0*pderiv 0 z+X 1*pderiv 1 z = (m : MvPolynomial (Fin 2) ℝ)*z) :
      diskEuler (p.eval₂ C (X 0^2+X 1^2)*z) =
        (2*Polynomial.X*p.derivative+(m : Polynomial ℝ)*p).eval₂ C (X 0^2+X 1^2)*z := by
    change X 0*pderiv 0 (p.eval₂ C (X 0^2+X 1^2)*z) +
      X 1*pderiv 1 (p.eval₂ C (X 0^2+X 1^2)*z) = _
    simp only [pderiv_mul, pderiv_zero_radial, pderiv_one_radial]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_natCast]
    linear_combination p.eval₂ C (X 0^2+X 1^2)*hz
  cases u <;> simp only [diskRadialLift, Bool.false_eq_true, ↓reduceIte]
  · exact h _ (euler_diskHarmonics m).1
  · exact h _ (euler_diskHarmonics m).2

/-- The divergence of `v ↦ v * p(v)` as a polynomial linear map. -/
def diskRadialDivergence : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ :=
  (2 : ℝ) • LinearMap.id + diskEuler

/-- Radial divergence reduces to a first-order radial expression. -/
theorem diskRadialDivergence_diskRadialLift (u : Bool) (p : Polynomial ℝ) (m : ℕ) :
    diskRadialDivergence (diskRadialLift u p m) =
      diskRadialLift u (2*(Polynomial.X*p.derivative+p)+(m : Polynomial ℝ)*p) m := by
  change (2 : ℝ) • diskRadialLift u p m + diskEuler (diskRadialLift u p m) = _
  rw [diskEuler_diskRadialLift]
  rw [show (2 : ℝ) = 1+1 by norm_num, add_smul, one_smul]
  cases u <;> simp [diskRadialLift, Polynomial.eval₂_add, Polynomial.eval₂_mul] <;> ring

/-- Only the constant angular sector contributes to the integrated radial divergence. -/
theorem integral_diskRadialDivergence_diskRadialLift {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    ∫ v, eval v (diskRadialDivergence (diskRadialLift u p m)) ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 =
      if u = false ∧ m = 0 then 2*Real.pi*(p.eval 1-q*p.eval q) else 0 := by
  have hone : diskRadialLift false (1 : Polynomial ℝ) 0 = 1 := by
    simp [diskRadialLift, diskHarmonics]
  have he (f : MvPolynomial (Fin 2) ℝ) :
      (∫ v, eval v f ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) =
        integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) f (diskRadialLift false 1 0) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    simp [hone, integralInner]
  rw [he]
  simp only [diskRadialDivergence_diskRadialLift]
  rw [integralInner_annulusRadialLift hq (by norm_num) (by norm_num)]
  by_cases h : u = false ∧ m = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, Real.rpow_zero, Nat.cast_zero, pow_zero,
      Polynomial.eval_one, mul_one, one_mul, zernikeAngularNormSq, Bool.false_eq_true,
      zero_mul, add_zero]
    have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := q) (b := 1) (fun x _ ↦ (Polynomial.X*p).hasDerivAt x)
      ((Polynomial.X*p).derivative.continuous.intervalIntegrable q 1)
    have hi : (∫ s in q..1, (2*(Polynomial.X*p.derivative+p)).eval s) =
        2*(p.eval 1-q*p.eval q) := by
      calc
        _ = (2 : ℝ) * ∫ s in q..1, (Polynomial.X*p).derivative.eval s := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s hs
          simp [Polynomial.derivative_mul]
          ring
        _ = _ := by rw [hd]; simp
    rw [intervalIntegral.integral_of_le hq.2.le, ← restrict_Ioo_eq_restrict_Ioc,
      ← integral_subtype_comap measurableSet_Ioo] at hi
    have hh := congrArg (fun a : ℝ ↦ (1/2)*a*(2*Real.pi)) hi
    convert hh using 1
    ring
  · simp [h]

/-- A squared boundary factor annihilates radial divergence flux. -/
theorem integral_diskRadialDivergence_boundary_sq {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v (diskRadialDivergence (annulusBoundaryWeight q ^ 2*p))
      ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 = 0 := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let L : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    ((integralBilinForm μ hμ).flip 1).comp
      (diskRadialDivergence.comp (LinearMap.mulLeft ℝ (annulusBoundaryWeight q ^ 2)))
  have he (z : MvPolynomial (Fin 2) ℝ) : L z =
      ∫ v, eval v (diskRadialDivergence (annulusBoundaryWeight q ^ 2*z)) ∂μ := by
    simp [L, integralBilinForm, integralInner]
  have hk : LinearMap.ker L = ⊤ := eq_top_of_annulusLift_mem hq _ (by
    intro u m z
    rw [LinearMap.mem_ker, he]
    change (∫ v, eval v (diskRadialDivergence
      (annulusBoundaryWeight q ^ 2 * diskRadialLift u _ m)) ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) = 0
    rw [annulusBoundaryWeight_sq_mul_radialLift, integral_diskRadialDivergence_diskRadialLift hq]
    split_ifs <;> simp)
  have hp : p ∈ LinearMap.ker L := by rw [hk]; trivial
  rw [LinearMap.mem_ker, he] at hp
  exact hp

end MvPolynomial
