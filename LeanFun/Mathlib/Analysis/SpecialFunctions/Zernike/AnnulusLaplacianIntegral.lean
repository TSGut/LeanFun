/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergyPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPolynomialSpan
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-! # Vanishing integrated Laplacians on an annulus
A squared boundary factor removes both the value and normal-derivative boundary
terms. Angular separation reduces the proof to the polynomial fundamental theorem
of calculus. This supplies the boundary step for polynomial Green identities.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The Cartesian Laplacian as a linear map on polynomials. -/
def diskLaplacianLinearMap : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ where
  toFun := diskLaplacian
  map_add' p z := by simp [diskLaplacian, map_add]; abel
  map_smul' a p := by simp [diskLaplacian, smul_add]

/-- The polynomial dot product of the two Cartesian gradients. -/
def diskGradientProduct (p z : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  pderiv 0 p * pderiv 0 z + pderiv 1 p * pderiv 1 z

/-- The Cartesian Laplacian product rule, with its cross-gradient term explicit. -/
theorem diskLaplacian_mul (p z : MvPolynomial (Fin 2) ℝ) :
    diskLaplacian (p*z) = diskLaplacian p*z + p*diskLaplacian z + 2*diskGradientProduct p z := by
  simp only [diskLaplacian, diskGradientProduct, pderiv_mul, map_add]
  ring

/-- The integral of a radial-sector Laplacian consists only of the constant-mode boundary flux. -/
theorem integral_diskLaplacian_diskRadialLift {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    ∫ v, eval v (diskLaplacian (diskRadialLift u p m)) ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 =
      if u = false ∧ m = 0 then
        4*Real.pi*(p.derivative.eval 1-q*p.derivative.eval q) else 0 := by
  have hone : diskRadialLift false (1 : Polynomial ℝ) 0 = 1 := by
    simp [diskRadialLift, diskHarmonics]
  have he (f : MvPolynomial (Fin 2) ℝ) :
      (∫ v, eval v f ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) =
        integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) f (diskRadialLift false 1 0) (h := (hasFiniteMoments_zernikeAnnulusMeasure hq (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    simp [hone, integralInner]
  rw [he]
  simp only [diskLaplacian_diskRadialLift]
  rw [integralInner_annulusRadialLift hq (by norm_num) (by norm_num)]
  by_cases h : u = false ∧ m = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, Real.rpow_zero, Nat.cast_zero, zero_add, pow_zero,
      Polynomial.eval_one, mul_one, one_mul, zernikeAngularNormSq, Bool.false_eq_true]
    have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := q) (b := 1) (fun x _ ↦ (Polynomial.X*p.derivative).hasDerivAt x)
      ((Polynomial.X*p.derivative).derivative.continuous.intervalIntegrable q 1)
    have hi : (∫ s in q..1,
        (4*(Polynomial.X*p.derivative.derivative+p.derivative)).eval s) =
        4*(p.derivative.eval 1-q*p.derivative.eval q) := by
      calc
        _ = (4 : ℝ) * ∫ s in q..1, (Polynomial.X*p.derivative).derivative.eval s := by
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

/-- Multiplication by the squared physical boundary factor stays in the same radial sector. -/
theorem annulusBoundaryWeight_sq_mul_radialLift (q : ℝ) (u : Bool) (m : ℕ)
    (p : Polynomial ℝ) :
    annulusBoundaryWeight q ^ 2 * diskRadialLift u p m =
      diskRadialLift u (((1-Polynomial.X)*(Polynomial.X-Polynomial.C q))^2*p) m := by
  simp only [diskRadialLift, annulusBoundaryWeight, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_one,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  ring

/-- The squared boundary factor annihilates the integrated Laplacian in every angular sector. -/
theorem integral_diskLaplacian_boundary_sq_annulusLift {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    ∫ v, eval v (diskLaplacian (annulusBoundaryWeight q ^ 2 * annulusLift ⟨q,ne_of_lt hq.2⟩ u m p))
      ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 = 0 := by
  change (∫ v, eval v (diskLaplacian (annulusBoundaryWeight q ^ 2 * diskRadialLift u _ m))
    ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0) = 0
  rw [annulusBoundaryWeight_sq_mul_radialLift, integral_diskLaplacian_diskRadialLift hq]
  split_ifs <;> simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

/-- Any Cartesian polynomial with a squared boundary factor has zero integrated Laplacian. -/
theorem integral_diskLaplacian_boundary_sq {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v (diskLaplacian (annulusBoundaryWeight q ^ 2 * p))
      ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 = 0 := by
  let μ := zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0
  let hμ := hasFiniteMoments_zernikeAnnulusMeasure hq
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  let L : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    ((integralBilinForm μ hμ).flip 1).comp
      (diskLaplacianLinearMap.comp (LinearMap.mulLeft ℝ (annulusBoundaryWeight q ^ 2)))
  have he (z : MvPolynomial (Fin 2) ℝ) : L z =
      ∫ v, eval v (diskLaplacian (annulusBoundaryWeight q ^ 2*z)) ∂μ := by
    simp [L, integralBilinForm, integralInner, diskLaplacianLinearMap]
  have hk : LinearMap.ker L = ⊤ := eq_top_of_annulusLift_mem hq _ (by
    intro u m z
    rw [LinearMap.mem_ker, he]
    exact integral_diskLaplacian_boundary_sq_annulusLift hq u m z)
  have hp : p ∈ LinearMap.ker L := by rw [hk]; trivial
  rw [LinearMap.mem_ker, he] at hp
  exact hp

end MvPolynomial
