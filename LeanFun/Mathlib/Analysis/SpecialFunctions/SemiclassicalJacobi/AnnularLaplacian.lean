/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.PartialWeightedOperator
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Derivative

/-! # The radial annular Laplacian on semiclassical coefficients
The scalar geometric factor 4t is separated from the product of the two
first-order operators. Reference: Papadopoulos–Gutleb–Slevinsky–Olver,
Proposition 14, equation (41).
-/

@[expose] public section
open Module
namespace Polynomial

/-- The radial differential expression after the annular affine change of variable. -/
noncomputable def semiclassicalJacobiAnnularLaplacianMap (t γ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (4*t) • (semiclassicalJacobiCWeightedDerivativeMap t γ).comp derivative

/-- Explicit polynomial action. -/
theorem semiclassicalJacobiAnnularLaplacianMap_apply (t γ : ℝ) (p : ℝ[X]) :
    semiclassicalJacobiAnnularLaplacianMap t γ p =
      C (4*t)*((C t-X)*p.derivative.derivative-C (γ+1)*p.derivative) := by
  simp [semiclassicalJacobiAnnularLaplacianMap, semiclassicalJacobiCWeightedDerivativeMap,
    smul_eq_C_mul]

/-- The actual Laplacian coefficient matrix raises both endpoint parameters twice. -/
noncomputable def semiclassicalJacobiAnnularLaplacian {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ)
    (hα2 : -1<(α+1)+1) (hβ2 : -1<(β+1)+1) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα2 hβ2 γ).toMatrix
    (fun n ↦ semiclassicalJacobiAnnularLaplacianMap t γ
      (semiclassicalJacobiSequence ht hα hβ γ n))

/-- Every finite expansion is acted on exactly, before or after coefficient conversion. -/
theorem semiclassicalJacobi_annularLaplacian_coefficientMap_exact {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ)
    (hα2 : -1<(α+1)+1) (hβ2 : -1<(β+1)+1) (v : ℕ →₀ ℝ) :
    (semiclassicalJacobiBasis ht hα2 hβ2 γ).repr.symm
      ((semiclassicalJacobiBasis ht hα hβ γ).coefficientMap
        (semiclassicalJacobiBasis ht hα2 hβ2 γ)
        (semiclassicalJacobiAnnularLaplacianMap t γ) v) =
      semiclassicalJacobiAnnularLaplacianMap t γ
        ((semiclassicalJacobiBasis ht hα hβ γ).repr.symm v) :=
  Basis.repr_symm_coefficientMap _ _ _ _

/-- Only the three upper diagonals n-1, n-2, n-3 can be nonzero. -/
theorem semiclassicalJacobiAnnularLaplacian_eq_zero {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ)
    (hα2 : -1<(α+1)+1) (hβ2 : -1<(β+1)+1) (n j : ℕ)
    (hgap : n≤j ∨ j+3<n) :
    semiclassicalJacobiAnnularLaplacian ht hα hβ γ hα2 hβ2 j n = 0 := by
  have hα1 : -1<α+1 := by linarith
  have hβ1 : -1<β+1 := by linarith
  let b := semiclassicalJacobiBasis ht hα hβ γ
  let c := semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)
  let d := semiclassicalJacobiBasis ht hα2 hβ2 γ
  let v := c.repr (b n).derivative
  have hz : (c.coefficientMap d (semiclassicalJacobiCWeightedDerivativeMap t γ) v) j = 0 := by
    rw [Basis.coefficientMap_apply]
    change ∑ k ∈ v.support, _ = 0
    apply Finset.sum_eq_zero
    intro k hk
    dsimp only
    by_cases h : n≤k ∨ k+2<n
    · have hv : v k=0 := by
        simpa only [v, b, c, semiclassicalJacobiBasis_apply, semiclassicalJacobiDerivative,
          Basis.toMatrix_apply] using
          semiclassicalJacobiDerivative_eq_zero ht hα hβ γ hα1 hβ1 n k h
      rw [hv, mul_zero]
    · have hm : d.toMatrix (fun k ↦ semiclassicalJacobiCWeightedDerivativeMap t γ (c k)) j k=0 := by
        simpa only [c, d, semiclassicalJacobiBasis_apply, semiclassicalJacobiCWeightedDerivative,
          Basis.toMatrix_apply] using
          semiclassicalJacobiCWeightedDerivative_eq_zero ht hα1 hβ1 γ hα2 hβ2 k j (by omega)
      rw [hm, zero_mul]
  rw [semiclassicalJacobiAnnularLaplacian, Basis.toMatrix_apply]
  simp only [semiclassicalJacobiAnnularLaplacianMap, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [← semiclassicalJacobiBasis_apply ht hα hβ γ n]
  change d.repr ((4*t) • semiclassicalJacobiCWeightedDerivativeMap t γ (b n).derivative) j=0
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have he : c.coefficientMap d (semiclassicalJacobiCWeightedDerivativeMap t γ) v =
      d.repr (semiclassicalJacobiCWeightedDerivativeMap t γ (b n).derivative) := by
    simp [Basis.coefficientMap, v]
  rw [← he, hz, mul_zero]

end Polynomial
