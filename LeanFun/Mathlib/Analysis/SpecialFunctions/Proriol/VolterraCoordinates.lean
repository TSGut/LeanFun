/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionClosedForm
public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.OperatorClenshaw

/-! # Full finite Proriol coordinates for Volterra assembly

The signed reflected synthesis is an equivalence on finitely supported vectors.
Kernel multiplication is conjugated through this equivalence, with reflection
of the kernel included. Reference: Gutleb–Olver, Sections 3.1–3.2.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial

/-- Every polynomial has finite signed reflected Proriol coordinates. -/
theorem proriolVolterraSynthesis_surjective : Function.Surjective proriolVolterraSynthesis := by
  intro p
  let q := triangleReflect p
  let N := q.totalDegree
  let b := proriolDegreeBasis (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) N
  let v : restrictTotalDegree (Fin 2) ℝ N :=
    ⟨q, (mem_restrictTotalDegree (Fin 2) N q).mpr le_rfl⟩
  refine ⟨proriolVolterraCoordinateTransport N (b.repr v), ?_⟩
  rw [proriolVolterraSynthesis_transport]
  have h := congrArg (fun t : restrictTotalDegree (Fin 2) ℝ N ↦
    (t : MvPolynomial (Fin 2) ℝ)) (b.linearCombination_repr v)
  have hf : (fun d ↦ (b d : MvPolynomial (Fin 2) ℝ)) =
      (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦
        proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) := by
    funext d
    exact proriolDegreeBasis_apply _ _ _ N d
  change (↑((b.repr v).sum (fun i a ↦ a • b i)) : MvPolynomial (Fin 2) ℝ) = q at h
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← hf, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  rw [h]
  exact triangleReflect_involutive p

/-- Coordinates for the existing signed reflected synthesis, with no cutoff choice. -/
def proriolVolterraEquiv : ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) ≃ₗ[ℝ]
    MvPolynomial (Fin 2) ℝ :=
  LinearEquiv.ofBijective proriolVolterraSynthesis
    ⟨proriolVolterraSynthesis_injective, proriolVolterraSynthesis_surjective⟩

/-- Exact inner extension on finite shifted Jacobi input coefficients. -/
def proriolExtensionMap : (ℕ →₀ ℝ) →ₗ[ℝ] ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) :=
  proriolVolterraEquiv.symm.toLinearMap.comp
    (triangleExtendY.toLinearMap.comp (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)))

/-- Each extension column is the already established finite coordinate vector. -/
theorem proriolExtensionMap_single (n : ℕ) :
    proriolExtensionMap (Finsupp.single n 1) =
      proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
        (natDegree_shiftedJacobi_le 1 0 n) := by
  apply proriolVolterraEquiv.injective
  change proriolVolterraEquiv (proriolVolterraEquiv.symm _) = _
  rw [proriolVolterraEquiv.apply_symm_apply]
  change triangleExtendY (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
    (Finsupp.single n 1)) = proriolVolterraSynthesis _
  simpa using (proriolVolterraSynthesis_extension n (shiftedJacobi 1 0 n)
    (natDegree_shiftedJacobi_le 1 0 n)).symm

/-- Reflected kernel multiplication as an algebra homomorphism on finite coordinates. -/
def proriolKernelMap : MvPolynomial (Fin 2) ℝ →ₐ[ℝ]
    Module.End ℝ ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) :=
  (proriolVolterraEquiv.symm.conjAlgEquiv ℝ).toAlgHom.comp
    ((Algebra.lmul ℝ (MvPolynomial (Fin 2) ℝ)).comp triangleReflect)

/-- Kernel multiplication reconstructs the reflected polynomial product exactly. -/
theorem proriolVolterraSynthesis_kernelMap (K : MvPolynomial (Fin 2) ℝ)
    (c : (Σ n : ℕ, Fin (n+1)) →₀ ℝ) :
    proriolVolterraSynthesis (proriolKernelMap K c) =
      triangleReflect K * proriolVolterraSynthesis c := by
  change proriolVolterraEquiv (proriolVolterraEquiv.symm _) = _
  exact proriolVolterraEquiv.apply_symm_apply _

/-- The core coefficient operator: extension, kernel multiplication, then marginal. -/
def volterraProriolCoefficients (K : MvPolynomial (Fin 2) ℝ) :
    (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  proriolMarginalCoefficients.comp ((proriolKernelMap K).comp proriolExtensionMap)

/-- The endpoint factor and output reflection are retained explicitly. -/
theorem volterraProriolCoefficients_exact (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) (x : ℝ) :
    x * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
      (volterraProriolCoefficients K c)).eval (1-x) =
      ∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) K *
        (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c).eval y := by
  have h := eval_proriolMarginalPolynomial (proriolKernelMap K (proriolExtensionMap c)) (1-x)
  rw [proriolVolterraSynthesis_kernelMap] at h
  have he : proriolVolterraSynthesis (proriolExtensionMap c) =
      triangleExtendY (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c) :=
    proriolVolterraEquiv.apply_symm_apply _
  rw [he] at h
  change _ = volterraPolynomial K _ x at h
  rw [volterraPolynomial_apply] at h
  simpa [proriolMarginalPolynomial, volterraProriolCoefficients] using h

end MvPolynomial
