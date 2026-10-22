/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System

/-!
# The existing Cartesian disk system as a Koornwinder system

This bridge retains the original disk polynomials and normalization.
Reference: Dunkl–Xu, §2.6.1.
-/

@[expose] public section
open MeasureTheory Polynomial Set
namespace Polynomial
/-- Internal identification of the disk shift on a supported real source. -/
theorem koornwinderOuterMeasure_disk_comap (μ : Measure ℝ)
    (_hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ) :
    koornwinderOuterMeasure (1-X^2) k (μ.comap Subtype.val) = diskOuterMeasure k (μ.comap Subtype.val) := rfl
end Polynomial
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ} (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)

/-- The Cartesian disk data satisfy the general separated interface. -/
noncomputable def toKoornwinderSystem (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    KoornwinderSystem (1-Polynomial.X^2)
      (fun x : Icc (-1 : ℝ) 1 => Real.sqrt (1-(x : ℝ)^2))
      (Measure.comap Subtype.val μ) ν where
  scale_nonneg := Filter.Eventually.of_forall (fun x => by
    simp only [Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X]
    nlinarith [x.property.1,x.property.2])
  outer := S.outer
  inner := S.inner
  lift k := diskLift k (S.inner k)
  lift_eval k := by
    apply Filter.Eventually.of_forall
    intro x z
    have hx := x.property
    apply eval_diskLift_scaled k (S.inner k) (by simp) (S.inner_parity k)
    · simpa only [koornwinderCoordinates, Matrix.cons_val_zero] using
        (Real.sq_sqrt (by nlinarith [hx.1,hx.2] : 0 ≤ 1-(x : ℝ)^2)).symm
    · rfl
  inner_orthogonal := S.inner_orthogonal
  outer_orthogonal k := by
    simpa only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx,koornwinderOuterMeasure_disk_comap μ hx,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_X] using S.outer_orthogonal_real k
  inner_leadingCoeff_pos := S.inner_leadingCoeff_pos
  outer_leadingCoeff_pos := S.outer_leadingCoeff_pos
  inner_norm k := by simpa only [Polynomial.integralInner_self] using S.inner_norm k
  outer_norm k n := by
    simpa only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx,Polynomial.integralInner,pow_two,koornwinderOuterMeasure_disk_comap μ hx,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X]
      using S.outer_norm_real k n

/-- The bridge uses exactly the existing Cartesian disk polynomial. -/
theorem toKoornwinderSystem_polynomial (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (n k : ℕ) :
    (S.toKoornwinderSystem hx).polynomial n k = S.polynomial n k := rfl

end MvPolynomial.CartesianDiskSystem
