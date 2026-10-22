/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusBasic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.AnnularLaplacian

/-! # Cartesian annular Laplacians from radial coefficient operators
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 14.
-/

public section
namespace Polynomial

/-- The affine radial change of variable transports the Cartesian radial Laplacian. -/
theorem annularLaplacian_comp (t : ℝ) (m : ℕ) (p : ℝ[X]) :
    4*(X*(p.comp (C t*(1-X))).derivative.derivative+
      ((m : ℝ[X])+1)*(p.comp (C t*(1-X))).derivative) =
    (semiclassicalJacobiAnnularLaplacianMap t m p).comp (C t*(1-X)) := by
  simp only [semiclassicalJacobiAnnularLaplacianMap_apply, derivative_comp,
    derivative_mul, derivative_C, derivative_sub, derivative_one, derivative_X,
    zero_mul, zero_sub, zero_add, derivative_neg,
    mul_comp, sub_comp, add_comp, natCast_comp, ofNat_comp, one_comp, C_comp, X_comp,
    map_mul, map_ofNat, map_add, map_natCast,
    map_one]
  ring

end Polynomial
namespace MvPolynomial
open Polynomial Set

/-- The Cartesian annular Laplacian preserves angular frequency and phase, with factor 4t. -/
theorem diskLaplacian_zernikeAnnulusMode {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (u : Bool) (k m : ℕ) :
    diskLaplacian (zernikeAnnulusMode hq ha hb u k m) =
      diskRadialLift u
        ((semiclassicalJacobiAnnularLaplacianMap (annulusParameter ⟨q,ne_of_lt hq.2⟩) m
          (semiclassicalJacobiSequence (one_lt_annulusParameter hq) ha hb m k)).comp
            (Polynomial.C (annulusParameter ⟨q,ne_of_lt hq.2⟩)*(1-Polynomial.X))) m := by
  rw [zernikeAnnulusMode, diskLaplacian_diskRadialLift, zernikeAnnulusRadial,
    annularLaplacian_comp]

end MvPolynomial
