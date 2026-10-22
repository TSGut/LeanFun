/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModificationDensity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.QuadraticPadding
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Polynomial representatives of the two separated quadratic cases
The zero vertical coefficient is an outer modification; zero A+B is the
radius-squared modification times an even inner quadratic.
Reference: Cartesian disk separation, Dunkl--Xu Section 2.6.1.
-/

public section
open Polynomial
namespace MvPolynomial

/-- An outer quadratic is the l=0 separated disk modification. -/
theorem coordinateQuadratic_outer (A B : ℝ) :
    coordinateQuadratic A B 0 =
      cartesianDiskModification (Polynomial.C A + Polynomial.C B * Polynomial.X ^ 2) 1 0 := by
  simp [coordinateQuadratic, cartesianDiskModification, cartesianDiskPolynomial, diskLift]

/-- The boundary-vanishing case is the l=1 separated disk modification. -/
theorem coordinateQuadratic_radius (A C : ℝ) :
    coordinateQuadratic A (-A) C =
      cartesianDiskModification 1 (Polynomial.C A + Polynomial.C C * Polynomial.X ^ 2) 1 := by
  simp [coordinateQuadratic, cartesianDiskModification, cartesianDiskPolynomial, diskLift,
    Finset.sum_range_succ, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul]
  ring

end MvPolynomial
