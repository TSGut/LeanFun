/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Polynomial.Sequence

/-! # Polynomial sequences over fields
A degree-indexed sequence has unit leading coefficients over any field.
-/

public section
namespace Polynomial.Sequence

/-- Over a field, the leading-coefficient hypotheses of the sequence basis API
follow from the prescribed degrees (Szegő, Chapter 3). -/
theorem isUnit_leadingCoeff {K : Type*} [Field K] (P : Sequence K) (n : ℕ) :
    IsUnit (P n).leadingCoeff :=
  isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (P.ne_zero n))

end Polynomial.Sequence
