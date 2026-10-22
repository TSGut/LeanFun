/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalIntegration

import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials as an orthogonal polynomial sequence

Reference: DLMF Table 18.3.1, https://dlmf.nist.gov/18.3.
-/

public section

namespace Polynomial.Chebyshev

/-- Mathlib's first-kind Chebyshev sequence satisfies the general orthogonality
predicate for its standard weight (DLMF Table 18.3.1). -/
theorem isOrthogonal_chebyshevTsequence :
    (chebyshevTsequence ℝ).IsOrthogonal classicalMeasureT where
  integrable m n := integrable_classicalMeasureT (by fun_prop)
  orthogonal m n hmn := by simpa only [chebyshevTsequence, hmn, ite_false] using (classicalMeasureT_orthogonality m n).2

end Polynomial.Chebyshev
