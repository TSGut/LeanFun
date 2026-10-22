/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.AlphaConnection
public import LeanFun.Mathlib.Analysis.Polynomial.RationalIdentity
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Universal Jacobi connection identities

The explicit connection coefficients are polynomial after clearing denominators.
Equality on the real orthogonality range determines the formal rational-parameter
identity, which then specializes to every commutative rational algebra.
Reference: DLMF 18.18.14.
-/

public section
namespace Polynomial

/-- The explicit one-parameter Jacobi connection formula with denominators
cleared, valid even at degenerate parameters in every commutative rational algebra
(DLMF 18.18.14). -/
theorem jacobiAlphaConnectionScale_smul {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β γ : R) (n : ℕ) :
    jacobiAlphaConnectionScale α β n • jacobi γ β n =
      ∑ k : Fin (n + 1), jacobiAlphaConnectionCleared α β γ n k • jacobi α β k := by
  let a : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 0
  let b : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 1
  let c : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 2
  have hid : jacobiAlphaConnectionScale a b n • jacobi c b n =
      ∑ k : Fin (n + 1), jacobiAlphaConnectionCleared a b c n k • jacobi a b k := by
    apply eq_of_map_eval₂_eq_on (fun _ ↦ Set.Ioi (-1)) (fun _ ↦ Set.Ioi_infinite _)
    intro v hv
    change (jacobiAlphaConnectionScale a b n • jacobi c b n).map
      (MvPolynomial.aeval v).toRingHom =
      (∑ k : Fin (n + 1), jacobiAlphaConnectionCleared a b c n k • jacobi a b k).map
        (MvPolynomial.aeval v).toRingHom
    simp only [Polynomial.map_smul, Polynomial.map_sum, map_jacobi]
    simpa [a, b, c] using
      jacobiAlphaConnectionScale_smul_of_neg_one_lt (hv 0 (Set.mem_univ _))
        (hv 1 (Set.mem_univ _)) (v 2) n
  let f : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] R := MvPolynomial.aeval ![α, β, γ]
  have h := congrArg (Polynomial.map f.toRingHom) hid
  simp only [Polynomial.map_smul, Polynomial.map_sum, map_jacobi] at h
  simpa [f, a, b, c] using h

end Polynomial
