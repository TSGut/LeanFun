/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraCoordinates

/-! # Polynomial functional calculus and Clenshaw for Volterra kernel operators

The two coordinate multiplication operators commute because they are images of
commuting polynomials. Clenshaw is transported from that commutative polynomial
algebra, not asserted for arbitrary noncommuting endomorphisms.
Reference: Gutleb–Olver, Sections 3.1–3.2; Clenshaw (1955).
-/

public section
namespace MvPolynomial
open Polynomial

/-- Polynomial functional calculus commutes with the kernel operator map.
In particular this applies to either coordinate and to nested kernel expansions. -/
theorem proriolKernelMap_aeval (K : MvPolynomial (Fin 2) ℝ) (p : ℝ[X]) :
    proriolKernelMap (Polynomial.aeval K p) =
      Polynomial.aeval (proriolKernelMap K) p := by
  exact (Polynomial.aeval_algHom_apply proriolKernelMap K p).symm

/-- Coordinate operators commute on all finitely supported Proriol vectors. -/
theorem proriolKernelMap_X_commute (i j : Fin 2) :
    Commute (proriolKernelMap (X i)) (proriolKernelMap (X j)) := by
  show proriolKernelMap (X i) * proriolKernelMap (X j) = _
  rw [← map_mul, ← map_mul, mul_comm]

/-- A polynomial-valued backward recurrence evaluates its kernel multiplication
operator exactly. Coefficients may themselves be bivariate polynomials. -/
theorem proriolKernelMap_clenshaw (a b c p : ℕ → MvPolynomial (Fin 2) ℝ)
    (hp : ∀ k, p (k+2) = a k * p (k+1) + b k * p k) (N : ℕ) :
    Polynomial.clenshaw (fun k ↦ proriolKernelMap (a k))
      (fun k ↦ proriolKernelMap (b k)) (fun k ↦ proriolKernelMap (c k))
      (proriolKernelMap (p 0)) (proriolKernelMap (p 1)) N =
      proriolKernelMap (∑ k ∈ Finset.range N, c k * p k) := by
  have h := Polynomial.clenshaw_map
    (S := Module.End ℝ ((Σ n : ℕ, Fin (n+1)) →₀ ℝ)) proriolKernelMap.toRingHom a b c (p 0) (p 1) N
  rw [Polynomial.clenshaw_eq_sum a b c p hp N] at h
  exact h

/-- Inserting operator Clenshaw between extension and marginal gives the exact
finite Volterra coefficient map for the polynomial kernel expansion. -/
theorem volterraProriolCoefficients_clenshaw (a b c p : ℕ → MvPolynomial (Fin 2) ℝ)
    (hp : ∀ k, p (k+2) = a k * p (k+1) + b k * p k) (N : ℕ) :
    proriolMarginalCoefficients.comp
      ((Polynomial.clenshaw (fun k ↦ proriolKernelMap (a k))
        (fun k ↦ proriolKernelMap (b k)) (fun k ↦ proriolKernelMap (c k))
        (proriolKernelMap (p 0)) (proriolKernelMap (p 1)) N).comp proriolExtensionMap) =
      volterraProriolCoefficients (∑ k ∈ Finset.range N, c k * p k) := by
  rw [proriolKernelMap_clenshaw a b c p hp]
  rfl

end MvPolynomial
