/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Positive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Support

/-!
# Finite Gram factors between Cartesian systems

Connection entries are coordinates in the target orthonormal basis. Therefore
every complete degree section has exactly the same entrywise support as the
integral coefficients, and its transpose product is the modified Gram matrix.
Reference: Gutleb–Olver–Slevinsky, Gram and connection factorizations.
-/

@[expose] public section
open MeasureTheory Set Module
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν μ' ν' : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    (hx' : ∀ᵐ x ∂μ', x ∈ Icc (-1 : ℝ) 1) (hz' : ∀ᵐ z ∂ν', z ∈ Icc (-1 : ℝ) 1)

/-- The exact finite connection in exponent-pair indices, ordered by degree then inner index. -/
noncomputable def connectionMatrix (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ :=
  (T.degreeBasis hx' hz' N).toMatrix (S.degreeBasis hx hz N)

/-- Finite sections use the same entries as the integral connection. -/
theorem connectionMatrix_apply (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    S.connectionMatrix T hx hz hx' hz' N i j =
      S.connectionEntry T (j.1 0+j.1 1) (j.1 1) (i.1 0+i.1 1) (i.1 1) := by
  change (T.degreeBasis hx' hz' N).repr (S.degreeBasis hx hz N j) i = _
  rw [T.degreeBasis_repr hx' hz']
  simp only [S.degreeBasis_apply]
  exact integralInner_comm _ _ _

/-- The finite Cartesian connection factors the target-measure Gram matrix exactly. -/
theorem integralGram_eq_connectionMatrix_transpose_mul (N : ℕ)
    [Fintype {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}] :
    integralGram (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν'))
      (fun i => (S.degreeBasis hx hz N i : MvPolynomial (Fin 2) ℝ)) =
      (S.connectionMatrix T hx hz hx' hz' N).transpose *
        S.connectionMatrix T hx hz hx' hz' N := by
  classical
  exact integralGram_eq_transpose_toMatrix_mul _
    (hasFiniteMoments_cartesianDiskMeasure hx' hz')
    (T.hasPositiveDefiniteIntegral hx' hz') _ _ (T.integralGram_degreeBasis hx' hz' N)

end MvPolynomial.CartesianDiskSystem
