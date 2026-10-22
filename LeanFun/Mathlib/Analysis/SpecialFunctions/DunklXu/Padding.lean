/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.GramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.MultiplicationSection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.QuadraticPadding

/-!
# Exact two-block padding for disk quadratic products

The degree-N leading coefficients of two quadratic factors are exact when
coordinate multiplication is compressed at degree N+2. Equivalently, N blocks
of output use N+2 blocks of coordinates. The full quartic output need not fit
inside the padded section; only the stated leading coefficients are asserted.
Reference: Gutleb–Olver–Slevinsky, finite-section polynomial modifications.
-/

@[expose] public section
open Module MeasureTheory
namespace MvPolynomial

/-- Orthogonal degree truncation for the disk polynomial measure. -/
noncomputable def dunklXuDegreeProjection {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ := by
  let b := normalizedDunklXuDegreeBasis hβ N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  exact integralProjection (dunklXuDiskMeasure β) (hasFiniteMoments_dunklXuDiskMeasure hβ) b

/-- Degree truncation fixes every polynomial below its cutoff. -/
theorem dunklXuDegreeProjection_eq_self {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ N) :
    dunklXuDegreeProjection hβ N p = p := by
  classical
  have := Module.Finite.finite_basis (normalizedDunklXuDegreeBasis hβ N)
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  unfold dunklXuDegreeProjection
  exact integralProjection_eq_self_of_totalDegree_le _ _ N _
    (integralGram_normalizedDunklXuDegreeBasis hβ N) p hp

/-- Degree truncation is symmetric for the original disk pairing. -/
theorem dunklXuDegreeProjection_symmetric {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (dunklXuDegreeProjection hβ N p) q) =
      integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) p (dunklXuDegreeProjection hβ N q)) := by
  have := Module.Finite.finite_basis (normalizedDunklXuDegreeBasis hβ N)
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  unfold dunklXuDegreeProjection
  exact integralProjection_symmetric _ _ _ p q

/-- Raw leading coefficients of a quadratic product need only two extra degree blocks.
The choices (0,1,0), (0,0,1) give x²y²; (1,-1,-1), (2,-2,-1) give the second density. -/
theorem dunklXu_quadratic_product_padding {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (a b c d e f : ℝ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ t => t) ≤ N}) :
    (dunklXuBasis hβ).repr
      (compressedCoordinateQuadratic (dunklXuDegreeProjection hβ (N+2)) a b c
        (compressedCoordinateQuadratic (dunklXuDegreeProjection hβ (N+2)) d e f
          (dunklXuDisk β (j.1 0+j.1 1) (j.1 1))))
      ⟨i.1 0+i.1 1,⟨i.1 1,by omega⟩⟩ =
    dunklXuMultiplicationSection hβ (coordinateQuadratic a b c*coordinateQuadratic d e f) N i j := by
  let ii : Σ n : ℕ, Fin (n+1) := ⟨i.1 0+i.1 1,⟨i.1 1,by omega⟩⟩
  have hi : (normalizedDunklXuBasis hβ ii).totalDegree ≤ N := by
    rw [normalizedDunklXuBasis_apply]
    exact (totalDegree_smul_le _ _).trans
      ((totalDegree_dunklXuDisk_le β _ _ (by dsimp [ii]; omega)).trans
        (by simpa only [ii,sum_exponents_fin_two] using i.2))
  have hj : (dunklXuDisk β (j.1 0+j.1 1) (j.1 1)).totalDegree ≤ N :=
    (totalDegree_dunklXuDisk_le β _ _ (by omega)).trans
      (by simpa only [sum_exponents_fin_two] using j.2)
  have he := integralInner_compressed_quadratic_product (dunklXuDiskMeasure β)
    (hasFiniteMoments_dunklXuDiskMeasure hβ) (dunklXuDegreeProjection hβ (N+2))
    (dunklXuDegreeProjection_symmetric hβ (N+2)) N
    (dunklXuDegreeProjection_eq_self hβ (N+2)) a b c d e f
    (normalizedDunklXuBasis hβ ii) (dunklXuDisk β (j.1 0+j.1 1) (j.1 1)) hi hj
  rw [← normalizedDunklXuBasis_repr_eq_integralInner,
    ← normalizedDunklXuBasis_repr_eq_integralInner,normalizedDunklXuBasis_repr,
    normalizedDunklXuBasis_repr] at he
  exact mul_left_cancel₀ (dunklXuNorm_pos hβ ii.1 ii.2).ne' he

end MvPolynomial
