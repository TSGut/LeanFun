/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.RealSymbol

/-! # Uniform circle-symbol bounds for real Toeplitz operators

Reference: Böttcher–Silbermann, continuous-symbol Toeplitz compression.
-/

@[expose] public noncomputable section
namespace lp
/-- A uniform complex circle-symbol bound controls real Laurent quantization. -/
theorem norm_laurentToeplitz_le_circle {T : ℝ} [Fact (0 < T)]
    (p : LaurentPolynomial ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x : AddCircle T, ‖AddCircle.laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩)
      (AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom p) x‖ ≤ M) :
    ‖laurentToeplitz p‖ ≤ M := by
  let q := AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom p
  have hs : ‖AddCircle.laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩) q‖ ≤ M :=
    (ContinuousMap.norm_le _ hM).mpr hb
  have ht := (AddCircle.norm_continuousToeplitz_le
    (AddCircle.laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩) q)).trans hs
  rw [AddCircle.continuousToeplitz_laurentSymbol] at ht
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  rw [← complexifyL2.norm_map (laurentToeplitz p u), complexifyL2_laurentToeplitz]
  exact ((laurentToeplitz q).le_opNorm _).trans (by
    rw [complexifyL2.norm_map]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))
end lp
