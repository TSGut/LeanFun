/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Symbol
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.PositiveSymbol

/-! # Real Laurent operators and complex circle symbols

Complexification transfers the continuous-symbol lower bound to real
coefficient operators. Reference: Böttcher–Silbermann, Introduction to Large
Truncated Toeplitz Matrices.
-/

@[expose] public noncomputable section
open scoped InnerProductSpace
namespace lp

/-- Real square-summable coefficients embed isometrically into complex coefficients. -/
def complexifyL2 : lp (fun _ : ℕ ↦ ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 where
  toFun u := ⟨fun n ↦ (u n : ℂ), by
    apply Memℓp.of_norm
    simpa using (lp.memℓp u).norm⟩
  map_add' u v := by
    apply lp.ext
    funext n
    change ((u n+v n : ℝ) : ℂ) = (u n : ℂ)+(v n : ℂ)
    exact Complex.ofReal_add _ _
  map_smul' a u := by apply lp.ext; funext n; simp [Complex.real_smul]
  norm_map' u := by
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro n
      simp
    · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro n
      simp

/-- Complexification acts coefficientwise. -/
@[simp] theorem complexifyL2_apply (u : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    complexifyL2 u n = (u n : ℂ) := rfl

/-- Complexification intertwines the forward shifts. -/
theorem complexifyL2_forwardShift (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    complexifyL2 (forwardShiftL2 u) = forwardShiftL2 (complexifyL2 u) := by
  apply lp.ext
  funext n
  cases n <;> simp

/-- Complexification intertwines the backward shifts. -/
theorem complexifyL2_backwardShift (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    complexifyL2 (backwardShiftL2 u) = backwardShiftL2 (complexifyL2 u) := by
  apply lp.ext
  funext n
  simp

/-- Complexification intertwines every signed shift. -/
theorem complexifyL2_laurentShift (k : ℤ) (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    complexifyL2 (laurentShiftL2 k u) = laurentShiftL2 k (complexifyL2 u) := by
  have hS (n : ℕ) : complexifyL2 ((forwardShiftL2.toContinuousLinearMap ^ n) u) =
      (forwardShiftL2.toContinuousLinearMap ^ n) (complexifyL2 u) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change complexifyL2 (forwardShiftL2 ((forwardShiftL2.toContinuousLinearMap ^ n) u)) = _
      rw [complexifyL2_forwardShift, ih]
      rfl
  have hB (n : ℕ) : complexifyL2 ((backwardShiftL2 ^ n) u) =
      (backwardShiftL2 ^ n) (complexifyL2 u) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change complexifyL2 (backwardShiftL2 ((backwardShiftL2 ^ n) u)) = _
      rw [complexifyL2_backwardShift, ih]
      rfl
  cases k with
  | ofNat n => exact hS n
  | negSucc n => exact hB (n+1)

/-- Real Laurent quantization agrees with its complexification. -/
theorem complexifyL2_laurentToeplitz (p : LaurentPolynomial ℝ) (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    complexifyL2 (laurentToeplitz p u) =
      laurentToeplitz (AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom p) (complexifyL2 u) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, add_apply, hp, hq]
  | single k a =>
    rw [AddMonoidAlgebra.mapRingHom_single, laurentToeplitz_single, laurentToeplitz_single]
    simp only [smul_apply, map_smul, complexifyL2_laurentShift]
    apply lp.ext
    funext i
    change a • (laurentShiftL2 k (complexifyL2 u) i) =
      (Complex.ofRealHom a) • (laurentShiftL2 k (complexifyL2 u) i)
    simp only [Complex.real_smul, smul_eq_mul]
    rfl

/-- Complexification preserves the real part of the inner product. -/
theorem re_inner_complexifyL2 (u v : lp (fun _ : ℕ ↦ ℝ) 2) :
    (⟪complexifyL2 u, complexifyL2 v⟫_ℂ).re = ⟪u, v⟫_ℝ := by
  change RCLike.re (⟪complexifyL2 u, complexifyL2 v⟫_ℂ) = _
  rw [← real_inner_eq_re_inner ℂ]
  let := InnerProductSpace.rclikeToReal ℂ (lp (fun _ : ℕ ↦ ℂ) 2)
  exact complexifyL2.inner_map_map u v

/-- The circle-symbol lower bound also controls the real Laurent operator. -/
theorem inner_laurentToeplitz_le {T : ℝ} [Fact (0 < T)]
    (p : LaurentPolynomial ℝ) {a : ℝ}
    (hp : ∀ x : AddCircle T,
      a ≤ (AddCircle.laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩)
        (AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom p) x).re)
    (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    a * ‖u‖^2 ≤ ⟪u, laurentToeplitz p u⟫_ℝ := by
  have h := AddCircle.re_inner_continuousToeplitz_le _ hp (complexifyL2 u)
  rw [AddCircle.continuousToeplitz_laurentSymbol,
    ← complexifyL2_laurentToeplitz, re_inner_complexifyL2,
    complexifyL2.norm_map] at h
  exact h

end lp
