/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.InnerProductSpace.DegreeWeightedL2
public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientShift

/-! Coordinate operators on polynomially weighted sequences, OT §4.1. -/
@[expose] public noncomputable section
namespace lp
open ContinuousLinearMap Filter
open scoped Topology

/-- Conjugation of an operator by degree weighting. -/
def degreeWeightedTransport (s : ℕ)
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2) :
    DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  (degreeWeightedL2Isometry s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (degreeWeightedL2Isometry s).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinate formula for the transported operator. -/
theorem degreeWeightedTransport_apply (s : ℕ)
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (x : DegreeWeightedL2 s) (n : ℕ) :
    (degreeWeightedTransport s A x).1 n =
      A (degreeWeightedL2Equiv s x) n / ((n : ℂ) + 1)^s := rfl

/-- A bounded diagonal multiplier on weighted sequences. -/
def degreeWeightedDiagonal (s : ℕ) (d : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ n, ‖d n‖ ≤ C) :
    DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  degreeWeightedTransport s (coefficientDiagonal d hC hd)

/-- Diagonal transport preserves the coordinatewise multiplier. -/
theorem degreeWeightedDiagonal_apply (s : ℕ) (d : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ n, ‖d n‖ ≤ C) (x : DegreeWeightedL2 s) (n : ℕ) :
    (degreeWeightedDiagonal s d hC hd x).1 n = d n * x.1 n := by
  change (d n * (((n : ℂ) + 1)^s * x.1 n)) / ((n : ℂ) + 1)^s = _
  field_simp

/-- Isometric transport preserves compactness. -/
theorem isCompactOperator_degreeWeightedTransport (s : ℕ)
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hA : IsCompactOperator A) : IsCompactOperator (degreeWeightedTransport s A) := by
  unfold degreeWeightedTransport
  exact (hA.comp_clm (degreeWeightedL2Isometry s).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (degreeWeightedL2Isometry s).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- A diagonal tending to zero is compact in the weighted norm. -/
theorem isCompactOperator_degreeWeightedDiagonal (s : ℕ) (d : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ n, ‖d n‖ ≤ C) (hlim : Tendsto d atTop (𝓝 0)) :
    IsCompactOperator (degreeWeightedDiagonal s d hC hd) :=
  isCompactOperator_degreeWeightedTransport s _
    (isCompactOperator_coefficientDiagonal d hC hd hlim)

/-- Weight ratio for the backward shift. -/
def degreeWeightLeftRatio (s n : ℕ) : ℂ :=
  ((((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ s : ℝ)

/-- Backward weight ratios are at most one. -/
theorem norm_degreeWeightLeftRatio_le (s n : ℕ) :
    ‖degreeWeightLeftRatio s n‖ ≤ 1 := by
  rw [degreeWeightLeftRatio, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 (by linarith))

/-- Weight ratio for the forward shift. -/
def degreeWeightRightRatio (s n : ℕ) : ℂ :=
  ((((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ s : ℝ)

/-- Forward weight ratios are bounded by two to the weight exponent. -/
theorem norm_degreeWeightRightRatio_le (s n : ℕ) :
    ‖degreeWeightRightRatio s n‖ ≤ (2 : ℝ)^s := by
  rw [degreeWeightRightRatio, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Backward shift in the weighted coefficient norm. -/
def degreeWeightedShiftLeft (s : ℕ) : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  degreeWeightedTransport s
    ((coefficientDiagonal (degreeWeightLeftRatio s) zero_le_one
      (norm_degreeWeightLeftRatio_le s)).comp coefficientShiftLeft)

/-- Forward shift in the weighted coefficient norm. -/
def degreeWeightedShiftRight (s : ℕ) : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  degreeWeightedTransport s
    (coefficientShiftRight.comp (coefficientDiagonal (degreeWeightRightRatio s)
      (by positivity) (norm_degreeWeightRightRatio_le s)))

/-- Backward shift removes the first coordinate. -/
theorem degreeWeightedShiftLeft_apply (s : ℕ) (x : DegreeWeightedL2 s) (n : ℕ) :
    (degreeWeightedShiftLeft s x).1 n = x.1 (n + 1) := by
  rw [degreeWeightedShiftLeft, degreeWeightedTransport_apply, comp_apply,
    coefficientDiagonal_apply, coefficientShiftLeft_apply]
  change (degreeWeightLeftRatio s n * ((((n + 1 : ℕ) : ℂ) + 1)^s * x.1 (n + 1))) /
    ((n : ℂ) + 1)^s = _
  simp only [degreeWeightLeftRatio]
  push_cast
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
  rw [div_pow]
  field_simp

/-- Forward shift inserts a zero coordinate. -/
theorem degreeWeightedShiftRight_zero (s : ℕ) (x : DegreeWeightedL2 s) :
    (degreeWeightedShiftRight s x).1 0 = 0 := by
  rw [degreeWeightedShiftRight, degreeWeightedTransport_apply, comp_apply,
    coefficientShiftRight_zero, zero_div]

/-- Forward shift moves each coordinate one place to the right. -/
theorem degreeWeightedShiftRight_succ (s : ℕ) (x : DegreeWeightedL2 s) (n : ℕ) :
    (degreeWeightedShiftRight s x).1 (n + 1) = x.1 n := by
  rw [degreeWeightedShiftRight, degreeWeightedTransport_apply, comp_apply,
    coefficientShiftRight_succ, coefficientDiagonal_apply]
  change (degreeWeightRightRatio s n * (((n : ℂ) + 1)^s * x.1 n)) /
    (((n + 1 : ℕ) : ℂ) + 1)^s = _
  simp only [degreeWeightRightRatio]
  push_cast
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
  rw [div_pow]
  field_simp

/-- Transport is conjugation by the degree-weighting isometry. -/
theorem degreeWeightedTransport_equiv (s : ℕ)
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (x : DegreeWeightedL2 s) :
    degreeWeightedL2Isometry s (degreeWeightedTransport s A x) =
      A (degreeWeightedL2Isometry s x) :=
  (degreeWeightedL2Isometry s).apply_symm_apply _

/-- Truncation to the first N weighted coordinates. -/
def degreeWeightedProjection (s N : ℕ) : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  degreeWeightedTransport s (coefficientProjection N)

@[simp] theorem degreeWeightedProjection_apply (s N : ℕ)
    (x : DegreeWeightedL2 s) (i : ℕ) :
    (degreeWeightedProjection s N x).1 i = if i < N then x.1 i else 0 := by
  rw [degreeWeightedProjection, degreeWeightedTransport_apply, coefficientProjection_apply]
  split_ifs
  · change (((i : ℂ) + 1)^s * x.1 i) / ((i : ℂ) + 1)^s = _
    field_simp
  · exact zero_div _

/-- Truncation is contractive in every degree-weighted norm. -/
theorem norm_degreeWeightedProjection_le (s N : ℕ) : ‖degreeWeightedProjection s N‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ← (degreeWeightedL2Isometry s).norm_map (degreeWeightedProjection s N x),
    degreeWeightedProjection, degreeWeightedTransport_equiv]
  calc
    ‖coefficientProjection N (degreeWeightedL2Isometry s x)‖ ≤
        ‖coefficientProjection (𝕜 := ℂ) N‖ * ‖degreeWeightedL2Isometry s x‖ :=
      (coefficientProjection (𝕜 := ℂ) N).le_opNorm (degreeWeightedL2Isometry s x)
    _ ≤ 1 * ‖degreeWeightedL2Isometry s x‖ :=
      mul_le_mul_of_nonneg_right (norm_coefficientProjection_le (𝕜 := ℂ) N) (norm_nonneg _)
    _ = ‖x‖ := by rw [one_mul, (degreeWeightedL2Isometry s).norm_map]

/-- Truncations converge in the weighted coefficient norm. -/
theorem tendsto_degreeWeightedProjection (s : ℕ) (x : DegreeWeightedL2 s) :
    Tendsto (fun N ↦ degreeWeightedProjection s N x) atTop (𝓝 x) := by
  have h := (degreeWeightedL2Isometry s).symm.continuous.continuousAt.tendsto.comp
    (tendsto_coefficientProjection (degreeWeightedL2Isometry s x))
  change Tendsto (fun N ↦ (degreeWeightedL2Isometry s).symm
    (coefficientProjection N (degreeWeightedL2Isometry s x))) atTop (𝓝 x)
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using h

/-- Reciprocal degree weights are bounded by one. -/
theorem norm_degreeWeightInverse_le (s n : ℕ) : ‖(((n : ℂ) + 1)^s)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_pow]
  have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by simpa using Complex.norm_natCast (n + 1)
  rw [hn]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

/-- Inclusion of degree-weighted sequences into ordinary square-summable sequences. -/
def degreeWeightedInclusion (s : ℕ) : DegreeWeightedL2 s →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  (coefficientDiagonal (fun n ↦ (((n : ℂ) + 1)^s)⁻¹) zero_le_one
    (norm_degreeWeightInverse_le s)).comp
      (degreeWeightedL2Isometry s).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem degreeWeightedInclusion_apply (s : ℕ) (x : DegreeWeightedL2 s) (n : ℕ) :
    degreeWeightedInclusion s x n = x.1 n := by
  change (((n : ℂ) + 1)^s)⁻¹ * (((n : ℂ) + 1)^s * x.1 n) = _
  field_simp

/-- The weighted inclusion does not identify distinct coefficient sequences. -/
theorem degreeWeightedInclusion_injective (s : ℕ) : Function.Injective (degreeWeightedInclusion s) := by
  intro x y h
  apply Subtype.ext
  funext n
  simpa only [degreeWeightedInclusion_apply] using congrArg (fun v : lp (fun _ : ℕ ↦ ℂ) 2 ↦ v n) h

end lp
