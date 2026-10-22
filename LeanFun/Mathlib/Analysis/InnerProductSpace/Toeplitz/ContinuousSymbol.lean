/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Basic
public import LeanFun.Mathlib.Analysis.IntegralEq.BoundedKernel
public import Mathlib.Analysis.Fourier.AddCircle

/-! # Continuous-symbol Toeplitz operators by Fourier compression

Compress multiplication on the circle to the nonnegative Fourier modes.
Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz
Matrices, Chapter 1.
-/

@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
namespace AddCircle
variable {T : ℝ} [Fact (0 < T)]
local notation "L" => Lp ℂ 2 (haarAddCircle (T := T))
local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

/-- The nonnegative Fourier modes are an orthonormal family. -/
theorem orthonormal_nonnegativeFourier :
    Orthonormal ℂ (fun n : ℕ ↦ (fourierLp (T := T) 2 (n : ℤ))) :=
  orthonormal_fourier.comp (fun n : ℕ ↦ (n : ℤ)) (by intro m n h; change (m : ℤ) = (n : ℤ) at h; omega)

/-- Isometric synthesis of the nonnegative Fourier coefficients. -/
def nonnegativeFourierIsometry : H →ₗᵢ[ℂ] L :=
  orthonormal_nonnegativeFourier.orthogonalFamily.linearIsometry

/-- A single coefficient synthesizes its corresponding Fourier monomial. -/
theorem nonnegativeFourierIsometry_single (n : ℕ) (a : ℂ) :
    nonnegativeFourierIsometry (T := T) (lp.single 2 n a) =
      a • fourierLp (T := T) 2 (n : ℤ) := by
  rw [nonnegativeFourierIsometry, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

/-- Multiplication by a continuous circle symbol on L². -/
def continuousSymbolMultiplier (f : C(AddCircle T, ℂ)) : L →L[ℂ] L :=
  boundedMulL2 haarAddCircle f f.continuous.aestronglyMeasurable (norm_nonneg f)
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- Circle multiplication is bounded by the uniform symbol norm. -/
theorem norm_continuousSymbolMultiplier_le (f : C(AddCircle T, ℂ)) :
    ‖continuousSymbolMultiplier f‖ ≤ ‖f‖ :=
  norm_boundedMulL2_le _ _ _ _ _

/-- The multiplier has the pointwise product as its almost-everywhere representative. -/
theorem continuousSymbolMultiplier_ae (f : C(AddCircle T, ℂ)) (u : L) :
    continuousSymbolMultiplier f u =ᵐ[haarAddCircle] fun x ↦ f x * u x :=
  boundedMulL2_ae _ _ _ _ _ _

/-- Toeplitz quantization by compression to the nonnegative Fourier modes. -/
def continuousToeplitz (f : C(AddCircle T, ℂ)) : H →L[ℂ] H :=
  nonnegativeFourierIsometry.toContinuousLinearMap.adjoint.comp
    ((continuousSymbolMultiplier f).comp nonnegativeFourierIsometry.toContinuousLinearMap)

/-- The continuous-symbol Toeplitz operator is bounded by the uniform norm. -/
theorem norm_continuousToeplitz_le (f : C(AddCircle T, ℂ)) :
    ‖continuousToeplitz f‖ ≤ ‖f‖ := by
  have hE : ‖(nonnegativeFourierIsometry (T := T)).toContinuousLinearMap‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  unfold continuousToeplitz
  apply (opNorm_comp_le _ _).trans
  rw [adjoint.norm_map]
  have hm := (opNorm_comp_le (continuousSymbolMultiplier f)
    nonnegativeFourierIsometry.toContinuousLinearMap).trans
      (mul_le_mul (norm_continuousSymbolMultiplier_le f) hE (norm_nonneg _) (norm_nonneg _))
  simpa only [mul_one, one_mul] using
    mul_le_mul hE hm (norm_nonneg _) (by norm_num)

/-- Continuous multiplication agrees with pointwise multiplication of continuous inputs. -/
theorem continuousSymbolMultiplier_toLp (f g : C(AddCircle T, ℂ)) :
    continuousSymbolMultiplier f (ContinuousMap.toLp 2 haarAddCircle ℂ g) =
      ContinuousMap.toLp 2 haarAddCircle ℂ (f*g) := by
  apply Lp.ext
  filter_upwards [continuousSymbolMultiplier_ae f (ContinuousMap.toLp 2 haarAddCircle ℂ g),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle g,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle (f*g)] with x hx hg hfg
  simp only [hx, hg, hfg, ContinuousMap.mul_apply]

/-- Toeplitz matrix entries are the corresponding Fourier coefficients of the symbol. -/
theorem continuousToeplitz_entry (f : C(AddCircle T, ℂ)) (i j : ℕ) :
    continuousToeplitz f (lp.single 2 j 1) i = fourierCoeff f ((i : ℤ)-j) := by
  have he : continuousToeplitz f (lp.single 2 j 1) i =
      ⟪fourierLp (T := T) 2 (i : ℤ),
        continuousSymbolMultiplier f (fourierLp (T := T) 2 (j : ℤ))⟫_ℂ := by
    have h := adjoint_inner_right
      (nonnegativeFourierIsometry (T := T)).toContinuousLinearMap
      (lp.single 2 i 1)
      (continuousSymbolMultiplier f (nonnegativeFourierIsometry (lp.single 2 j 1)))
    simpa only [continuousToeplitz, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      nonnegativeFourierIsometry_single, one_smul, lp.inner_single_left,
      RCLike.inner_apply, map_one, mul_one] using h
  rw [he, fourierLp, fourierLp, continuousSymbolMultiplier_toLp,
    ContinuousMap.inner_toLp, fourierCoeff]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply, ← fourier_neg, smul_eq_mul]
  rw [show -((i : ℤ)-j) = - (i : ℤ) + j by ring, fourier_add]
  ring

/-- Continuous-symbol compression has constant matrix diagonals. -/
theorem isToeplitz_continuousToeplitz (f : C(AddCircle T, ℂ)) :
    lp.IsToeplitz (continuousToeplitz f) := by
  intro i j
  simp only [continuousToeplitz_entry, Nat.cast_add, Nat.cast_one,
    add_sub_add_right_eq_sub]

/-- Continuous-symbol Toeplitz quantization preserves addition. -/
theorem continuousToeplitz_add (f g : C(AddCircle T, ℂ)) :
    continuousToeplitz (f+g) = continuousToeplitz f+continuousToeplitz g := by
  apply lp.continuousLinearMap_ext_single
  intro j
  apply lp.ext
  funext i
  change continuousToeplitz (f+g) (lp.single 2 j 1) i =
    continuousToeplitz f (lp.single 2 j 1) i+continuousToeplitz g (lp.single 2 j 1) i
  simp only [continuousToeplitz_entry]
  exact congrFun (fourierCoeff.add
    ((ContinuousMap.memLp (p := 1) haarAddCircle ℂ f).integrable le_rfl)
    ((ContinuousMap.memLp (p := 1) haarAddCircle ℂ g).integrable le_rfl)) _

/-- Continuous-symbol Toeplitz quantization preserves complex scalar multiplication. -/
theorem continuousToeplitz_smul (a : ℂ) (f : C(AddCircle T, ℂ)) :
    continuousToeplitz (a • f) = a • continuousToeplitz f := by
  apply lp.continuousLinearMap_ext_single
  intro j
  apply lp.ext
  funext i
  change continuousToeplitz (a • f) (lp.single 2 j 1) i =
    a • continuousToeplitz f (lp.single 2 j 1) i
  simp only [continuousToeplitz_entry]
  exact fourierCoeff.const_smul f a _

/-- Toeplitz quantization is a bounded linear map on continuous symbols. -/
def continuousToeplitzCLM : C(AddCircle T, ℂ) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := continuousToeplitz
      map_add' := continuousToeplitz_add
      map_smul' := continuousToeplitz_smul }
    1 (by intro f; simpa using norm_continuousToeplitz_le f)

/-- Uniform convergence of continuous symbols implies operator-norm convergence. -/
theorem tendsto_continuousToeplitz {f : ℕ → C(AddCircle T, ℂ)} {g : C(AddCircle T, ℂ)}
    (h : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun n ↦ continuousToeplitz (f n)) Filter.atTop (nhds (continuousToeplitz g)) :=
  (continuousToeplitzCLM.continuous.tendsto g).comp h

end AddCircle
