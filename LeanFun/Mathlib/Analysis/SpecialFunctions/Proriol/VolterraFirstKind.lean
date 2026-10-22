/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.FirstOrderL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraJacobiCoefficients

/-! # The first-kind Volterra diagonal between coefficient spaces

The endpoint-factor-free constant-kernel map has diagonal `(-1)^n/(n+1)`.
Between raw ℓ² and first-order weighted ℓ² it is an isometric equivalence.
Reference: Gutleb–Olver, Lemma 5.6; Gutleb's thesis, §2.7, Lemma 2.3.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace lp

/-- Alternating signs preserve each real coefficient norm. -/
theorem norm_alternating_mul (n : ℕ) (a : ℝ) : ‖(-1 : ℝ)^n*a‖ = ‖a‖ := by
  simp [norm_mul, norm_pow]

/-- Alternating coefficient signs act isometrically on real ℓ². -/
def alternatingL2Isometry : lp (fun _ : ℕ ↦ ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 where
  toFun u := ⟨fun n ↦ (-1 : ℝ)^n*u n,
    (lp.memℓp u).mono' (fun n ↦ (norm_alternating_mul n (u n)).le)⟩
  invFun u := ⟨fun n ↦ (-1 : ℝ)^n*u n,
    (lp.memℓp u).mono' (fun n ↦ (norm_alternating_mul n (u n)).le)⟩
  left_inv u := by
    apply lp.ext
    funext n
    change (-1 : ℝ)^n*((-1 : ℝ)^n*u n) = u n
    simp [← mul_assoc, ← mul_pow]
  right_inv u := by
    apply lp.ext
    funext n
    change (-1 : ℝ)^n*((-1 : ℝ)^n*u n) = u n
    simp [← mul_assoc, ← mul_pow]
  map_add' u v := by
    apply lp.ext
    funext n
    exact mul_add _ _ _
  map_smul' c u := by
    apply lp.ext
    funext n
    change (-1 : ℝ)^n*(c*u n) = c*((-1 : ℝ)^n*u n)
    ring
  norm_map' u := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun n ↦ (norm_alternating_mul n (u n)).le)
    · exact lp.norm_mono (by norm_num) (fun n ↦ (norm_alternating_mul n (u n)).ge)

end lp
namespace MvPolynomial

/-- The Volterra integration diagonal is boundedly invertible into the weighted range space. -/
def volterraJacobiL2Equiv : lp (fun _ : ℕ ↦ ℝ) 2 ≃ₗᵢ[ℝ] lp.FirstOrderL2 :=
  lp.alternatingL2Isometry.trans lp.firstOrderL2Isometry.symm

/-- Exact zero-based diagonal, with the endpoint factor excluded. -/
theorem volterraJacobiL2Equiv_apply (u : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    (volterraJacobiL2Equiv u).1 n = ((-1 : ℝ)^n/((n : ℝ)+1))*u n := by
  change ((-1 : ℝ)^n*u n)/((n : ℝ)+1) = _
  ring

/-- The inverse restores one degree weight and the alternating sign. -/
theorem volterraJacobiL2Equiv_symm_apply (q : lp.FirstOrderL2) (n : ℕ) :
    volterraJacobiL2Equiv.symm q n = ((-1 : ℝ)^n*((n : ℝ)+1))*q.1 n := by
  change (-1 : ℝ)^n*(((n : ℝ)+1)*q.1 n) = _
  ring

/-- Agreement with the existing finite coefficient diagonal, checked column by column. -/
theorem volterraJacobiL2Equiv_single (n : ℕ) (a : ℝ) :
    (volterraJacobiL2Equiv (lp.single 2 n a)).1 =
      ⇑(volterraJacobiDiagonal (Finsupp.single n a)) := by
  funext i
  rw [volterraJacobiL2Equiv_apply, volterraJacobiDiagonal_single]
  simp only [lp.coeFn_single, Finsupp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all [mul_comm]

/-- Every weighted right-hand side has exactly one raw ℓ² solution for the constant kernel. -/
theorem existsUnique_volterraJacobiL2_solution (q : lp.FirstOrderL2) :
    ∃! u : lp (fun _ : ℕ ↦ ℝ) 2, volterraJacobiL2Equiv u = q :=
  ⟨volterraJacobiL2Equiv.symm q, volterraJacobiL2Equiv.apply_symm_apply q,
    fun _u hu ↦ volterraJacobiL2Equiv.injective (hu.trans
      (volterraJacobiL2Equiv.apply_symm_apply q).symm)⟩

/-- The weighted residual is exactly the error for the diagonal first-kind problem. -/
theorem norm_volterraJacobiL2_error_eq_residual (q : lp.FirstOrderL2)
    (v : lp (fun _ : ℕ ↦ ℝ) 2) :
    ‖v-volterraJacobiL2Equiv.symm q‖ = ‖volterraJacobiL2Equiv v-q‖ := by
  rw [← volterraJacobiL2Equiv.norm_map (v-volterraJacobiL2Equiv.symm q), map_sub,
    volterraJacobiL2Equiv.apply_symm_apply]

/-- The finite diagonal solve is the initial truncation of the exact inverse. -/
def volterraJacobiFiniteSolution (N : ℕ) (q : lp.FirstOrderL2) : lp (fun _ : ℕ ↦ ℝ) 2 :=
  lp.initialL2Projection N (volterraJacobiL2Equiv.symm q)

/-- Each resolved coefficient is obtained by the exact first-kind diagonal inverse. -/
theorem volterraJacobiFiniteSolution_apply (N : ℕ) (q : lp.FirstOrderL2) (i : ℕ) :
    volterraJacobiFiniteSolution N q i =
      if i < N then ((-1 : ℝ)^i*((i : ℝ)+1))*q.1 i else 0 := by
  simp only [volterraJacobiFiniteSolution, lp.initialL2Projection_apply, lp.coeFn_sum,
    lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_range,
    volterraJacobiL2Equiv_symm_apply]

/-- The diagonal finite solve satisfies every resolved equation exactly. -/
theorem volterraJacobiFiniteSolution_equations (N : ℕ) (q : lp.FirstOrderL2)
    (i : ℕ) (hi : i < N) :
    (volterraJacobiL2Equiv (volterraJacobiFiniteSolution N q)).1 i = q.1 i := by
  rw [volterraJacobiL2Equiv_apply, volterraJacobiFiniteSolution_apply, ite_eq_left hi]
  have hn : (i : ℝ)+1 ≠ 0 := by positivity
  have hs : (-1 : ℝ)^i*(-1 : ℝ)^i = 1 := by rw [← mul_pow]; norm_num
  field_simp
  rw [pow_two, hs, one_mul]

/-- Truncated solutions converge in the raw input coefficient norm. -/
theorem tendsto_volterraJacobiL2_solution (q : lp.FirstOrderL2) :
    Tendsto (fun N ↦ volterraJacobiFiniteSolution N q) atTop
      (𝓝 (volterraJacobiL2Equiv.symm q)) := lp.tendsto_initialL2Projection _

end MvPolynomial
