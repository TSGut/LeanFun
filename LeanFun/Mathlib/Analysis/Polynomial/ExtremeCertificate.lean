/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Convex.CompactHull
public import LeanFun.Mathlib.Topology.ContinuousMap.UniformImprovement
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-! # Finite certificates for real minimax approximation
Convex separation and Carathéodory reduce the extreme set of a best approximation
to at most `n+2` norming points. Reference: ATAP, Theorem 10.1.
-/

@[expose] public section
namespace Polynomial
open Set

/-- Error-weighted monomial evaluation vector used in the minimax certificate. -/
noncomputable def extremeMoment {a b : ℝ} (n : ℕ) (e : C(Icc a b, ℝ))
    (x : Icc a b) : Fin (n + 1) → ℝ := fun j ↦ e x * (x : ℝ) ^ (j : ℕ)

private noncomputable def dualPolynomial {n : ℕ} (L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) : ℝ[X] :=
  ∑ j : Fin (n + 1), C (L (Pi.single j 1)) * X ^ (j : ℕ)

private theorem degree_dualPolynomial_le {n : ℕ} (L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) :
    (dualPolynomial L).degree ≤ n := by
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j _
  exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.le_of_lt_succ j.isLt)

private theorem eval_dualPolynomial {n : ℕ} (L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (x : ℝ) :
    (dualPolynomial L).eval x = L (fun j ↦ x ^ (j : ℕ)) := by
  have hv : (fun j : Fin (n + 1) ↦ x ^ (j : ℕ)) =
      ∑ j : Fin (n + 1), x ^ (j : ℕ) • Pi.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply, smul_eq_mul]
  rw [hv, map_sum]
  simp only [dualPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For a nonzero best error, zero lies in the convex hull of the signed
monomial vectors at its extreme points (ATAP 10.1, separation argument). -/
theorem zero_mem_convexHull_extremeMoment {a b : ℝ} {n : ℕ} (e : C(Icc a b, ℝ))
    (he : 0 < ‖e‖)
    (hmin : ∀ q : ℝ[X], q.degree ≤ n → ‖e‖ ≤ ‖e - q.toContinuousMapOn (Icc a b)‖) :
    0 ∈ convexHull ℝ (extremeMoment n e '' {x | |e x| = ‖e‖}) := by
  have hK : IsCompact (extremeMoment n e '' {x | |e x| = ‖e‖}) :=
    (isClosed_eq (by fun_prop) continuous_const).isCompact.image (by
      unfold extremeMoment
      fun_prop)
  by_contra h
  obtain ⟨L, c, hc, hL⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _) hK.convexHull_finiteDimensional.isClosed h
  have hsign (x : Icc a b) (hx : |e x| = ‖e‖) :
      0 < e x * (dualPolynomial L).eval (x : ℝ) := by
    have ht := hL _ (subset_convexHull ℝ _ (mem_image_of_mem _ hx))
    have hv : extremeMoment n e x = e x • (fun j : Fin (n + 1) ↦ (x : ℝ) ^ (j : ℕ)) := rfl
    rw [hv, map_smul, smul_eq_mul, ← eval_dualPolynomial] at ht
    simpa only [map_zero] using hc.trans ht
  obtain ⟨t, ht, himprove⟩ := e.exists_norm_sub_smul_lt_of_extreme_sign
    ((dualPolynomial L).toContinuousMapOn (Icc a b)) he hsign
  have hq := hmin (t • dualPolynomial L)
    ((degree_smul_le _ _).trans (degree_dualPolynomial_le L))
  have hmap : (t • dualPolynomial L).toContinuousMapOn (Icc a b) =
      t • (dualPolynomial L).toContinuousMapOn (Icc a b) := by ext x; simp
  rw [hmap] at hq
  exact (not_lt_of_ge hq) himprove

/-- A nonzero best error has a positive norming certificate supported at at
most `n+2` distinct extreme points (ATAP 10.1). -/
theorem exists_extremeMoment_certificate {a b : ℝ} {n : ℕ} (e : C(Icc a b, ℝ))
    (he : 0 < ‖e‖)
    (hmin : ∀ q : ℝ[X], q.degree ≤ n → ‖e‖ ≤ ‖e - q.toContinuousMapOn (Icc a b)‖) :
    ∃ (m : ℕ) (x : Fin m → Icc a b) (w : Fin m → ℝ),
      m ≤ n + 2 ∧ Function.Injective x ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧ (∀ i, |e (x i)| = ‖e‖) ∧
      ∑ i, w i • extremeMoment n e (x i) = 0 := by
  obtain ⟨ι, hι, z, w, hz, hi, hw, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull (zero_mem_convexHull_extremeMoment e he hmin)
  have hx (i : ι) : ∃ x : Icc a b, |e x| = ‖e‖ ∧ extremeMoment n e x = z i := hz ⟨i, rfl⟩
  choose x hxe hxz using hx
  have hinj : Function.Injective x := by
    intro i j hij
    apply hi.injective
    rw [← hxz i, ← hxz j, hij]
  let f := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, x ∘ f, w ∘ f, ?_, hinj.comp f.injective,
    fun i ↦ hw _, ?_, fun i ↦ hxe _, ?_⟩
  · have hcard := hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa using hcard
  · simpa only [Function.comp_apply] using (Equiv.sum_comp f w).trans hsum
  · simpa only [Function.comp_apply, hxz] using
      (Equiv.sum_comp f (fun i ↦ w i • z i)).trans heq

end Polynomial
