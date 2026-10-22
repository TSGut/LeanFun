/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticCholesky
public import LeanFun.Mathlib.LinearAlgebra.Matrix.GramFactorSectors

/-! # Lifting the disk obstruction to an interleaved full Gram factor
A complete even sector may be extracted without changing its factor entries.
The existing degree/inner order puts lower degrees before the top degree and
orders the top degree by its inner index.
Reference: Cholesky elimination with orthogonal parity sectors.
-/

@[expose] public section
open Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- The normalized affine Gram pencil on all even-even indices through degree 2r. -/
noncomputable def dunklXuEvenGramPencil {β : ℝ} (hβ : -1 < β) (u v t : ℝ) (r : ℕ) :
    Matrix (DunklXuEvenInterior r ⊕ Fin (r + 1)) (DunklXuEvenInterior r ⊕ Fin (r + 1)) ℝ :=
  fromBlocks (1 + t • dunklXuInteriorMatrix hβ u v r)
    (t • dunklXuQuadraticRightBlock hβ u v r)
    (t • dunklXuQuadraticLeftBlock hβ u v r)
    (1 + t • dunklXuQuadraticBoundaryBlock hβ u v r)

/-- The distant factor entry survives extraction from a full factor with
interleaved orthogonal sectors. Exact sector coverage and ordering are explicit. -/
theorem eventually_dunklXu_full_factor_entry_ne_zero {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (hv : v ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ {N : ℕ} {γ : Type}
      (R : Matrix (Fin N) (Fin N) ℝ) (sector : Fin N → γ)
      (e : DunklXuEvenInterior r ⊕ Fin (r + 1) → Fin N) (c : γ),
      R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
      (∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0) →
      Function.Injective e → (∀ i, sector (e i) = c) →
      (∀ k, sector k = c → k ∈ Set.range e) →
      (∀ i j, e (Sum.inl i) < e (Sum.inr j)) → StrictMono (e ∘ Sum.inr) →
      (R.transpose * R).submatrix e e = dunklXuEvenGramPencil hβ u v t r →
      R (e (Sum.inr 0)) (e (Sum.inr (Fin.last r))) ≠ 0 := by
  filter_upwards [eventually_dunklXuQuadratic_cholesky_first_last_ne_zero hβ u v hv r hr]
    with t ht
  intro N γ R sector e c hR hd hG he hc hcover hbefore hmono hP
  let A := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let B := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let D := R.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  have hblocks := hR.gram_sector_blocks hd sector hG e he c hc hcover hbefore
  change (R.transpose * R).submatrix e e =
    fromBlocks (A.transpose * A) (A.transpose * B) (B.transpose * A)
      (B.transpose * B + D.transpose * D) at hblocks
  have h := hblocks.symm.trans hP
  have hAA : A.transpose * A = 1 + t • dunklXuInteriorMatrix hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inl i) (Sum.inl j)) h
  have hAB : A.transpose * B = t • dunklXuQuadraticRightBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inl i) (Sum.inr j)) h
  have hBA : B.transpose * A = t • dunklXuQuadraticLeftBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inr i) (Sum.inl j)) h
  have hDD : B.transpose * B + D.transpose * D =
      1 + t • dunklXuQuadraticBoundaryBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inr i) (Sum.inr j)) h
  exact ht A B D (hR.isUnit_det_submatrix hd _ (he.comp Sum.inl_injective))
    (hR.submatrix_strictMono _ hmono) hAA hAB hBA hDD

end MvPolynomial
