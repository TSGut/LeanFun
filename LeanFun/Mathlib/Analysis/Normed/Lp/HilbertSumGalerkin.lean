/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Galerkin approximation in a Hilbert sum
Finite-dimensional approximations in each sector combine with finite angular
truncation. Both cutoffs may grow independently. The proof uses density and
orthogonal projections, without a rate or a uniform sector regularity assumption.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace lp
namespace HilbertSumGalerkin

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  (W : ∀ i, ℕ → Submodule ℝ (E i)) [∀ i N, FiniteDimensional ℝ (W i N)]

/-- Trial vectors have finitely many sectors and a finite trial vector in each sector. -/
def trialSpace (c : Finset ι × ℕ) : Submodule ℝ (lp E 2) :=
  ⨆ i : c.1, (W i c.2).map (lp.lsingle (𝕜 := ℝ) (E := E) 2 (i : ι))

instance (c : Finset ι × ℕ) : FiniteDimensional ℝ (trialSpace W c) := by
  unfold trialSpace
  infer_instance

omit [∀ i N, FiniteDimensional ℝ (W i N)] in
/-- One retained sector embeds into the combined trial space. -/
theorem single_mem_trialSpace (c : Finset ι × ℕ) {i : ι} (hi : i ∈ c.1)
    {x : E i} (hx : x ∈ W i c.2) : lp.single 2 i x ∈ trialSpace W c := by
  apply (le_iSup (fun j : c.1 ↦ (W j c.2).map (lp.lsingle (𝕜 := ℝ) (E := E) 2 (j : ι))) ⟨i, hi⟩)
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

omit [∀ i N, FiniteDimensional ℝ (W i N)] in
/-- Enlarging both cutoffs enlarges the trial space. -/
theorem trialSpace_mono (hW : ∀ i, Monotone (W i)) : Monotone (trialSpace W) := by
  intro c d h
  apply iSup_le
  intro i
  rintro x ⟨y, hy, rfl⟩
  exact single_mem_trialSpace W d (h.1 i.property) (hW i h.2 hy)

/-- Independent finite sector projections reconstruct the combined orthogonal projection. -/
theorem sum_projection_eq (c : Finset ι × ℕ) (x : lp E 2) :
    ∑ i ∈ c.1, lp.single 2 i ((W i c.2).starProjection (x i)) =
      (trialSpace W c).starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem _ fun i hi ↦
      single_mem_trialSpace W c hi ((W i c.2).starProjection_apply_mem _)
  · intro z hz
    unfold trialSpace at hz
    refine Submodule.iSup_induction _ (motive := fun z ↦
      inner ℝ (x - ∑ j ∈ c.1, lp.single 2 j ((W j c.2).starProjection (x j))) z = 0)
      hz ?_ ?_ ?_
    · intro i z hz
      obtain ⟨y, hy, rfl⟩ := hz
      change inner ℝ (x - ∑ j ∈ c.1, lp.single 2 j ((W j c.2).starProjection (x j)))
        (lp.single 2 i y) = 0
      rw [lp.inner_single_right]
      simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply,
        lp.coeFn_single, Finset.sum_pi_single, ite_eq_left i.property]
      exact (W i c.2).starProjection_inner_eq_zero _ _ hy
    · simp
    · intro a b ha hb
      simp [inner_add_right, ha, hb]

/-- Dense radial trial spaces give a dense union of combined finite trial spaces. -/
theorem trialSpace_closure_iSup (hW : ∀ i, Monotone (W i))
    (hd : ∀ i, (⨆ N, W i N).topologicalClosure = ⊤) :
    (⨆ c, trialSpace W c).topologicalClosure = ⊤ := by
  let K := (⨆ c, trialSpace W c).topologicalClosure
  have hK : IsClosed (K : Set (lp E 2)) := Submodule.isClosed_topologicalClosure _
  have hs (i : ι) (y : E i) : lp.single 2 i y ∈ K := by
    have ht := (lp.singleContinuousLinearMap ℝ E 2 i).continuous.tendsto y |>.comp
      (Submodule.starProjection_tendsto_self (W i) (hW i) y (by rw [hd i]))
    apply hK.mem_of_tendsto ht
    apply Eventually.of_forall
    intro N
    apply Submodule.le_topologicalClosure
    apply (le_iSup (trialSpace W) ({i}, N))
    exact single_mem_trialSpace W ({i}, N) (Finset.mem_singleton_self i)
      ((W i N).starProjection_apply_mem _)
  apply le_antisymm le_top
  intro x hx
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
  exact Eventually.of_forall fun S ↦ Submodule.sum_mem _ fun i hi ↦ hs i (x i)

/-- Actual sector projections converge jointly as the finite sector set and radial degree grow. -/
theorem tendsto_sum_projection (hW : ∀ i, Monotone (W i))
    (hd : ∀ i, (⨆ N, W i N).topologicalClosure = ⊤) (x : lp E 2) :
    Tendsto (fun c : Finset ι × ℕ ↦
      ∑ i ∈ c.1, lp.single 2 i ((W i c.2).starProjection (x i))) atTop (𝓝 x) := by
  simp only [sum_projection_eq]
  exact Submodule.starProjection_tendsto_self (trialSpace W) (trialSpace_mono W hW) x
    (by rw [trialSpace_closure_iSup W hW hd])

end HilbertSumGalerkin
end lp
