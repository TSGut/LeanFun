/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space
/-! # The zero-boundary Sobolev graph

For an open subset of real coordinate space, take the closure of smooth compactly
supported function/gradient pairs in `L² × (⊕² L²)`. Integration by parts passes
to this closure, so every pair satisfies the weak-derivative identities.
Reference: the standard `H₀¹` closure construction, e.g. Evans,
*Partial Differential Equations*, Chapter 5.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Distributions
namespace MeasureTheory.DirichletSpace
variable {n : ℕ} (Ω : TopologicalSpace.Opens (Fin n → ℝ))
/-- Scalar square-integrable functions on the open domain. -/
abbrev FunctionL2 := Lp ℝ 2 (volume.restrict (Ω : Set (Fin n → ℝ)))
/-- Square-integrable Cartesian gradient components with the Hilbert-sum norm. -/
abbrev GradientL2 := lp (fun _ : Fin n ↦ FunctionL2 Ω) 2
/-- A smooth compactly supported test function as an L² class. -/
noncomputable def testL2 : TestFunction Ω ℝ ⊤ →ₗ[ℝ] FunctionL2 Ω where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- The Cartesian derivative of a test function, with the same support constraint. -/
noncomputable def testDerivative (i : Fin n) :
    TestFunction Ω ℝ ⊤ →L[ℝ] TestFunction Ω ℝ ⊤ :=
  TestFunction.lineDerivCLM ℝ (Pi.single i 1)
/-- The Cartesian gradient of a test function as L² classes. -/
noncomputable def testGradient : TestFunction Ω ℝ ⊤ →ₗ[ℝ] GradientL2 Ω :=
  ∑ i : Fin n, (lp.singleContinuousLinearMap ℝ (fun _ : Fin n ↦ FunctionL2 Ω) 2 i).toLinearMap.comp
    ((testL2 Ω).comp (testDerivative Ω i).toLinearMap)
/-- The function/gradient pair of a smooth compactly supported test function. -/
noncomputable def testGraph : TestFunction Ω ℝ ⊤ →ₗ[ℝ] FunctionL2 Ω × GradientL2 Ω :=
  (testL2 Ω).prod (testGradient Ω)
/-- The closed zero-boundary Sobolev graph (the standard H₀¹ closure construction). -/
noncomputable def graph : Submodule ℝ (FunctionL2 Ω × GradientL2 Ω) :=
  (testGraph Ω).range.topologicalClosure
/-- The zero-boundary Sobolev space represented by function/gradient pairs. -/
abbrev Space := graph Ω
/-- Each gradient coordinate is the corresponding derivative class. -/
@[simp] theorem testGradient_apply (f : TestFunction Ω ℝ ⊤) (i : Fin n) :
    testGradient Ω f i = testL2 Ω (testDerivative Ω i f) := by
  simp only [testGradient, LinearMap.sum_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, lp.singleContinuousLinearMap_apply, lp.coeFn_sum]
  simp only [lp.coeFn_single]
  rw [Finset.sum_apply]
  simp [Pi.single_apply]
/-- Smooth compactly supported function/gradient pairs belong to the closed graph. -/
theorem testGraph_mem (f : TestFunction Ω ℝ ⊤) : testGraph Ω f ∈ graph Ω :=
  Submodule.le_topologicalClosure _ ⟨f, rfl⟩
/-- The zero-boundary Sobolev graph is closed in the product L² topology. -/
theorem graph_isClosed : IsClosed (graph Ω : Set (FunctionL2 Ω × GradientL2 Ω)) :=
  Submodule.isClosed_topologicalClosure _
/-- The L² representative agrees almost everywhere with the test function. -/
theorem coe_testL2 (f : TestFunction Ω ℝ ⊤) :
    (testL2 Ω f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] f :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).coeFn_toLp
/-- Test-function differentiation is Cartesian Fréchet differentiation. -/
theorem testDerivative_apply (f : TestFunction Ω ℝ ⊤) (i : Fin n) (x : Fin n → ℝ) :
    testDerivative Ω i f x = fderiv ℝ f x (Pi.single i 1) := by
  rw [testDerivative, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
/-- The L² pairing of tests is their ordinary Lebesgue integral on coordinate space. -/
theorem inner_testL2 (f g : TestFunction Ω ℝ ⊤) :
    inner ℝ (testL2 Ω f) (testL2 Ω g) = ∫ x, f x*g x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in (Ω : Set (Fin n → ℝ)), f x*g x := by
      apply integral_congr_ae
      filter_upwards [coe_testL2 Ω f, coe_testL2 Ω g] with x hf hg
      simp [hf, hg, mul_comm]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hf : f x = 0 := by
        by_contra hn
        exact hx (f.tsupport_subset (subset_tsupport f (Function.mem_support.mpr hn)))
      rw [hf, zero_mul])
/-- Compactly supported smooth tests satisfy integration by parts. -/
theorem inner_testDerivative (f g : TestFunction Ω ℝ ⊤) (i : Fin n) :
    inner ℝ (testL2 Ω f) (testL2 Ω (testDerivative Ω i g)) =
      -inner ℝ (testL2 Ω (testDerivative Ω i f)) (testL2 Ω g) := by
  rw [inner_testL2, inner_testL2]
  have hi (a b : TestFunction Ω ℝ ⊤) : Integrable (fun x ↦ a x*b x) :=
    (a.continuous.mul b.continuous).integrable_of_hasCompactSupport
      a.hasCompactSupport.mul_right
  simp_rw [testDerivative_apply]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · simpa only [testDerivative_apply] using hi (testDerivative Ω i f) g
  · simpa only [testDerivative_apply] using hi f (testDerivative Ω i g)
  · exact hi f g
  · exact fun x _ ↦ (f.contDiff.differentiable (by simp)).differentiableAt
  · exact fun x _ ↦ (g.contDiff.differentiable (by simp)).differentiableAt

/-- Every pair in the closed Sobolev graph satisfies the weak-derivative identities. -/
theorem graph_weakDerivative {u : FunctionL2 Ω × GradientL2 Ω} (hu : u ∈ graph Ω)
    (φ : TestFunction Ω ℝ ⊤) (i : Fin n) :
    inner ℝ u.1 (testL2 Ω (testDerivative Ω i φ)) =
      -inner ℝ (u.2 i) (testL2 Ω φ) := by
  have hc : IsClosed {u : FunctionL2 Ω × GradientL2 Ω |
      inner ℝ u.1 (testL2 Ω (testDerivative Ω i φ)) =
        -inner ℝ (u.2 i) (testL2 Ω φ)} := by
    apply isClosed_eq
    · fun_prop
    · exact (((lp.evalCLM ℝ (fun _ : Fin n ↦ FunctionL2 Ω) 2 i).continuous.comp
        continuous_snd).inner continuous_const).neg
  apply closure_minimal (s := Set.range (testGraph Ω)) ?_ hc hu
  rintro _ ⟨f, rfl⟩
  change inner ℝ (testL2 Ω f) (testL2 Ω (testDerivative Ω i φ)) =
    -inner ℝ (testGradient Ω f i) (testL2 Ω φ)
  rw [testGradient_apply]
  exact inner_testDerivative Ω f φ i
end MeasureTheory.DirichletSpace
