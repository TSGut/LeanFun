/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletForm

/-! # Strict negativity of the annular Dirichlet form
The endpoint factors remove the constant kernel of differentiation.
Reference: the energy identity underlying Papadopoulos–Gutleb–Slevinsky–Olver,
Proposition 15.
-/

public section
namespace Polynomial

/-- A polynomial with endpoint zeros cannot have identically zero derivative unless it is zero. -/
theorem semiclassicalJacobiABWeightedDerivativeMap_ne_zero {p : ℝ[X]} (hp : p≠0) :
    semiclassicalJacobiABWeightedDerivativeMap p ≠ 0 := by
  intro h
  change (X*(1-X)*p).derivative=0 at h
  have he := eq_C_of_derivative_eq_zero h
  have hz : X*(1-X)*p=0 := by simpa using he
  have hs : (X*(1-X) : ℝ[X])≠0 := by
    intro hh
    have hval := congrArg (eval (1/2 : ℝ)) hh
    norm_num at hval
  exact hp ((mul_eq_zero.mp hz).resolve_left hs)

/-- Every nonzero radial polynomial has strictly negative Dirichlet energy. -/
theorem integralInner_semiclassicalJacobi_dirichlet_neg {t : ℝ} (ht : 1<t)
    (γ : ℝ) {p : ℝ[X]} (hp : p≠0) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ p) p) < 0 := by
  rw [integralInner_semiclassicalJacobi_dirichlet ht, integralInner_self]
  have he := hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure
    (γ := γ+1) ht (by norm_num : (-1 : ℝ)<0) (by norm_num : (-1 : ℝ)<0)
    _ (semiclassicalJacobiABWeightedDerivativeMap_ne_zero hp)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (by norm_num) (by linarith))) he

/-- In particular the weighted radial Laplacian has no polynomial kernel. -/
theorem semiclassicalJacobiDirichletMap_injective {t : ℝ} (ht : 1<t) (γ : ℝ) :
    Function.Injective (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  by_contra hne
  have h := integralInner_semiclassicalJacobi_dirichlet_neg ht γ hne
  simp only [integralInner, hp, eval_zero, zero_mul, MeasureTheory.integral_zero] at h
  exact (lt_irrefl 0) h

end Polynomial
