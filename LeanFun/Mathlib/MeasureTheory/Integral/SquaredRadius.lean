/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! # Squared-radius substitution on the unit interval
The one-dimensional Jacobian theorem handles integrable endpoint singularities
without imposing endpoint differentiability on the integrand.
-/

public section
open Set
namespace MeasureTheory

attribute [local instance] Measure.Subtype.measureSpace
/-- An integrable input transforms under squared radius with Jacobian `2*r`. -/
theorem integral_unitInterval_sq (f : IntegrableInput (volume : Measure (Ioo (0 : ℝ) 1))) :
    Integrable (fun r : Ioo (0 : ℝ) 1 ↦ 2*(r : ℝ)*f.val ⟨(r : ℝ)^2, by constructor <;> nlinarith [r.property.1, r.property.2, sq_nonneg (r : ℝ)]⟩) volume ∧
    (∫ s : Ioo (0 : ℝ) 1, f.val s) =
      ∫ r : Ioo (0 : ℝ) 1, 2*(r : ℝ)*f.val ⟨(r : ℝ)^2, by constructor <;> nlinarith [r.property.1, r.property.2, sq_nonneg (r : ℝ)]⟩ := by
  let F : ℝ → ℝ := fun r ↦ if h : r ∈ Ioo (0 : ℝ) 1 then f.val ⟨r,h⟩ else 0
  have hF (r : Ioo (0 : ℝ) 1) : F r = f.val r := by simp only [F, dite_eq_left r.property]
  have hi : IntegrableOn F (Ioo (0 : ℝ) 1) := by
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
    simpa only [Measure.Subtype.volume_def, Function.comp_def, hF] using f.integrable
  have him : (fun r : ℝ ↦ r^2) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext s
    constructor
    · rintro ⟨r,hr,rfl⟩
      constructor <;> nlinarith [hr.1, hr.2, sq_nonneg r]
    · intro hs
      refine ⟨Real.sqrt s, ⟨Real.sqrt_pos.2 hs.1, ?_⟩, Real.sq_sqrt hs.1.le⟩
      have := Real.sq_sqrt hs.1.le
      nlinarith [hs.2, Real.sqrt_nonneg s]
  have hd (r : ℝ) (_hr : r ∈ Ioo (0 : ℝ) 1) :
      HasDerivWithinAt (fun r : ℝ ↦ r^2) (2*r) (Ioo (0 : ℝ) 1) r := by
    convert! ((hasDerivAt_id r).pow 2).hasDerivWithinAt (s := Ioo (0 : ℝ) 1) using 1
    all_goals first | rfl | simp
  have hinj : InjOn (fun r : ℝ ↦ r^2) (Ioo (0 : ℝ) 1) := by
    intro r hr s hs he
    nlinarith [hr.1, hs.1]
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj F
  have hgi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj F
  rw [him] at he hgi
  have hx (r : Ioo (0 : ℝ) 1) : |2*(r : ℝ)| • F ((r : ℝ)^2) =
      2*(r : ℝ)*f.val ⟨(r : ℝ)^2, by constructor <;> nlinarith [r.property.1, r.property.2, sq_nonneg (r : ℝ)]⟩ := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) r.property.1.le), smul_eq_mul]
    congr 1
    exact hF ⟨(r : ℝ)^2, by constructor <;> nlinarith [r.property.1, r.property.2, sq_nonneg (r : ℝ)]⟩
  refine ⟨?_, ?_⟩
  · apply ((integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp (hgi.mp hi)).congr
    exact Filter.Eventually.of_forall hx
  · rw [← integral_subtype_comap measurableSet_Ioo F,
      ← integral_subtype_comap measurableSet_Ioo (fun r : ℝ ↦ |2*r| • F (r^2))] at he
    simpa only [Measure.Subtype.volume_def, hF, hx] using he

end MeasureTheory
