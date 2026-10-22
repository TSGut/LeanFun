/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Polynomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerIntegrationByParts
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Lowering
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerReflection

/-! # Recurrence for power-law integrals of Gegenbauer modes

The kernel exponent stays fixed. The cleared form includes the degenerate
parameter `lam = 0`. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Lemma 2.2.
-/

public section
open Set Polynomial
namespace Real




end Real

namespace Real

theorem powerLawLeftPolynomial_gegenbauer_recurrenceOn
    (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (m : ℕ) :
    let U := fun n ↦ powerLawLeftPolynomial α lam x (gegenbauer lam.val n)
    2*((m : ℝ)+lam.val+1)*((m : ℝ)+1)*((m : ℝ)+1+2*lam.val)*x.val*U (m+1) =
      ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*lam.val+α.val+2)*U (m+2)+
      ((m : ℝ)+1+2*lam.val)*((m : ℝ)-α.val)*((m : ℝ)+2*lam.val)*U m := by
  dsimp only
  let L := powerLawLeftPolynomial α lam x
  have hr := congrArg L (gegenbauer_recurrence lam.val m)
  have hl := congrArg L (gegenbauer_lowering lam.property m)
  have hL (c : ℝ) (p : ℝ[X]) : L (C c*p) = c*L p := by
    rw [← smul_eq_C_mul,map_smul,smul_eq_mul]
  rw [mul_assoc] at hr hl
  simp only [L.map_add,L.map_sub,L.map_zero,hL] at hr hl
  have hi := powerLawLeftPolynomial_gegenbauer_integrationByParts α lam x (m+1)
  rw [← powerLawLeftPolynomial_shift_weight] at hi
  have he := powerLawLeftPolynomial_mul_X α lam x (gegenbauer lam.val (m+1))
  change L (X*gegenbauer lam.val (m+1)) = x.val*L (gegenbauer lam.val (m+1)) - _ at he
  change _ = -(α.val+1)*L ((1-X^2)*(gegenbauer lam.val (m+1)).derivative) at hi
  change _*L (gegenbauer lam.val (m+1)) = _*L (gegenbauer lam.val (m+2)) + _*L (gegenbauer lam.val m)
  push_cast at hi hl hr
  linear_combination -2*((m : ℝ)+lam.val+1)*((m : ℝ)+1)*((m : ℝ)+1+2*lam.val)*he +
    2*((m : ℝ)+lam.val+1)*hi - 2*((m : ℝ)+lam.val+1)*(α.val+1)*hl -
    ((m : ℝ)+1)*((m : ℝ)+2*lam.val+α.val+2)*hr

theorem powerLawRight_gegenbauer_recurrenceOn
    (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (m : ℕ) :
    let U := fun n ↦ powerLawRight ((PowerLawInput.gegenbauerMode α lam x n).right
      ⟨x.val,Ioo_subset_Icc_self x.property⟩)
    2*((m : ℝ)+lam.val+1)*((m : ℝ)+1)*((m : ℝ)+1+2*lam.val)*x.val*U (m+1) =
      ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*lam.val+α.val+2)*U (m+2)+
      ((m : ℝ)+1+2*lam.val)*((m : ℝ)-α.val)*((m : ℝ)+2*lam.val)*U m := by
  let xn : Ioo (-1 : ℝ) 1 := ⟨-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩
  have h := powerLawLeftPolynomial_gegenbauer_recurrenceOn α lam xn m
  dsimp only at h ⊢
  simp only [powerLawRight_gegenbauerMode_reflect,pow_add,pow_one,neg_one_sq]
  dsimp only [xn] at h
  linear_combination (-1 : ℝ)^m*h

theorem powerLawIntegral_gegenbauer_recurrenceOn
    (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (m : ℕ) :
    let U := fun n ↦ powerLawIntegral (.gegenbauerMode α lam x n)
    2*((m : ℝ)+lam.val+1)*((m : ℝ)+1)*((m : ℝ)+1+2*lam.val)*x.val*U (m+1) =
      ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*lam.val+α.val+2)*U (m+2)+
      ((m : ℝ)+1+2*lam.val)*((m : ℝ)-α.val)*((m : ℝ)+2*lam.val)*U m := by
  have hl := powerLawLeftPolynomial_gegenbauer_recurrenceOn α lam x m
  have hr := powerLawRight_gegenbauer_recurrenceOn α lam x m
  dsimp only at hl hr ⊢
  simp_rw [powerLawIntegral_eq_left_add_right ⟨x.val,Ioo_subset_Icc_self x.property⟩]
  have he (n : ℕ) : powerLawLeftPolynomial α lam x (gegenbauer lam.val n) =
      powerLawLeft ((PowerLawInput.gegenbauerMode α lam x n).left
        ⟨x.val,Ioo_subset_Icc_self x.property⟩) := rfl
  simp_rw [he] at hl
  linear_combination hl+hr

end Real
