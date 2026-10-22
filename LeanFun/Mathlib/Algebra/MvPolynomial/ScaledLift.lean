/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.MvPolynomial.VerticalTruncation
public import Mathlib.Data.PNat.Basic

/-!
# Polynomial lifts for separated Koornwinder systems

The coefficient formula covers polynomial scales (step 1) and square-root
polynomial scales with parity (step 2). No degree restriction is built into the
definition. Ordinary total-degree bounds require degree(scale) ≤ step.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, §2.6.1.
-/

@[expose] public section
namespace MvPolynomial
variable {R : Type*} [CommRing R]

/-- Division-free lift for a scale whose specified power is polynomial. -/
noncomputable def scaledLift (a : Polynomial R) (step : ℕ+) (n : ℕ) (p : Polynomial R) :
    MvPolynomial (Fin 2) R :=
  ∑ j ∈ Finset.range (n+1), C (p.coeff j) * X 1 ^ j *
    a.eval₂ C (X 0) ^ ((n-j)/(step : ℕ))

/-- The scaled-coordinate evaluation formula, including zero-scale boundary points. -/
theorem eval_scaledLift (a : Polynomial R) (step : ℕ+) (n : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ n)
    (hpar : ∀ j ≤ n, p.coeff j ≠ 0 → (step : ℕ) ∣ n-j)
    (v : Fin 2 → R) (s z : R) (hs : a.eval (v 0) = s^(step : ℕ)) (hy : v 1 = s*z) :
    eval v (scaledLift a step n p) = s^n * p.eval z := by
  rw [scaledLift, map_sum, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n+1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_pow, eval_C, eval_X, eval_eval₂_C_X, hs, hy]
  by_cases hz : p.coeff j = 0
  · simp [hz]
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have he : j+(step : ℕ)*((n-j)/(step : ℕ)) = n := by
    rw [Nat.mul_div_cancel' (hpar j hjn hz)]
    omega
  rw [mul_pow, ← pow_mul]
  calc
    p.coeff j * (s^j*z^j) * s^((step : ℕ)*((n-j)/(step : ℕ))) =
        (s^j*s^((step : ℕ)*((n-j)/(step : ℕ)))) * (p.coeff j*z^j) := by ring
    _ = s^n * (p.coeff j*z^j) := by rw [← pow_add, he]

/-- Ordinary Koornwinder scale degrees preserve the total-degree bound. -/
theorem totalDegree_scaledLift_le (a : Polynomial R) (step : ℕ+) (n : ℕ) (p : Polynomial R)
    (ha : a.natDegree ≤ (step : ℕ)) : (scaledLift a step n p).totalDegree ≤ n := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    rw [Subsingleton.elim (scaledLift a step n p) 0, totalDegree_zero]
    exact Nat.zero_le _
  let := hR
  unfold scaledLift
  apply totalDegree_finsetSum_le
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hc : (C (p.coeff j) * (X 1 : MvPolynomial (Fin 2) R)^j).totalDegree ≤ j := by
    exact (totalDegree_mul _ _).trans (by simp)
  have hb := (totalDegree_eval₂_C_X_le a (0 : Fin 2)).trans ha
  have hp := totalDegree_pow (a.eval₂ C (X 0 : MvPolynomial (Fin 2) R)) ((n-j)/(step : ℕ))
  have hm := Nat.mul_le_mul_left ((n-j)/(step : ℕ)) hb
  have hd := Nat.div_mul_le_self (n-j) (step : ℕ)
  have ht := totalDegree_mul (C (p.coeff j)*(X 1 : MvPolynomial (Fin 2) R)^j)
    (a.eval₂ C (X 0)^((n-j)/(step : ℕ)))
  omega

/-- The existing disk lift is the square-root-quadratic specialization. -/
theorem scaledLift_disk (n : ℕ) (p : Polynomial R) :
    scaledLift (1-Polynomial.X^2) 2 n p = diskLift n p := by
  simp [scaledLift, diskLift]

end MvPolynomial
