/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Norm

/-! # Total-degree ordering of the real Zernike family
Within even degree the order is 1,sin(2theta),cos(2theta),...; within odd degree
it is sin(theta),cos(theta),sin(3theta),cos(3theta),... . This is the convention
used in MultivariateOrthogonalPolynomials.jl, disk.jl (zero-based inner indices).
-/

@[expose] public section
namespace MvPolynomial

/-- Angular parity flag for the real degree ordering. -/
def zernikeSine (n j : ℕ) : Bool := decide ((n+j)%2 ≠ 0)

/-- Angular frequency in the real degree ordering. -/
def zernikeFrequency (n j : ℕ) : ℕ := j + if zernikeSine n j then 1 else 0

/-- Radial degree in the real degree ordering. -/
def zernikeRadialDegree (n j : ℕ) : ℕ := (n-zernikeFrequency n j)/2

/-- Recover the total degree and omit the zero sine mode. -/
theorem zernike_index_spec {n j : ℕ} (hj : j ≤ n) :
    2*zernikeRadialDegree n j + zernikeFrequency n j = n ∧
      (zernikeSine n j=true → zernikeFrequency n j≠0) := by
  simp only [zernikeSine, zernikeFrequency, zernikeRadialDegree, decide_eq_true_eq]
  split_ifs <;> omega

/-- The total-degree ordering never repeats a real mode. -/
theorem zernike_index_injective {n j m l : ℕ} (hj : j≤n) (hl : l≤m)
    (h : (zernikeSine n j,zernikeRadialDegree n j,zernikeFrequency n j) =
      (zernikeSine m l,zernikeRadialDegree m l,zernikeFrequency m l)) :
    (n,j)=(m,l) := by
  have hn := (zernike_index_spec hj).1
  have hm := (zernike_index_spec hl).1
  have hs := congrArg (fun v : Bool × ℕ × ℕ ↦ v.1) h
  have hk := congrArg (fun v : Bool × ℕ × ℕ ↦ v.2.1) h
  have hf := congrArg (fun v : Bool × ℕ × ℕ ↦ v.2.2) h
  simp only at hs hk hf
  have hnm : n=m := by omega
  have hjl : j=l := by
    unfold zernikeFrequency at hf
    rw [hs] at hf
    omega
  exact Prod.ext hnm hjl

/-- The real Zernike polynomial in total-degree order, before positive normalization. -/
noncomputable def zernike (a b : ℝ) (n j : ℕ) : MvPolynomial (Fin 2) ℝ :=
  zernikeMode (zernikeSine n j) a b (zernikeRadialDegree n j) (zernikeFrequency n j)

/-- The ordered polynomial lies in the indicated total-degree space. -/
theorem totalDegree_zernike_le_of_index (a b : ℝ) {n j : ℕ} (hj : j≤n) :
    (zernike a b n j).totalDegree ≤ n := by
  have hd : (zernike a b n j).totalDegree ≤
      2*zernikeRadialDegree n j+zernikeFrequency n j := by
    unfold zernike zernikeMode
    split
    · exact (totalDegree_zernike_le _ _ _ _).2
    · exact (totalDegree_zernike_le _ _ _ _).1
  simpa only [(zernike_index_spec hj).1] using hd

/-- Distinct valid total-degree indices are orthogonal in the standard disk measure. -/
theorem integralInner_zernike_eq_zero {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n j m l : ℕ} (hj : j≤n) (hl : l≤m) (hne : (n,j)≠(m,l)) :
    integralInner (zernikeMeasure a b) (IntegrablePair.of (zernikeMeasure a b) (zernike a b n j) (zernike a b m l)) = 0 := by
  apply integralInner_zernikeMode_eq_zero ha hb
  exact fun h ↦ hne (zernike_index_injective hj hl h)

/-- All valid ordered modes have positive squared norm. -/
theorem integral_sq_zernike_pos {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n j : ℕ} (hj : j≤n) :
    0 < ∫ v, (eval v (zernike a b n j))^2 ∂zernikeMeasure a b :=
  integral_sq_zernikeMode_pos ha hb _ _ _ (zernike_index_spec hj).2

end MvPolynomial
