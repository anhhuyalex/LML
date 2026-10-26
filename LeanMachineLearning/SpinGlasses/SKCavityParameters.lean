/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub

/-!
# Passing from the `N`-spin to the `(N+1)`-spin SK parameters

The cavity method compares the `(N+1)`-spin system at `(β, q)` with the `N`-spin system at
`β_- = β √(N/(N+1))` and a fixed point `q_-`, where `|q - q_-| ≤ 1/(N+1)` (the fixed-point shift).
The two estimates here say that replacing `(β_-, q_-)` by `(β, q)` in the cavity formulas costs
`O(1/(N+1))`.  They are specific to this scaling of `β_-` and to the shift hypothesis, so they
live here and not in the model-independent `SqrtSub.lean`, which only holds the square-root
algebra they use.

## Main declarations

* `SpinGlasses.sq_cavity_param_le`: `(β_- √q_- - β √q)² ≤ 1/(N+1)` (Theorem 1.7.1).
* `SpinGlasses.abs_tap_coef_le`: `|β²(1-q) - β_-²(1-q_-)| ≤ 1/(N+1)` (Theorem 1.7.7).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.7.
-/

@[expose] public section

namespace SpinGlasses

/-- A real-analytic estimate for the passage from `(β_-, q_-)` to `(β, q)`:
`(β_- √q_- - β √q)² ≤ 1/(N+1)` when `|q - q_-| ≤ 1/(N+1)`, `β_- = β √(N/(N+1))` and
`4 β² < 1`. -/
theorem sq_cavity_param_le {β q qm : ℝ} {N : ℕ} (hβ4 : 4 * β ^ 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqm : qm ∈ Set.Icc (0 : ℝ) 1)
    (hshift : |q - qm| ≤ 1 / ((N : ℝ) + 1)) :
    (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm - β * Real.sqrt q) ^ 2 ≤
      1 / ((N : ℝ) + 1) := by
  set ε : ℝ := 1 / ((N : ℝ) + 1) with hε
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one hN1]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set s : ℝ := Real.sqrt ((N : ℝ) / (N + 1)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hx : (N : ℝ) / (N + 1) = 1 - ε := by rw [hε]; field_simp; ring
  have hs1 : 1 - ε ≤ s := by
    rw [hs, hx]
    have h0 : 0 ≤ 1 - ε := by linarith
    calc 1 - ε = Real.sqrt ((1 - ε) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - ε) := Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : s ≤ 1 := by
    rw [hs, hx]; exact Real.sqrt_le_one.mpr (by linarith)
  have hd : (Real.sqrt qm - Real.sqrt q) ^ 2 ≤ ε := by
    have h1 := Real.sq_sqrt_sub_le_abs_sub hqm.1 hq.1
    calc _ ≤ |qm - q| := h1
      _ = |q - qm| := abs_sub_comm _ _
      _ ≤ ε := hshift
  have hsq : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq.2
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hdec : β * s * Real.sqrt qm - β * Real.sqrt q =
      β * s * (Real.sqrt qm - Real.sqrt q) + β * ((s - 1) * Real.sqrt q) := by ring
  have hb2 : β ^ 2 ≤ 1 / 4 := by linarith
  have he2 : ((s - 1) * Real.sqrt q) ^ 2 ≤ ε := by
    rw [mul_pow]
    have : (s - 1) ^ 2 ≤ ε := by nlinarith
    have : Real.sqrt q ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (s - 1), sq_nonneg (Real.sqrt q)]
  rw [hdec]
  have h1 : (β * s * (Real.sqrt qm - Real.sqrt q)) ^ 2 ≤ β ^ 2 * ε := by
    have hs2' : s ^ 2 ≤ 1 := by nlinarith
    have h1a : s ^ 2 * (Real.sqrt qm - Real.sqrt q) ^ 2 ≤ ε :=
      (mul_le_of_le_one_left (sq_nonneg _) hs2').trans hd
    calc (β * s * (Real.sqrt qm - Real.sqrt q)) ^ 2 =
          β ^ 2 * (s ^ 2 * (Real.sqrt qm - Real.sqrt q) ^ 2) := by ring
      _ ≤ β ^ 2 * ε := mul_le_mul_of_nonneg_left h1a (sq_nonneg β)
  have h2 : (β * ((s - 1) * Real.sqrt q)) ^ 2 ≤ β ^ 2 * ε := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left he2 (sq_nonneg β)
  have h3 : β ^ 2 * ε ≤ ε / 4 := by nlinarith
  nlinarith [sq_nonneg (β * s * (Real.sqrt qm - Real.sqrt q) - β * ((s - 1) * Real.sqrt q))]

/-- **Replacing `β_-², q_-` by `β², q` costs `1/(N+1)`:** for `4 β² < 1`, `q, q_- ∈ [0, 1]` and
`|q - q_-| ≤ 1/(N+1)`, `|β²(1-q) - (β √(N/(N+1)))² (1-q_-)| ≤ 1/(N+1)`. -/
theorem abs_tap_coef_le {N : ℕ} {β q qm : ℝ} (hβ4 : 4 * β ^ 2 < 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hshift : |q - qm| ≤ 1 / ((N : ℝ) + 1)) :
    |β ^ 2 * (1 - q) - (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 * (1 - qm)| ≤
      1 / ((N : ℝ) + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsq : (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 = β ^ 2 * ((N : ℝ) / (N + 1)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hdiff : β ^ 2 - β ^ 2 * ((N : ℝ) / (N + 1)) = β ^ 2 / ((N : ℝ) + 1) := by
    field_simp; ring
  have hsh := abs_le.mp hshift
  set ε : ℝ := 1 / ((N : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hb0 : 0 ≤ β ^ 2 / ((N : ℝ) + 1) := by positivity
  have hb1 : β ^ 2 / ((N : ℝ) + 1) ≤ ε / 4 := by
    have h14 : β ^ 2 ≤ 1 / 4 := by linarith
    calc β ^ 2 / ((N : ℝ) + 1) ≤ (1 / 4) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right h14 hN1.le
      _ = ε / 4 := by rw [hε]; field_simp
  have hbm : β ^ 2 * ((N : ℝ) / (N + 1)) ≤ 1 / 4 := by
    have : (N : ℝ) / (N + 1) ≤ 1 := (div_le_one hN1).mpr (by linarith)
    nlinarith [sq_nonneg β]
  have hbm0 : 0 ≤ β ^ 2 * ((N : ℝ) / (N + 1)) := by positivity
  rw [hsq, abs_le]
  have e : β ^ 2 * (1 - q) - β ^ 2 * ((N : ℝ) / (N + 1)) * (1 - qm) =
      (β ^ 2 / ((N : ℝ) + 1)) * (1 - q) + β ^ 2 * ((N : ℝ) / (N + 1)) * (qm - q) := by
    rw [← hdiff]; ring
  rw [e]
  obtain ⟨hq0, hq1⟩ := hq
  set a := β ^ 2 / ((N : ℝ) + 1) with ha
  set b := β ^ 2 * ((N : ℝ) / (N + 1)) with hb
  have h1 : 0 ≤ a * (1 - q) := mul_nonneg hb0 (sub_nonneg.mpr hq1)
  have h2 : a * (1 - q) ≤ a := by nlinarith [mul_nonneg hb0 hq0]
  have h3 : b * (qm - q) ≤ b * ε := mul_le_mul_of_nonneg_left (by linarith) hbm0
  have h4 : -(b * ε) ≤ b * (qm - q) := by
    have := mul_le_mul_of_nonneg_left (show -ε ≤ qm - q by linarith) hbm0
    linarith
  have h5 : b * ε ≤ ε / 4 := by nlinarith
  constructor <;> linarith

end SpinGlasses
