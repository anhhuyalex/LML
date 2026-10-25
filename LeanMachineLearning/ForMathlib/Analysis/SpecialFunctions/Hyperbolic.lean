/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Product and comparison identities for `Real.sinh` and `Real.cosh`

* `Real.cosh_mul_cosh`: `cosh x * cosh y = (cosh (x + y) + cosh (x - y)) / 2`.
* `Real.cosh_add_add_eq`: exponential expansion of `cosh (x + y + m)`.
* `Real.abs_sinh_le_cosh`: `|sinh x| ≤ cosh x`.
* `Real.abs_sinh_mul_sinh_le_cosh_mul_cosh`: `|sinh x * sinh y| ≤ cosh x * cosh y`.
* `Real.cosh_le_exp_abs`: `cosh x ≤ exp |x|`.
* `two_cosh_le_exp_abs_mul`: `2 cosh x ≤ 2 exp |x|`.
* `inv_two_cosh_le_exp_abs_mul`: `(2 cosh x)⁻¹ ≤ exp |x|`.
-/

@[expose] public section

namespace Real

/-- Product formula for hyperbolic cosine: `cosh x * cosh y = (cosh (x + y) + cosh (x - y)) / 2`. -/
theorem cosh_mul_cosh (x y : ℝ) :
    Real.cosh x * Real.cosh y = (Real.cosh (x + y) + Real.cosh (x - y)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  ring

/-- Exponential expansion of the hyperbolic cosine of a three-term sum. -/
theorem cosh_add_add_eq (x y m : ℝ) :
    Real.cosh (x + y + m) =
      (Real.exp m * (Real.exp x * Real.exp y) +
        Real.exp (-m) * (Real.exp (-x) * Real.exp (-y))) / 2 := by
  rw [Real.cosh_eq]
  have hneg : -(x + y + m) = -m + (-x) + (-y) := by ring
  rw [hneg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-- Hyperbolic sine is bounded by hyperbolic cosine in absolute value: `|sinh x| ≤ cosh x`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs x]
  exact (Real.sinh_lt_cosh _).le

/-- Product of hyperbolic sines is bounded by the product of hyperbolic cosines:
`|sinh x * sinh y| ≤ cosh x * cosh y`. -/
theorem abs_sinh_mul_sinh_le_cosh_mul_cosh (x y : ℝ) :
    |Real.sinh x * Real.sinh y| ≤ Real.cosh x * Real.cosh y := by
  rw [abs_mul]
  exact mul_le_mul (abs_sinh_le_cosh x) (abs_sinh_le_cosh y)
    (abs_nonneg _) (Real.cosh_pos x).le

/-- Hyperbolic cosine is bounded by the exponential of the absolute value. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    nlinarith [Real.exp_pos (-x), Real.exp_le_exp.2 (show -x ≤ x by linarith)]
  · rw [abs_of_nonpos h]
    nlinarith [Real.exp_pos x, Real.exp_le_exp.2 (show x ≤ -x by linarith)]

/-- `cosh (u + h)` in terms of exponentials of `±u`, `±h`. -/
theorem cosh_add_eq_exp (u h : ℝ) :
    Real.cosh (u + h) = (Real.exp h * Real.exp u + Real.exp (-h) * Real.exp (-u)) / 2 := by
  rw [Real.cosh_eq, Real.exp_add, show -(u + h) = -h + -u by ring, Real.exp_add]
  ring

/-- `sinh (u + h)` in terms of exponentials of `±u`, `±h`. -/
theorem sinh_add_eq_exp (u h : ℝ) :
    Real.sinh (u + h) = (Real.exp h * Real.exp u - Real.exp (-h) * Real.exp (-u)) / 2 := by
  rw [Real.sinh_eq, Real.exp_add, show -(u + h) = -h + -u by ring, Real.exp_add]
  ring

/-- `exp h ≤ 2 cosh h`. -/
theorem exp_le_two_cosh (h : ℝ) : Real.exp h ≤ 2 * Real.cosh h := by
  rw [Real.cosh_eq]; linarith [Real.exp_pos (-h)]

/-- `exp (-h) ≤ 2 cosh h`. -/
theorem exp_neg_le_two_cosh (h : ℝ) : Real.exp (-h) ≤ 2 * Real.cosh h := by
  rw [Real.cosh_eq]; linarith [Real.exp_pos h]

/-- `|(eʰ D₁ + e⁻ʰ D₂) / 2| ≤ cosh h (|D₁| + |D₂|)`. -/
theorem abs_exp_mul_add_exp_neg_mul_div_two_le (h D₁ D₂ : ℝ) :
    |(Real.exp h * D₁ + Real.exp (-h) * D₂) / 2| ≤ Real.cosh h * (|D₁| + |D₂|) := by
  have h1 : |(Real.exp h * D₁ + Real.exp (-h) * D₂) / 2| ≤
      (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc |Real.exp h * D₁ + Real.exp (-h) * D₂|
      _ ≤ |Real.exp h * D₁| + |Real.exp (-h) * D₂| := abs_add_le _ _
      _ = Real.exp h * |D₁| + Real.exp (-h) * |D₂| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  refine h1.trans ?_
  have he1 := exp_le_two_cosh h
  have he2 := exp_neg_le_two_cosh h
  calc (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2
    _ ≤ (2 * Real.cosh h * |D₁| + 2 * Real.cosh h * |D₂|) / 2 := by gcongr
    _ = Real.cosh h * (|D₁| + |D₂|) := by ring

/-- `|(eʰ D₁ - e⁻ʰ D₂) / 2| ≤ cosh h (|D₁| + |D₂|)`. -/
theorem abs_exp_mul_sub_exp_neg_mul_div_two_le (h D₁ D₂ : ℝ) :
    |(Real.exp h * D₁ - Real.exp (-h) * D₂) / 2| ≤ Real.cosh h * (|D₁| + |D₂|) := by
  have := abs_exp_mul_add_exp_neg_mul_div_two_le h D₁ (-D₂)
  rwa [abs_neg, mul_neg, ← sub_eq_add_neg] at this

end Real

namespace SpinGlasses

/-- Twice the hyperbolic cosine is bounded by twice the exponential of the absolute value. -/
theorem two_cosh_le_exp_abs_mul (x : ℝ) : 2 * Real.cosh x ≤ 2 * Real.exp |x| := by
  exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_abs x) (by norm_num)

/-- The reciprocal of twice the hyperbolic cosine is bounded by `exp |x|`. -/
theorem inv_two_cosh_le_exp_abs_mul (x : ℝ) :
    (2 * Real.cosh x)⁻¹ ≤ 1 * Real.exp |x| := by
  have h1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have h2 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  rw [one_mul]
  calc
    (2 * Real.cosh x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    _ ≤ _ := h2

end SpinGlasses
