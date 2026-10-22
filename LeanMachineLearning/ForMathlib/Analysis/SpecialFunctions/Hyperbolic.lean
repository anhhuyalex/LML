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
* `Real.abs_sinh_le_cosh`: `|sinh x| ≤ cosh x`.
* `Real.abs_sinh_mul_sinh_le_cosh_mul_cosh`: `|sinh x * sinh y| ≤ cosh x * cosh y`.
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

end Real

namespace SpinGlasses

/-- Twice the hyperbolic cosine is bounded by twice the exponential of the absolute value. -/
theorem two_cosh_le_exp_abs_mul (x : ℝ) : 2 * Real.cosh x ≤ 2 * Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    nlinarith [Real.exp_pos (-x), Real.exp_le_exp.2 (show -x ≤ x by linarith)]
  · rw [abs_of_nonpos h]
    nlinarith [Real.exp_pos x, Real.exp_le_exp.2 (show x ≤ -x by linarith)]

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
