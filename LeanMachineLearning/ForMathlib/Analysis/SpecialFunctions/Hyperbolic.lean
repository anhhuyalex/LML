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
