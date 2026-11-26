/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# The truncated squared norm

## Main statements

* `abs_min_norm_sq_sub_le`: `x ↦ min ‖x‖ a ^ 2` is `2 a`-Lipschitz.
-/

@[expose] public section

/-- The squared norm truncated at radius `a` is `2 a`-Lipschitz. -/
theorem abs_min_norm_sq_sub_le {E : Type*} [SeminormedAddCommGroup E] {a : ℝ} (ha : 0 ≤ a)
    (x y : E) : |min ‖x‖ a ^ 2 - min ‖y‖ a ^ 2| ≤ 2 * a * ‖x - y‖ := by
  have h1 : |min ‖x‖ a - min ‖y‖ a| ≤ ‖x - y‖ := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (abs_norm_sub_norm_le x y) ?_)
    rw [sub_self, abs_zero]
    exact norm_nonneg _
  have h2 : |min ‖x‖ a + min ‖y‖ a| ≤ 2 * a := by
    rw [abs_of_nonneg (add_nonneg (le_min (norm_nonneg _) ha) (le_min (norm_nonneg _) ha))]
    linarith [min_le_right ‖x‖ a, min_le_right ‖y‖ a]
  rw [sq_sub_sq, abs_mul]
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
