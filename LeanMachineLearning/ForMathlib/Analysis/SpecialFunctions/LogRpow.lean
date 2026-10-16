/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithm is controlled by a power and its inverse

`|log z| ≤ (z ^ a + z ^ (-a)) / a` for `z ≥ 0` and `a > 0`. It is the standard way to see that
`log T` is integrable as soon as both `T ^ a` and `T ^ (-a)` are.
-/

@[expose] public section

namespace Real

/-- `|log z| ≤ (z ^ a + z ^ (-a)) / a` for `z ≥ 0`, `a > 0` (both sides vanish at `z = 0`). -/
theorem abs_log_le_rpow_add_rpow_neg {z a : ℝ} (hz : 0 ≤ z) (ha : 0 < a) :
    |Real.log z| ≤ (z ^ a + z ^ (-a)) / a := by
  rcases hz.eq_or_lt with rfl | hz0
  · simp [Real.zero_rpow ha.ne', Real.zero_rpow (neg_ne_zero.2 ha.ne')]
  have h1 : 0 ≤ z ^ a := Real.rpow_nonneg hz _
  have h2 : 0 ≤ z ^ (-a) := Real.rpow_nonneg hz _
  rcases le_total 1 z with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    exact (Real.log_le_rpow_div hz ha).trans (div_le_div_of_nonneg_right (by linarith) ha.le)
  · rw [abs_of_nonpos (Real.log_nonpos hz h), ← Real.log_inv]
    refine (Real.log_le_rpow_div (inv_nonneg.2 hz) ha).trans
      (div_le_div_of_nonneg_right ?_ ha.le)
    rw [Real.inv_rpow hz, ← Real.rpow_neg hz]
    linarith

end Real
