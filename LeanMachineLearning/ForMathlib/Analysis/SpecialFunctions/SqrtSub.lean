/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Estimates for differences of square roots

* `Real.sq_sqrt_sub_le_abs_sub`: `(√a - √b)² ≤ |a - b|` for `a, b ≥ 0`.
* `Real.sq_sqrt_sub_le`: `(√q - a)² ≤ (q - a²)² / q` for `q > 0`, `a ≥ 0`.
-/

@[expose] public section

namespace Real

/-- `(√a - √b)² ≤ |a - b|` for `a, b ≥ 0`: `|a - b| = |√a - √b| (√a + √b)` and
`|√a - √b| ≤ √a + √b`. -/
theorem sq_sqrt_sub_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hab : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have heq : |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    have := Real.sq_sqrt ha
    have := Real.sq_sqrt hb
    nlinarith
  rw [heq, ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)

/-- `(√q - a)² ≤ (q - a²)² / q` for `q > 0`, `a ≥ 0`, because
`(q - a²)² = (√q - a)² (√q + a)²` and `(√q + a)² ≥ q`. -/
theorem sq_sqrt_sub_le {q a : ℝ} (hq : 0 < q) (ha : 0 ≤ a) :
    (Real.sqrt q - a) ^ 2 ≤ (q - a ^ 2) ^ 2 / q := by
  have key : ∀ s : ℝ, 0 < s → (s - a) ^ 2 ≤ (s ^ 2 - a ^ 2) ^ 2 / s ^ 2 := fun s hs => by
    rw [le_div_iff₀ (by positivity)]
    have hid : (s ^ 2 - a ^ 2) ^ 2 - (s - a) ^ 2 * s ^ 2 = (s - a) ^ 2 * (a * (2 * s + a)) := by
      ring
    have : 0 ≤ (s - a) ^ 2 * (a * (2 * s + a)) := by positivity
    linarith
  have := key (Real.sqrt q) (Real.sqrt_pos.mpr hq)
  rwa [Real.sq_sqrt hq.le] at this

end Real
