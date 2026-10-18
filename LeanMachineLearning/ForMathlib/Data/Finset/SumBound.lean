/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Bounds on finite sums of real functions
-/

@[expose] public section

namespace Finset

/-- Triangle-inequality bound on the difference between a finite sum and a scaled multiple. -/
theorem abs_sum_sub_card_mul_le {ι α : Type*} [Fintype ι] {M : ℝ} (Q : α → ℝ) (hQ0 : ∀ a, 0 ≤ Q a)
    (hQM : ∀ a, Q a ≤ M) (x : ι → α) (y : α) :
    |∑ i, Q (x i) - (Fintype.card ι : ℝ) * Q y| ≤ 2 * (Fintype.card ι : ℝ) * M := by
  have hA : |∑ i, Q (x i)| ≤ (Fintype.card ι : ℝ) * M := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |Q (x i)| ≤ ∑ i : ι, M :=
        sum_le_sum fun i _ => (abs_of_nonneg (hQ0 _)).le.trans (hQM _)
      _ = (Fintype.card ι : ℝ) * M := by simp
  have hB : |(Fintype.card ι : ℝ) * Q y| ≤ (Fintype.card ι : ℝ) * M := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (hQ0 _)]
    exact mul_le_mul_of_nonneg_left (hQM _) (Nat.cast_nonneg _)
  calc |∑ i, Q (x i) - (Fintype.card ι : ℝ) * Q y|
      ≤ |∑ i, Q (x i)| + |(Fintype.card ι : ℝ) * Q y| := abs_sub _ _
    _ ≤ (Fintype.card ι : ℝ) * M + (Fintype.card ι : ℝ) * M := add_le_add hA hB
    _ = 2 * (Fintype.card ι : ℝ) * M := by ring

end Finset
