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

/-- **A replica combination of bounded terms:** if `|f j| ≤ b` for all `j` and `|g| ≤ b`, then
`|∑ⱼ f j - |ι| g| ≤ 2 |ι| b`. -/
theorem abs_sum_sub_card_mul_le_of_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (g b : ℝ)
    (hf : ∀ j, |f j| ≤ b) (hg : |g| ≤ b) :
    |∑ j, f j - (Fintype.card ι : ℝ) * g| ≤ 2 * (Fintype.card ι : ℝ) * b := by
  have h1 : |∑ j, f j| ≤ (Fintype.card ι : ℝ) * b := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |f j| ≤ ∑ _j : ι, b := sum_le_sum fun j _ => hf j
      _ = (Fintype.card ι : ℝ) * b := by simp
  have h2 : |(Fintype.card ι : ℝ) * g| ≤ (Fintype.card ι : ℝ) * b := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)
  calc |∑ j, f j - (Fintype.card ι : ℝ) * g|
      ≤ |∑ j, f j| + |(Fintype.card ι : ℝ) * g| := abs_sub _ _
    _ ≤ (Fintype.card ι : ℝ) * b + (Fintype.card ι : ℝ) * b := add_le_add h1 h2
    _ = 2 * (Fintype.card ι : ℝ) * b := by ring

/-- Triangle-inequality bound on the difference between a finite sum and a scaled multiple. -/
theorem abs_sum_sub_card_mul_le {ι α : Type*} [Fintype ι] {M : ℝ} (Q : α → ℝ) (hQ0 : ∀ a, 0 ≤ Q a)
    (hQM : ∀ a, Q a ≤ M) (x : ι → α) (y : α) :
    |∑ i, Q (x i) - (Fintype.card ι : ℝ) * Q y| ≤ 2 * (Fintype.card ι : ℝ) * M :=
  abs_sum_sub_card_mul_le_of_abs_le (fun i => Q (x i)) (Q y) M
    (fun _ => (abs_of_nonneg (hQ0 _)).le.trans (hQM _))
    ((abs_of_nonneg (hQ0 _)).le.trans (hQM _))

end Finset
