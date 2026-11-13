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

/-- A finite sum of terms that are each within `B` of `L` is within `card * B` of `card * L`. -/
theorem abs_sum_sub_card_mul_le_of_abs_sub_le {ι : Type*} [Fintype ι] (W : ι → ℝ) (L B : ℝ)
    (h : ∀ i, |W i - L| ≤ B) :
    |∑ i, W i - (Fintype.card ι : ℝ) * L| ≤ (Fintype.card ι : ℝ) * B := by
  have e : ∑ i, W i - (Fintype.card ι : ℝ) * L = ∑ i, (W i - L) := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |W i - L| ≤ ∑ _i : ι, B := sum_le_sum fun i _ => h i
    _ = _ := by simp

/-- **A replica combination of bounded terms:** if `|f j| ≤ b` for all `j` and `|g| ≤ b`, then
`|∑ⱼ f j - |ι| g| ≤ 2 |ι| b`. -/
theorem abs_sum_sub_card_mul_le_of_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (g b : ℝ)
    (hf : ∀ j, |f j| ≤ b) (hg : |g| ≤ b) :
    |∑ j, f j - (Fintype.card ι : ℝ) * g| ≤ 2 * (Fintype.card ι : ℝ) * b := by
  have := abs_sum_sub_card_mul_le_of_abs_sub_le f g (2 * b) fun j =>
    (abs_sub _ _).trans ((add_le_add (hf j) hg).trans_eq (two_mul b).symm)
  exact this.trans_eq (by ring)

/-- Triangle-inequality bound on the difference between a finite sum and a scaled multiple. -/
theorem abs_sum_sub_card_mul_le {ι α : Type*} [Fintype ι] {M : ℝ} (Q : α → ℝ) (hQ0 : ∀ a, 0 ≤ Q a)
    (hQM : ∀ a, Q a ≤ M) (x : ι → α) (y : α) :
    |∑ i, Q (x i) - (Fintype.card ι : ℝ) * Q y| ≤ 2 * (Fintype.card ι : ℝ) * M :=
  abs_sum_sub_card_mul_le_of_abs_le (fun i => Q (x i)) (Q y) M
    (fun _ => (abs_of_nonneg (hQ0 _)).le.trans (hQM _))
    ((abs_of_nonneg (hQ0 _)).le.trans (hQM _))

end Finset
