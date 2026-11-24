/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Interior points of the unit interval

A point of `(0, 1)` has a closed-off neighbourhood `(δ, 1 - δ)` inside the interval. This is
the radius used to dominate derivatives uniformly near an interior interpolation parameter.
`exists_Ioo_nhds_bound` gives a whole neighbourhood of `t` kept at distance `δ` from `0` and `1`.
-/

@[expose] public section

/-- Given `t ∈ (0, 1)`, there exists an interior radius `δ > 0` such that
`δ < t` and `δ < 1 - t`. -/
theorem exists_pos_lt_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < t ∧ δ < 1 - t := by
  obtain ⟨δ, hδ0, hδmin⟩ := exists_between (lt_min ht.1 (sub_pos.2 ht.2))
  exact ⟨δ, hδ0, hδmin.trans_le (min_le_left _ _), hδmin.trans_le (min_le_right _ _)⟩

/-- Given `t ∈ (0, 1)`, there is `δ > 0` such that `(t - δ, t + δ)` stays at distance at least `δ`
from both endpoints `0` and `1` (and in particular lies inside `(0, 1)`). -/
theorem exists_Ioo_nhds_bound {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ > 0, ∀ t' ∈ Set.Ioo (t - δ) (t + δ), δ ≤ t' ∧ δ ≤ 1 - t' := by
  refine ⟨min (t / 2) ((1 - t) / 2), lt_min (half_pos ht.1) (half_pos (sub_pos.2 ht.2)),
    fun t' ht' => ?_⟩
  have h1 : min (t / 2) ((1 - t) / 2) ≤ t / 2 := min_le_left _ _
  have h2 : min (t / 2) ((1 - t) / 2) ≤ (1 - t) / 2 := min_le_right _ _
  exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
