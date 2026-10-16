/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Subadditivity of `x ↦ x ^ p` for countable sums in `ℝ≥0∞`

For `0 < p ≤ 1`, Mathlib has `ENNReal.rpow_add_le_add_rpow` for two summands. We extend it to
finite and countable sums.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace ENNReal

/-- Finite version of `ENNReal.rpow_tsum_le_tsum_rpow`. -/
theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add_right ih _)

/-- **Subadditivity of `x ^ p`, `0 < p ≤ 1`, for countable sums in `ℝ≥0∞`:**
`(∑' i, f i) ^ p ≤ ∑' i, f i ^ p`. -/
theorem rpow_tsum_le_tsum_rpow {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  have hmono : Monotone fun x : ℝ≥0∞ => x ^ p := fun a b hab => ENNReal.rpow_le_rpow hab hp0.le
  rw [hmono.map_iSup_of_continuousAt (ENNReal.continuous_rpow_const (y := p)).continuousAt
    (ENNReal.zero_rpow_of_pos hp0)]
  exact iSup_mono fun s => rpow_sum_le_sum_rpow s f hp0 hp1

/-- For `0 ≤ p ≤ 1`, `x ^ p ≤ 1 + x`. -/
theorem rpow_le_one_add {x : ℝ≥0∞} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : x ^ p ≤ 1 + x := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hp0).trans le_self_add
  · calc x ^ p ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (not_le.1 hx).le hp1
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_self

end ENNReal
