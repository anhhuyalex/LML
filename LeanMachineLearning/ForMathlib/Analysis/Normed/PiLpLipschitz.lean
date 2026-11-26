/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Coordinatewise Lipschitz maps between `ℓ^p` products

## Main statements

* `PiLp.lipschitzWith_toLp_comp`: applying a `K`-Lipschitz map to every coordinate is
  `K`-Lipschitz for the `ℓ^p` distance.
-/

@[expose] public section

open scoped ENNReal NNReal

/-- Applying a `K`-Lipschitz map to every coordinate is `K`-Lipschitz for the `ℓ^p` distance. -/
theorem PiLp.lipschitzWith_toLp_comp {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β γ : ι → Type*} [∀ i, PseudoMetricSpace (β i)] [∀ i, PseudoMetricSpace (γ i)] {K : ℝ≥0}
    {φ : ∀ i, β i → γ i} (hφ : ∀ i, LipschitzWith K (φ i)) :
    LipschitzWith K fun x : PiLp p β => WithLp.toLp p fun i => φ i (x i) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases p.dichotomy with rfl | h
  · rw [PiLp.dist_eq_iSup]
    exact Real.iSup_le (fun i => ((hφ i).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y i) K.2)) (by positivity)
  · have hp : 0 < p.toReal := lt_of_lt_of_le one_pos h
    have hsum : 0 ≤ ∑ i, dist (x i) (y i) ^ p.toReal :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg dist_nonneg _
    rw [PiLp.dist_eq_sum hp, PiLp.dist_eq_sum hp]
    calc (∑ i, dist (φ i (x i)) (φ i (y i)) ^ p.toReal) ^ (1 / p.toReal)
        ≤ (∑ i, ((K : ℝ) * dist (x i) (y i)) ^ p.toReal) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg dist_nonneg _)
            (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow dist_nonneg
              ((hφ i).dist_le_mul _ _) hp.le) (by positivity)
      _ = K * (∑ i, dist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
          have e : ∀ i, ((K : ℝ) * dist (x i) (y i)) ^ p.toReal =
              (K : ℝ) ^ p.toReal * dist (x i) (y i) ^ p.toReal := fun i =>
            Real.mul_rpow K.coe_nonneg dist_nonneg
          simp only [e]
          rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg K.coe_nonneg _) hsum,
            ← Real.rpow_mul K.coe_nonneg, mul_one_div_cancel hp.ne', Real.rpow_one]
