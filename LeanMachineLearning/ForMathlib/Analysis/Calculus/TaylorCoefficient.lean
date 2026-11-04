/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor

/-!
# Isolating a Taylor coefficient

A single coefficient can be retained exactly while all other coefficients and the remainder
are bounded. This separates the analytic Taylor argument from model-specific vanishing.
-/

@[expose] public section

open Finset Set

/-- Bound the error after retaining one Taylor coefficient on the unit interval.
The coefficients may be bounded separately, so vanishing terms can be assigned bound zero. -/
theorem norm_sub_taylor_coefficient_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {s a : ℕ} (ha : a ≤ s)
    (hc : ContDiffOn ℝ (s + 1) f (Set.Icc 0 1)) (C : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hterm : ∀ k ∈ range (s + 1), k ≠ a →
      ‖(k.factorial : ℝ)⁻¹ • iteratedDerivWithin k f (Set.Icc 0 1) 0‖ ≤ C k)
    (hder : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDerivWithin (s + 1) f (Set.Icc 0 1) u‖ ≤ M) :
    ‖f 1 - (a.factorial : ℝ)⁻¹ • iteratedDerivWithin a f (Set.Icc 0 1) 0‖ ≤
      (∑ k ∈ (range (s + 1)).erase a, C k) + M := by
  have hpoly : taylorWithinEval f s (Set.Icc 0 1) 0 1 -
      (a.factorial : ℝ)⁻¹ • iteratedDerivWithin a f (Set.Icc 0 1) 0 =
      ∑ k ∈ (range (s + 1)).erase a,
        (k.factorial : ℝ)⁻¹ • iteratedDerivWithin k f (Set.Icc 0 1) 0 := by
    rw [taylor_within_apply]
    simp only [sub_zero, one_pow, mul_one]
    exact (eq_sub_iff_add_eq.mpr (sum_erase_add _ _ (mem_range.mpr (by omega)))).symm
  have hp : ‖taylorWithinEval f s (Set.Icc 0 1) 0 1 -
      (a.factorial : ℝ)⁻¹ • iteratedDerivWithin a f (Set.Icc 0 1) 0‖ ≤
      ∑ k ∈ (range (s + 1)).erase a, C k := by
    rw [hpoly]
    exact (norm_sum_le _ _).trans (sum_le_sum fun k hk =>
      hterm k (mem_of_mem_erase hk) (ne_of_mem_erase hk))
  have hr : ‖f 1 - taylorWithinEval f s (Set.Icc 0 1) 0 1‖ ≤ M := by
    have hb := taylor_mean_remainder_bound (f := f) (n := s) zero_le_one hc
      (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) hder
    simp only [sub_zero, one_pow, mul_one] at hb
    exact hb.trans (div_le_self hM (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero s)))
  calc
    _ ≤ ‖f 1 - taylorWithinEval f s (Set.Icc 0 1) 0 1‖ +
        ‖taylorWithinEval f s (Set.Icc 0 1) 0 1 -
          (a.factorial : ℝ)⁻¹ • iteratedDerivWithin a f (Set.Icc 0 1) 0‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M + ∑ k ∈ (range (s + 1)).erase a, C k := add_le_add hr hp
    _ = _ := add_comm _ _
