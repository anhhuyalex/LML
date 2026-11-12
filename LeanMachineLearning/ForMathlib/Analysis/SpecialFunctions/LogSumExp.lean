/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Elementary bounds on the logarithm of a finite sum of exponentials

This module contains uniform Lipschitz and absolute bounds on `log ∑ exp`:
* `abs_log_sum_exp_sub_le_of_forall`: `log ∑ exp (u + h)` is 1-Lipschitz for the supremum norm.
* `abs_log_sum_exp_le_of_forall`: bound on `|log ∑ exp u|` by `log (card α) + sup |u|`.
-/

@[expose] public section

open Finset Real

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **`log ∑ₐ exp (· + h)` is 1-Lipschitz for the sup norm:** if `|uₐ - vₐ| ≤ M` for all `a`, then
`|log ∑ₐ exp (uₐ + hₐ) - log ∑ₐ exp (vₐ + hₐ)| ≤ M`. -/
theorem abs_log_sum_exp_sub_le_of_forall (h u v : α → ℝ) {M : ℝ} (hM : ∀ a, |u a - v a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a + h a)) - Real.log (∑ a, Real.exp (v a + h a))| ≤ M := by
  have key : ∀ u v : α → ℝ, (∀ a, u a - v a ≤ M) → Real.log (∑ a, Real.exp (u a + h a)) -
      Real.log (∑ a, Real.exp (v a + h a)) ≤ M := by
    intro u v huv
    have hu : 0 < ∑ a, Real.exp (u a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    have hv : 0 < ∑ a, Real.exp (v a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    rw [sub_le_iff_le_add', ← Real.log_exp M, ← Real.log_mul hv.ne' (Real.exp_pos _).ne']
    refine Real.log_le_log hu ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [huv a])
  rw [abs_le]
  constructor
  · have := key v u fun a => by linarith [neg_le_of_abs_le (hM a)]
    linarith
  · exact key u v fun a => le_of_abs_le (hM a)

/-- Bound on `|log ∑ₐ exp (uₐ)|` by `log (card α) + M` when `|uₐ| ≤ M` for all `a`. -/
theorem abs_log_sum_exp_le_of_forall (u : α → ℝ) {M : ℝ} (hM : ∀ a, |u a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a))| ≤ Real.log (Fintype.card α) + M := by
  have h_sub := abs_log_sum_exp_sub_le_of_forall (fun _ => 0) u (fun _ => 0) (by simpa using hM)
  have h_zero : (∑ a : α, Real.exp ((0 : ℝ) + 0)) = (Fintype.card α : ℝ) := by
    simp only [add_zero, Real.exp_zero, sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [h_zero] at h_sub
  simp only [add_zero] at h_sub
  have h1 : 1 ≤ (Fintype.card α : ℝ) := by
    have : 1 ≤ Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hlog_nonneg : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg h1
  have h_tri := abs_le.mp h_sub
  rw [abs_le]
  constructor
  · linarith [h_tri.1, hlog_nonneg]
  · linarith [h_tri.2]
