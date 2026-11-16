/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz bounds from bounded iterated derivatives

The differentiability assumptions express existence of the derivatives, separately from bounds
on Lean's total `iteratedDeriv`. Continuity of the highest derivative is not required.
For `n = 3` these are the regularity assumptions in Talagrand's perceptron hypothesis (2.7).
-/

@[expose] public section

/-- If derivatives through order `n` exist and have modulus at most `D`, then `D` is nonnegative
and every derivative of order less than `n` is `D`-Lipschitz. The order-zero bound is included;
the statement also covers `n = 0`, when there is no differentiability assumption. -/
theorem lipschitzWith_iteratedDeriv_of_forall_abs_le {u : ℝ → ℝ} {n : ℕ} {D : ℝ}
    (hd : ∀ j < n, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ n, ∀ x, |iteratedDeriv j u x| ≤ D) :
    0 ≤ D ∧ ∀ j < n, LipschitzWith D.toNNReal (iteratedDeriv j u) := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hb 0 (Nat.zero_le n) 0)
  refine ⟨hD, fun j hj => lipschitzWith_of_nnnorm_deriv_le (hd j hj) fun x => ?_⟩
  change ‖deriv (iteratedDeriv j u) x‖ ≤ (D.toNNReal : ℝ)
  rw [Real.coe_toNNReal D hD, Real.norm_eq_abs, ← iteratedDeriv_succ]
  exact hb (j + 1) (by omega) x
