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

/-- Select a function or the constant one using a predicate on a separate index. -/
theorem differentiable_and_abs_deriv_le_ite_one {R : Type*} {p : R → Prop} [DecidablePred p]
    {g : ℝ → ℝ} {B₀ B₁ B₂ : ℝ}
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (hb₀ : ∀ x, |g x| ≤ B₀) (hb₁ : ∀ x, |deriv g x| ≤ B₁)
    (hb₂ : ∀ x, |deriv (deriv g) x| ≤ B₂)
    (h₀ : 1 ≤ B₀) (h₁ : 0 ≤ B₁) (h₂ : 0 ≤ B₂) :
    let ψ (r : R) := fun x => if p r then g x else 1
    (∀ r, Differentiable ℝ (ψ r)) ∧ (∀ r, Differentiable ℝ (deriv (ψ r))) ∧
      (∀ r x, |ψ r x| ≤ B₀) ∧ (∀ r x, |deriv (ψ r) x| ≤ B₁) ∧
      (∀ r x, |deriv (deriv (ψ r)) x| ≤ B₂) := by
  dsimp only
  simp only [← forall_and]
  intro r
  by_cases hp : p r
  · simp only [hp, ite_true]
    exact ⟨hg, hg', fun x => ⟨hb₀ x, hb₁ x, hb₂ x⟩⟩
  · simp [hp, h₀, h₁, h₂]
