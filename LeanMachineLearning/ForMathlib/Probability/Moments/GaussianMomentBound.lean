/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bounds on products of scaled Gaussian moments

The moments of a centered Gaussian satisfy `|𝔼 g^n| ≤ n!`. A product of scaled moments
`∏_k 𝔼 (σ g)^{n_k}` is therefore bounded by `(∏ n_k!) σ^{∑ n_k}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Nat

namespace ProbabilityTheory

/-- The moments of the standard Gaussian satisfy `|𝔼 g^n| ≤ n!`. -/
theorem abs_integral_pow_gaussianReal_le (n : ℕ) :
    |∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)| ≤ (n ! : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [integral_id_gaussianReal]
  | more n ih1 ih2 =>
    rw [integral_pow_add_two_gaussianReal, abs_mul]
    have h1 : |((n : ℝ) + 1)| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
    rw [h1, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hb : (0 : ℝ) ≤ ((n : ℝ) + 1) * (n ! : ℝ) := by positivity
    calc ((n : ℝ) + 1) * |∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)| ≤ ((n : ℝ) + 1) * (n ! : ℝ) :=
          mul_le_mul_of_nonneg_left ih1 (by positivity)
      _ ≤ ((n : ℝ) + 1 + 1) * (((n : ℝ) + 1) * (n ! : ℝ)) :=
          le_mul_of_one_le_left hb (by linarith)

/-- A product of scaled Gaussian moments is bounded by `(∏ n_k!) σ^{∑ n_k}`. -/
theorem abs_prod_integral_pow_scaled_gaussianReal_le {ι : Type*} [Fintype ι] (c : ι → ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    |∏ k, ∫ x : ℝ, (σ * x) ^ (c k) ∂(gaussianReal 0 1)| ≤
      (∏ k, ((c k) ! : ℝ)) * σ ^ (∑ k, c k) := by
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => ?_
  have : ∫ x : ℝ, (σ * x) ^ (c k) ∂(gaussianReal 0 1) =
      σ ^ (c k) * ∫ x : ℝ, x ^ (c k) ∂(gaussianReal 0 1) := by
    simp only [mul_pow]
    rw [integral_const_mul]
  rw [this, abs_mul, abs_of_nonneg (pow_nonneg hσ _), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_integral_pow_gaussianReal_le _) (pow_nonneg hσ _)

end ProbabilityTheory
