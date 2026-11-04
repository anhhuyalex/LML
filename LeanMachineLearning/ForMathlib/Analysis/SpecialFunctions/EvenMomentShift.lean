/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-! # Stability of even moments under small deterministic shifts -/

@[expose] public section

/-- A deterministic shift of size at most `L / s` preserves an even-moment bound of
order `s⁻ᵏ`, for any positive normalized linear expectation and `s ≥ 1`. -/
theorem positive_linear_even_moment_add_le {α : Type} (E : (α → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ x, f x ≤ g x) → E f ≤ E g)
    (hone : E (fun _ => 1) = 1) (f : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (s C L δ : ℝ) (hs : 1 ≤ s) (hL : 0 ≤ L)
    (hf : E (fun x => f x ^ (2 * k)) ≤ C / s ^ k)
    (hδ : |δ| ≤ L / s) :
    E (fun x => (f x + δ) ^ (2 * k)) ≤
      (2 : ℝ) ^ (2 * k - 1) * (C + L ^ (2 * k)) / s ^ k := by
  have hs0 : 0 < s := by linarith
  have hδpow : δ ^ (2 * k) ≤ L ^ (2 * k) / s ^ k := by
    have h := pow_le_pow_left₀ (abs_nonneg δ) hδ (2 * k)
    rw [← abs_pow, abs_of_nonneg (Even.pow_nonneg (even_two_mul k) δ), div_pow] at h
    have hden : s ^ k ≤ s ^ (2 * k) := by
      apply pow_le_pow_right₀ hs
      omega
    exact h.trans (div_le_div_of_nonneg_left (pow_nonneg hL _) (by positivity) hden)
  have hpoint (x : α) : (f x + δ) ^ (2 * k) ≤
      (2 : ℝ) ^ (2 * k - 1) * (f x ^ (2 * k) + δ ^ (2 * k)) :=
    add_pow_two_mul_le hk _ _
  calc
    _ ≤ E (fun x => (2 : ℝ) ^ (2 * k - 1) *
        (f x ^ (2 * k) + δ ^ (2 * k))) := hmono _ _ hpoint
    _ = (2 : ℝ) ^ (2 * k - 1) * (E (fun x => f x ^ (2 * k)) + δ ^ (2 * k)) := by
      rw [show (fun x : α => (2 : ℝ) ^ (2 * k - 1) *
          (f x ^ (2 * k) + δ ^ (2 * k))) =
          (2 : ℝ) ^ (2 * k - 1) • ((fun x => f x ^ (2 * k)) +
            δ ^ (2 * k) • (fun _ => 1)) by ext x; simp]
      simp only [map_smul, map_add, hone, smul_eq_mul, mul_one]
    _ ≤ (2 : ℝ) ^ (2 * k - 1) * (C / s ^ k + L ^ (2 * k) / s ^ k) := by
      gcongr
    _ = _ := by ring

