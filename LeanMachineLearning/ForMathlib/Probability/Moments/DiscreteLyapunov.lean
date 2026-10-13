/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lyapunov monotonicity of a finite weighted log-partition function

For a finite family of nonnegative weights `w a` (not all zero) and a function `f`, the normalized
log-moment-generating function
`β ↦ β⁻¹ (log ∑ₐ w a exp (β f a) - log ∑ₐ w a)` is non-decreasing on `(0, ∞)`
(`monotoneOn_inv_mul_log_sum_mul_exp_sub_log_sum`).  With `p = w / ∑ w` it is
`β ↦ β⁻¹ log 𝔼_p exp (β f) = log ‖exp f‖_{L^β(p)}`, and the claim is the power-mean inequality
`(𝔼_p z)^q ≤ 𝔼_p z^q` for `z = exp (β₁ f)` and `q = β₂ / β₁ ≥ 1`.  The uniform case `w ≡ 1` is the
Gibbs monotonicity used for the SK model (`SpinGlasses/ThermodynamicLimit.lean`); general weights
cover reference measures such as the weights `G` of `SpinGlasses/GaussianIBP.lean`.
-/

@[expose] public section

open Finset

/-- **Lyapunov monotonicity for nonnegative weights:** for `w ≥ 0` with positive total mass,
`β ↦ β⁻¹ (log ∑ₐ w a exp (β f a) - log ∑ₐ w a)` is non-decreasing on `(0, ∞)`. -/
theorem monotoneOn_inv_mul_log_sum_mul_exp_sub_log_sum {α : Type*} [Fintype α] (f w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw : 0 < ∑ a, w a) :
    MonotoneOn (fun β => β⁻¹ * (Real.log (∑ a, w a * Real.exp (β * f a)) -
      Real.log (∑ a, w a))) (Set.Ioi 0) := by
  have hex : ∃ a, 0 < w a := by
    by_contra h
    push Not at h
    exact absurd hw (not_lt.2 (Finset.sum_nonpos fun a _ => h a))
  obtain ⟨a₀, ha₀⟩ := hex
  intro β₁ (hβ₁ : 0 < β₁) β₂ (hβ₂ : 0 < β₂) hle
  have hZ : ∀ β : ℝ, 0 < ∑ a, w a * Real.exp (β * f a) := fun β =>
    Finset.sum_pos' (fun a _ => mul_nonneg (hw0 a) (Real.exp_pos _).le)
      ⟨a₀, mem_univ _, mul_pos ha₀ (Real.exp_pos _)⟩
  have hmean : ∀ β : ℝ, 0 < ∑ a, w a / (∑ b, w b) * Real.exp (β * f a) := fun β => by
    have : ∑ a, w a / (∑ b, w b) * Real.exp (β * f a) =
        (∑ a, w a * Real.exp (β * f a)) / ∑ b, w b := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]; exact div_pos (hZ β) hw
  have hlog : ∀ β : ℝ, Real.log (∑ a, w a / (∑ b, w b) * Real.exp (β * f a)) =
      Real.log (∑ a, w a * Real.exp (β * f a)) - Real.log (∑ a, w a) := fun β => by
    have : ∑ a, w a / (∑ b, w b) * Real.exp (β * f a) =
        (∑ a, w a * Real.exp (β * f a)) / ∑ b, w b := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, Real.log_div (hZ β).ne' hw.ne']
  have hpow := Real.rpow_arith_mean_le_arith_mean_rpow univ (fun a => w a / ∑ b, w b)
    (fun a => Real.exp (β₁ * f a)) (fun a _ => div_nonneg (hw0 a) hw.le)
    (by rw [← Finset.sum_div, div_self hw.ne']) (fun _ _ => (Real.exp_pos _).le)
    ((one_le_div hβ₁).2 hle)
  have hexp : ∀ a, Real.exp (β₁ * f a) ^ (β₂ / β₁) = Real.exp (β₂ * f a) := fun a => by
    rw [← Real.exp_mul]; congr 1; field_simp
  simp only [hexp] at hpow
  have hlogpow := Real.log_le_log (Real.rpow_pos_of_pos (hmean β₁) _) hpow
  rw [Real.log_rpow (hmean β₁), hlog, hlog] at hlogpow
  change β₁⁻¹ * _ ≤ β₂⁻¹ * _
  calc β₁⁻¹ * (Real.log (∑ a, w a * Real.exp (β₁ * f a)) - Real.log (∑ a, w a))
      = β₂⁻¹ * (β₂ / β₁ * (Real.log (∑ a, w a * Real.exp (β₁ * f a)) -
          Real.log (∑ a, w a))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow (inv_nonneg.2 hβ₂.le)
