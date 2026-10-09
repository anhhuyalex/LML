/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.FeatureLearning.Criterion

/-!
# Feature learning: the scaling regimes and the balance condition

Two numbers govern a gradient step of size `η` on the width-`n` network with scaling knob `γ`
(`featureLearningNetwork`):

* the **feature motion** `(η / (γ √n))²`, the normalized squared displacement of the hidden
  preactivations (`one_step_preactivation_update`, Definition 4.1 in `Criterion`), and
* the **function motion** `η / γ²`, the speed of the predictor
  (`hasDerivAt_predictor_featureLearningNetwork`: `∂ₜ f = -(η / (m γ²)) K r`, where the normalized
  kernel `K` and the residual `r` are of order one).

No new definition is introduced: both scales are written out, and a regime is a hypothesis on
`(γ, η)` rather than a value of a `ScalingRegime` type.

## Main results and proof outline

* `scales_isTheta` (master scaling lemma): the two scales only depend on `(γ, η)` up to `=Θ`;
  `IsTheta.mul`, `.div`, `.pow`.  Every regime theorem below is this lemma applied to a reference
  pair `(γ', η')`.
* `scaling_lazy_ntk_dynamics` (`γ = 1`, `η = Θ(1)`): feature motion `Θ(n⁻¹) → 0`, function motion
  `Θ(1)`.
* `isLittleO_sqrt_of_lazy_learningRate`: `η = O(1)` is below the feature-learning scale,
  `η = o(√n)` (input to the kernel freeze of `Stability`).
* `scaling_naive_large_eta_instability` (`γ = 1`, `η = Θ(√n)`): feature motion `Θ(1)`, function
  motion `Θ(√n) → ∞`.
* `scaling_mean_field_muP_balance` (`γ = √n`, `η = Θ(n)`): both scales are `Θ(1)`.
* `featureMotion_and_functionMotion_isTheta_one_iff`, `unique_scaling_balance_solution`: both scales
  are `Θ(1)` if and only if `γ = Θ(√n)` and `η = Θ(n)`.  The feature half is
  `featureLearning_criterion_iff_learningRate`; the function half is
  `isTheta_iff_div_isTheta_one` applied to `η` and `γ²`.
-/

@[expose] public section

open Asymptotics Filter
open scoped Topology

namespace NTK

/-- **Master scaling lemma.** The feature motion `(η / (γ √n))²` and the function motion `η / γ²`
are `=Θ`-invariant in `γ` and `η`: if `γ = Θ(γ')` and `η = Θ(η')`, they are `Θ` of the same two
expressions in `(γ', η')`. -/
theorem scales_isTheta {γ γ' η η' : ℕ → ℝ} (hγ : γ =Θ[atTop] γ') (hη : η =Θ[atTop] η') :
    (fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2) =Θ[atTop]
        (fun n : ℕ => (η' n / (γ' n * Real.sqrt n)) ^ 2) ∧
      (fun n : ℕ => η n / γ n ^ 2) =Θ[atTop] (fun n : ℕ => η' n / γ' n ^ 2) :=
  ⟨(hη.div (hγ.mul (isTheta_refl (fun n : ℕ => Real.sqrt n) atTop))).pow 2,
    hη.div (hγ.pow 2)⟩

/-- **Regime 1 (lazy / NTK).** With `γ = 1` and `η = Θ(1)` the hidden features barely move (feature
motion `Θ(n⁻¹) → 0`) while the predictor moves at speed `Θ(1)`. -/
theorem scaling_lazy_ntk_dynamics {η : ℕ → ℝ} (hη : η =Θ[atTop] fun _ => (1 : ℝ)) :
    (fun n : ℕ => (η n / (1 * Real.sqrt n)) ^ 2) =Θ[atTop] (fun n : ℕ => (n : ℝ)⁻¹) ∧
      Tendsto (fun n : ℕ => (η n / (1 * Real.sqrt n)) ^ 2) atTop (𝓝 0) ∧
      (fun n : ℕ => η n / (1 : ℝ) ^ 2) =Θ[atTop] fun _ => (1 : ℝ) := by
  obtain ⟨hfeat, hfun⟩ := scales_isTheta (isTheta_refl (fun _ : ℕ => (1 : ℝ)) atTop) hη
  have h : (fun n : ℕ => ((1 : ℝ) / (1 * Real.sqrt n)) ^ 2) = fun n : ℕ => (n : ℝ)⁻¹ := by
    funext n
    rw [one_mul, div_pow, Real.sq_sqrt n.cast_nonneg, one_pow, one_div]
  rw [h] at hfeat
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨hfeat, hfeat.isBigO.trans_tendsto hinv, ?_⟩
  simpa using hfun

/-- In the lazy regime the learning rate is below the feature-learning scale: `η = O(1)` implies
`η = o(γ √n)` for `γ = 1`.  (By `featureLearning_criterion_iff_learningRate` the complement of
`η = o(γ √n)` is not the criterion, but `η = o(γ √n)` does exclude it.) -/
theorem isLittleO_sqrt_of_lazy_learningRate {η : ℕ → ℝ} (hη : η =O[atTop] fun _ => (1 : ℝ)) :
    η =o[atTop] fun n : ℕ => (1 : ℝ) * Real.sqrt n := by
  have hsqrt : Tendsto (fun n : ℕ => ‖(1 : ℝ) * Real.sqrt (n : ℝ)‖) atTop atTop := by
    refine (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact hη.trans_isLittleO (isLittleO_const_left.2 (Or.inr hsqrt))

/-- **Regime 2 (naive large learning rate).** With `γ = 1` and `η = Θ(√n)` the features move at
order one (feature motion `Θ(1)`, so features are learned) but the predictor moves at speed
`Θ(√n) → ∞`: the function-space dynamics blow up. -/
theorem scaling_naive_large_eta_instability {η : ℕ → ℝ}
    (hη : η =Θ[atTop] fun n : ℕ => Real.sqrt n) :
    (fun n : ℕ => (η n / (1 * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n : ℕ => η n / (1 : ℝ) ^ 2) =Θ[atTop] (fun n : ℕ => Real.sqrt n) ∧
      Tendsto (fun n : ℕ => ‖η n / (1 : ℝ) ^ 2‖) atTop atTop := by
  have hfun : (fun n : ℕ => η n / (1 : ℝ) ^ 2) =Θ[atTop] (fun n : ℕ => Real.sqrt n) := by
    simpa using hη
  refine ⟨?_, hfun, ?_⟩
  · simpa using (featureLearning_criterion_iff_learningRate η (fun _ => 1) fun _ => one_pos).2
      (by simpa using hη)
  · have hsqrt : Tendsto (fun n : ℕ => ‖Real.sqrt (n : ℝ)‖) atTop atTop := by
      refine (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
      exact (Real.norm_of_nonneg (Real.sqrt_nonneg _)).symm
    exact hfun.tendsto_norm_atTop_iff.2 hsqrt

/-- **Regime 3 (mean field / `μP`).** With `γ = √n` and `η = Θ(n)` (for instance `η = η₀ n`,
`scaling_mean_field_muP_balance`) both the feature motion and the function motion are `Θ(1)`. -/
theorem scaling_mean_field_isTheta_one {η : ℕ → ℝ} (hη : η =Θ[atTop] fun n : ℕ => (n : ℝ)) :
    (fun n : ℕ => (η n / (Real.sqrt n * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n : ℕ => η n / Real.sqrt n ^ 2) =Θ[atTop] fun _ => (1 : ℝ) := by
  have h : ∀ n : ℕ, Real.sqrt (n : ℝ) * Real.sqrt n = n := fun n => Real.mul_self_sqrt n.cast_nonneg
  have h' : ∀ n : ℕ, Real.sqrt (n : ℝ) ^ 2 = n := fun n => Real.sq_sqrt n.cast_nonneg
  simp_rw [h, h']
  have hn : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn using by positivity
  refine ⟨(isTheta_sq_div_one_iff hn).2 hη, (isTheta_iff_div_isTheta_one hn).1 hη⟩

/-- **Regime 3 (mean field / `μP`), `η = η₀ n`.** The mean-field choice `γ = √n`, `η = η₀ n` with a
fixed `η₀ ≠ 0` balances both motions at order one. -/
theorem scaling_mean_field_muP_balance {η₀ : ℝ} (hη₀ : η₀ ≠ 0) :
    (fun n : ℕ => (η₀ * n / (Real.sqrt n * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n : ℕ => η₀ * n / Real.sqrt n ^ 2) =Θ[atTop] fun _ => (1 : ℝ) :=
  scaling_mean_field_isTheta_one ((isTheta_const_mul_left hη₀).2 (isTheta_refl _ _))

section Balance

variable {γ η : ℕ → ℝ}

/-- **Balance of the two scales.** Feature motion and function motion are both `Θ(1)` if and only
if `η = Θ(γ √n)` and `η = Θ(γ²)`. -/
theorem featureMotion_and_functionMotion_isTheta_one_iff (hγ : ∀ᶠ n : ℕ in atTop, γ n ≠ 0) :
    ((fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n : ℕ => η n / γ n ^ 2) =Θ[atTop] fun _ => (1 : ℝ)) ↔
    (η =Θ[atTop] fun n : ℕ => γ n * Real.sqrt n) ∧ η =Θ[atTop] fun n : ℕ => γ n ^ 2 := by
  have hs : ∀ᶠ n : ℕ in atTop, γ n * Real.sqrt n ≠ 0 := by
    filter_upwards [hγ, eventually_gt_atTop 0] with n h hn
    exact mul_ne_zero h (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [isTheta_sq_div_one_iff hs, ← isTheta_iff_div_isTheta_one (hγ.mono fun n h => pow_ne_zero 2 h)]

/-- **Unique balanced scaling.** For a positive width-dependent knob `γ`, the two balance
conditions `η = Θ(γ √n)` (feature motion of order one) and `η = Θ(γ²)` (function motion of order
one) hold simultaneously if and only if `γ = Θ(√n)` and `η = Θ(n)`: the mean-field scaling is the
only one that learns features without destabilizing the predictor. -/
theorem unique_scaling_balance_solution (hγ : ∀ᶠ n : ℕ in atTop, γ n ≠ 0) :
    ((η =Θ[atTop] fun n : ℕ => γ n * Real.sqrt n) ∧ η =Θ[atTop] fun n : ℕ => γ n ^ 2) ↔
      (γ =Θ[atTop] fun n : ℕ => Real.sqrt n) ∧ η =Θ[atTop] fun n : ℕ => (n : ℝ) := by
  have hsq : (fun n : ℕ => Real.sqrt (n : ℝ) * Real.sqrt n) = fun n : ℕ => (n : ℝ) := by
    funext n
    exact Real.mul_self_sqrt n.cast_nonneg
  constructor
  · rintro ⟨hfeat, hfun⟩
    -- cancel one factor `γ` from `γ √n =Θ γ²`
    have hγ' : (fun n : ℕ => Real.sqrt n) =Θ[atTop] γ := by
      have h := (hfeat.symm.trans hfun).div (isTheta_refl γ atTop)
      refine (EventuallyEq.isTheta ?_).trans (h.trans (EventuallyEq.isTheta ?_))
      · filter_upwards [hγ] with n hn
        simp [mul_div_cancel_left₀ _ hn]
      · filter_upwards [hγ] with n hn
        simp [pow_two, mul_div_cancel_left₀ _ hn]
    refine ⟨hγ'.symm, ?_⟩
    simpa [hsq] using
      hfeat.trans (hγ'.symm.mul (isTheta_refl (fun n : ℕ => Real.sqrt n) atTop))
  · rintro ⟨hγ', hη⟩
    refine ⟨hη.trans ?_, hη.trans ?_⟩
    · simpa [hsq] using (hγ'.mul (isTheta_refl (fun n : ℕ => Real.sqrt n) atTop)).symm
    · simpa [hsq] using (hγ'.pow 2).symm

/-- The balance `unique_scaling_balance_solution` in terms of the two motions. -/
theorem featureMotion_and_functionMotion_isTheta_one_iff_meanField
    (hγ : ∀ᶠ n : ℕ in atTop, γ n ≠ 0) :
    ((fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n : ℕ => η n / γ n ^ 2) =Θ[atTop] fun _ => (1 : ℝ)) ↔
    (γ =Θ[atTop] fun n : ℕ => Real.sqrt n) ∧ η =Θ[atTop] fun n : ℕ => (n : ℝ) :=
  (featureMotion_and_functionMotion_isTheta_one_iff hγ).trans
    (unique_scaling_balance_solution hγ)

end Balance

end NTK
