/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.AmbientBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FeatureBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.SampleBottleneck

/-!
# The double-descent curve

The deterministic asymptotic variance, bias and total risk of random-feature regression as a
function of the width ratio `δ = n / m`, for fixed ambient ratio `γ = n₀ / m`
([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]). The three branches are the limits
proved for the three regimes:

* **feature bottleneck** `δ < min {1, γ}`: variance `σ² δ / (1 - δ)`, bias
  `(γ - δ) / (γ (1 - δ)) ρ⋆` (`featureBottleneck_asymptotic_variance_limit`,
  `featureBottleneck_asymptotic_bias_limit`);
* **ambient bottleneck** `γ < 1`, `γ ≤ δ`: variance `σ² γ / (1 - γ)`, no bias
  (`featureBottleneck_asymptotic_variance_limit` with `n := n₀`, `ambientBottleneck_bias_variance`);
* **sample bottleneck** `1 ≤ γ`, `1 ≤ δ`: variance `σ² ((γ - 1)⁻¹ + (δ - 1)⁻¹)`, bias
  `(1 - γ⁻¹) δ / (δ - 1) ρ⋆` (`sampleBottleneck_asymptotic_variance_limit`,
  `sampleBottleneck_asymptotic_bias_limit`).

At the singular values `γ = 1` or `δ = 1` the third branch has Mathlib's junk value `x / 0 = 0`; the
statements below never evaluate there.

For `γ > 1` the total risk is, on both sides of the interpolation threshold `δ = 1`, a multiple of
`|1 - δ|⁻¹` plus a constant, with the *same* coefficient `κ = σ² + (1 - γ⁻¹) ρ⋆`
(`asymptoticTotalRisk_of_feature_of_one_lt`, `asymptoticTotalRisk_of_sample`). Everything in the
global analysis follows from this and from `κ > 0`:

* `double_descent_first_ascent_strictMonoOn`, `double_descent_interpolation_divergence`: the risk
  increases to `+∞` as `δ ↑ 1`;
* `double_descent_second_descent_strictAntiOn`: it decreases strictly for `δ > 1`;
* `double_descent_infinite_width_limit`: it tends to `σ² / (γ - 1) + (1 - γ⁻¹) ρ⋆` as `δ → ∞`;
* `undercomplete_continuousAt_gamma`, `undercomplete_saturated_flat_segment`: for `γ < 1` the risk
  is continuous at `δ = γ` and constant on `δ ≥ γ`.

`κ > 0` is exactly the sharp hypothesis; it holds when `σ², ρ⋆ ≥ 0` and one of them is positive
(`kappa_pos_of_nonneg`).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Filter Topology Set

/-- `x / (x - 1) = 1 + (x - 1)⁻¹`: the bias factor `δ / (δ - 1)` is an affine function of the
decreasing `(δ - 1)⁻¹`. -/
theorem div_sub_one_eq_one_add_inv {x : ℝ} (hx : x ≠ 1) : x / (x - 1) = 1 + (x - 1)⁻¹ := by
  have : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

/-- **Asymptotic variance across all regimes** as a function of `γ = n₀ / m`, `δ = n / m`. -/
noncomputable def asymptoticVariance (σ_sq γ δ : ℝ) : ℝ :=
  if δ < min 1 γ then
    σ_sq * (δ / (1 - δ))
  else if γ < 1 ∧ γ ≤ δ then
    σ_sq * (γ / (1 - γ))
  else
    σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹)

/-- **Asymptotic bias across all regimes**, `ρ_star = ‖θ⋆‖²`. -/
noncomputable def asymptoticBias (ρ_star γ δ : ℝ) : ℝ :=
  if δ < min 1 γ then
    ((γ - δ) / (γ * (1 - δ))) * ρ_star
  else if γ < 1 ∧ γ ≤ δ then
    0
  else
    (1 - γ⁻¹) * (δ / (δ - 1)) * ρ_star

/-- **Total asymptotic risk** `R(δ) = R^(bias)(δ) + R^(var)(δ)`. -/
noncomputable def asymptoticTotalRisk (σ_sq ρ_star γ δ : ℝ) : ℝ :=
  asymptoticBias ρ_star γ δ + asymptoticVariance σ_sq γ δ

section Branches

variable (σ_sq ρ_star : ℝ) {γ δ : ℝ}

/-- Feature-bottleneck branch of `asymptoticVariance`. -/
theorem asymptoticVariance_of_feature (h : δ < min 1 γ) :
    asymptoticVariance σ_sq γ δ = σ_sq * (δ / (1 - δ)) := by
  simp [asymptoticVariance, h]

/-- Ambient-bottleneck branch of `asymptoticVariance`. -/
theorem asymptoticVariance_of_ambient (hγ : γ < 1) (hδ : γ ≤ δ) :
    asymptoticVariance σ_sq γ δ = σ_sq * (γ / (1 - γ)) := by
  have hn : ¬ δ < min 1 γ := not_lt.mpr ((min_le_right _ _).trans hδ)
  simp [asymptoticVariance, hn, hγ, hδ]

/-- Sample-bottleneck branch of `asymptoticVariance`. -/
theorem asymptoticVariance_of_sample (hγ : 1 ≤ γ) (hδ : 1 ≤ δ) :
    asymptoticVariance σ_sq γ δ = σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹) := by
  have hn : ¬ δ < min 1 γ := not_lt.mpr ((min_le_left _ _).trans hδ)
  simp [asymptoticVariance, hn, not_lt.mpr hγ]

/-- Feature-bottleneck branch of `asymptoticBias`. -/
theorem asymptoticBias_of_feature (h : δ < min 1 γ) :
    asymptoticBias ρ_star γ δ = ((γ - δ) / (γ * (1 - δ))) * ρ_star := by
  simp [asymptoticBias, h]

/-- Ambient-bottleneck branch of `asymptoticBias`: the estimator is unbiased. -/
theorem asymptoticBias_of_ambient (hγ : γ < 1) (hδ : γ ≤ δ) :
    asymptoticBias ρ_star γ δ = 0 := by
  have hn : ¬ δ < min 1 γ := not_lt.mpr ((min_le_right _ _).trans hδ)
  simp [asymptoticBias, hn, hγ, hδ]

/-- Sample-bottleneck branch of `asymptoticBias`. -/
theorem asymptoticBias_of_sample (hγ : 1 ≤ γ) (hδ : 1 ≤ δ) :
    asymptoticBias ρ_star γ δ = (1 - γ⁻¹) * (δ / (δ - 1)) * ρ_star := by
  have hn : ¬ δ < min 1 γ := not_lt.mpr ((min_le_left _ _).trans hδ)
  simp [asymptoticBias, hn, not_lt.mpr hγ]

/-- Total risk in the feature-bottleneck regime. -/
theorem asymptoticTotalRisk_of_feature (h : δ < min 1 γ) :
    asymptoticTotalRisk σ_sq ρ_star γ δ =
      ((γ - δ) / (γ * (1 - δ))) * ρ_star + σ_sq * (δ / (1 - δ)) := by
  rw [asymptoticTotalRisk, asymptoticBias_of_feature ρ_star h,
    asymptoticVariance_of_feature σ_sq h]

/-- Total risk in the ambient-bottleneck regime: constant in `δ`. -/
theorem asymptoticTotalRisk_of_ambient (hγ : γ < 1) (hδ : γ ≤ δ) :
    asymptoticTotalRisk σ_sq ρ_star γ δ = σ_sq * (γ / (1 - γ)) := by
  rw [asymptoticTotalRisk, asymptoticBias_of_ambient ρ_star hγ hδ,
    asymptoticVariance_of_ambient σ_sq hγ hδ, zero_add]

/-- **Total risk in the sample-bottleneck regime** `γ, δ > 1`:
`σ² (γ - 1)⁻¹ + (1 - γ⁻¹) ρ⋆ + κ (δ - 1)⁻¹` with `κ = σ² + (1 - γ⁻¹) ρ⋆`. -/
theorem asymptoticTotalRisk_of_sample (hγ : 1 < γ) (hδ : 1 < δ) :
    asymptoticTotalRisk σ_sq ρ_star γ δ =
      σ_sq * (γ - 1)⁻¹ + (1 - γ⁻¹) * ρ_star + (σ_sq + (1 - γ⁻¹) * ρ_star) * (δ - 1)⁻¹ := by
  have h1 : γ - 1 ≠ 0 := (sub_pos.mpr hγ).ne'
  have h2 : δ - 1 ≠ 0 := (sub_pos.mpr hδ).ne'
  rw [asymptoticTotalRisk, asymptoticBias_of_sample ρ_star hγ.le hδ.le,
    asymptoticVariance_of_sample σ_sq hγ.le hδ.le]
  rw [div_sub_one_eq_one_add_inv hδ.ne']
  ring

/-- **Total risk below the interpolation threshold for `γ > 1`** (`δ < 1`):
`κ (1 - δ)⁻¹ + (γ⁻¹ ρ⋆ - σ²)` with the same `κ = σ² + (1 - γ⁻¹) ρ⋆` as for `δ > 1`. -/
theorem asymptoticTotalRisk_of_feature_of_one_lt (hγ : 1 < γ) (hδ : δ < 1) :
    asymptoticTotalRisk σ_sq ρ_star γ δ =
      (σ_sq + (1 - γ⁻¹) * ρ_star) * (1 - δ)⁻¹ + (γ⁻¹ * ρ_star - σ_sq) := by
  have hγ0 : γ ≠ 0 := by positivity
  have h2 : 1 - δ ≠ 0 := (sub_pos.mpr hδ).ne'
  rw [asymptoticTotalRisk_of_feature σ_sq ρ_star (lt_min hδ (hδ.trans hγ))]
  field_simp
  ring

end Branches

section KappaFacts

/-- The coefficient `κ = σ² + (1 - γ⁻¹) ρ⋆` is positive when `σ², ρ⋆ ≥ 0`, not both zero, and
`γ > 1`. -/
theorem kappa_pos_of_nonneg {σ_sq ρ_star γ : ℝ} (hγ : 1 < γ) (hσ : 0 ≤ σ_sq) (hρ : 0 ≤ ρ_star)
    (h_pos : 0 < σ_sq ∨ 0 < ρ_star) : 0 < σ_sq + (1 - γ⁻¹) * ρ_star := by
  have hγ' : 0 < 1 - γ⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hγ)
  rcases h_pos with h | h
  · exact add_pos_of_pos_of_nonneg h (mul_nonneg hγ'.le hρ)
  · exact add_pos_of_nonneg_of_pos hσ (mul_pos hγ' h)

end KappaFacts

section Curve

variable {σ_sq ρ_star γ : ℝ}

/-- **First ascent** (`γ > 1`, `κ > 0`): below the interpolation threshold the total risk is
strictly increasing in `δ`. -/
theorem double_descent_first_ascent_strictMonoOn (hγ : 1 < γ)
    (hκ : 0 < σ_sq + (1 - γ⁻¹) * ρ_star) :
    StrictMonoOn (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) (Iio 1) := by
  intro a ha b hb hab
  simp only
  rw [asymptoticTotalRisk_of_feature_of_one_lt σ_sq ρ_star hγ ha,
    asymptoticTotalRisk_of_feature_of_one_lt σ_sq ρ_star hγ hb]
  have hb' : 0 < 1 - b := sub_pos.mpr hb
  have : (1 - a)⁻¹ < (1 - b)⁻¹ := (inv_lt_inv₀ (sub_pos.mpr ha) hb').mpr (by linarith)
  nlinarith

/-- **Divergence at the interpolation threshold** (`γ > 1`, `κ > 0`): as `δ ↑ 1` the total risk
tends to `+∞`. -/
theorem double_descent_interpolation_divergence (hγ : 1 < γ)
    (hκ : 0 < σ_sq + (1 - γ⁻¹) * ρ_star) :
    Tendsto (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) (𝓝[<] 1) atTop := by
  have hinv : Tendsto (fun δ : ℝ => (1 - δ)⁻¹) (𝓝[<] 1) atTop := by
    refine Filter.Tendsto.inv_tendsto_nhdsGT_zero ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun δ : ℝ => 1 - δ) (𝓝[<] 1) (𝓝 (1 - 1)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with δ hδ using sub_pos.mpr (mem_Iio.mp hδ)
  have h := (hinv.const_mul_atTop hκ).atTop_add (tendsto_const_nhds (x := γ⁻¹ * ρ_star - σ_sq))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (asymptoticTotalRisk_of_feature_of_one_lt σ_sq ρ_star hγ (mem_Iio.mp hδ)).symm

/-- **Divergence at the interpolation threshold**, in the form of the plan: `σ², ρ⋆ ≥ 0`, not both
zero. -/
theorem double_descent_interpolation_divergence_of_nonneg (hγ : 1 < γ) (hσ : 0 ≤ σ_sq)
    (hρ : 0 ≤ ρ_star) (h_pos : 0 < σ_sq ∨ 0 < ρ_star) :
    Tendsto (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) (𝓝[<] 1) atTop :=
  double_descent_interpolation_divergence hγ (kappa_pos_of_nonneg hγ hσ hρ h_pos)

/-- **Second descent** (`γ > 1`, `κ > 0`): beyond the interpolation threshold the total risk is
strictly decreasing in `δ`. -/
theorem double_descent_second_descent_strictAntiOn (hγ : 1 < γ)
    (hκ : 0 < σ_sq + (1 - γ⁻¹) * ρ_star) :
    StrictAntiOn (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) (Ioi 1) := by
  intro a ha b hb hab
  simp only
  rw [asymptoticTotalRisk_of_sample σ_sq ρ_star hγ hb,
    asymptoticTotalRisk_of_sample σ_sq ρ_star hγ ha]
  have ha' : 0 < a - 1 := sub_pos.mpr ha
  have : (b - 1)⁻¹ < (a - 1)⁻¹ := (inv_lt_inv₀ (sub_pos.mpr hb) ha').mpr (by linarith)
  nlinarith

/-- **Second descent**, in the form of the plan: `σ², ρ⋆ ≥ 0`, not both zero. -/
theorem double_descent_second_descent_strictly_decreasing (hγ : 1 < γ) (hσ : 0 ≤ σ_sq)
    (hρ : 0 ≤ ρ_star) (h_pos : 0 < σ_sq ∨ 0 < ρ_star) {δ₁ δ₂ : ℝ} (h1 : 1 < δ₁)
    (hle : δ₁ < δ₂) :
    asymptoticTotalRisk σ_sq ρ_star γ δ₂ < asymptoticTotalRisk σ_sq ρ_star γ δ₁ :=
  double_descent_second_descent_strictAntiOn hγ (kappa_pos_of_nonneg hγ hσ hρ h_pos) h1
    (h1.trans hle) hle

/-- **Infinite-width limit** (`γ > 1`): the second descent levels off at
`σ² / (γ - 1) + (1 - γ⁻¹) ρ⋆`, the risk of ridgeless regression on the raw inputs `X`. -/
theorem double_descent_infinite_width_limit (hγ : 1 < γ) :
    Tendsto (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) atTop
      (𝓝 (σ_sq / (γ - 1) + (1 - γ⁻¹) * ρ_star)) := by
  have hinv : Tendsto (fun δ : ℝ => (δ - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have h := (hinv.const_mul (σ_sq + (1 - γ⁻¹) * ρ_star)).const_add
    (σ_sq * (γ - 1)⁻¹ + (1 - γ⁻¹) * ρ_star)
  have h' : Tendsto (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) atTop
      (𝓝 (σ_sq * (γ - 1)⁻¹ + (1 - γ⁻¹) * ρ_star + (σ_sq + (1 - γ⁻¹) * ρ_star) * 0)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with δ hδ
    exact (asymptoticTotalRisk_of_sample σ_sq ρ_star hγ hδ).symm
  simpa [div_eq_mul_inv] using h'

end Curve

section Undercomplete

variable {σ_sq ρ_star γ : ℝ}

/-- **Saturated flat segment** (`γ < 1`): once the width reaches the ambient dimension
(`δ ≥ γ`), further width does not change the risk, which equals `σ² γ / (1 - γ)`. -/
theorem undercomplete_saturated_flat_segment (hγ : γ < 1) {δ : ℝ} (hδ : γ ≤ δ) :
    asymptoticTotalRisk σ_sq ρ_star γ δ = σ_sq * (γ / (1 - γ)) :=
  asymptoticTotalRisk_of_ambient σ_sq ρ_star hγ hδ

/-- **The total risk is continuous at the ambient boundary `δ = γ`** (`0 < γ < 1`): the feature
branch `δ < γ` meets the flat ambient branch with no jump. -/
theorem undercomplete_continuousAt_gamma (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    ContinuousAt (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) γ := by
  have h1 : 1 - γ ≠ 0 := (sub_pos.mpr hγ₁).ne'
  -- the feature-branch formula, continuous at `γ`
  have hg : ContinuousAt
      (fun δ : ℝ => (γ - δ) / (γ * (1 - δ)) * ρ_star + σ_sq * (δ / (1 - δ))) γ :=
    ((((continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
      (mul_ne_zero hγ₀.ne' h1)).mul_const ρ_star).add
      (continuousAt_const.mul (continuousAt_id.div (continuousAt_const.sub continuousAt_id) h1)))
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨hg.continuousWithinAt.congr (fun δ hδ => ?_) ?_, ?_⟩
  · rcases (mem_Iic.mp hδ).lt_or_eq with h | h
    · exact asymptoticTotalRisk_of_feature σ_sq ρ_star (lt_min (h.trans hγ₁) h)
    · subst h
      rw [asymptoticTotalRisk_of_ambient σ_sq ρ_star hγ₁ le_rfl]
      simp
  · rw [asymptoticTotalRisk_of_ambient σ_sq ρ_star hγ₁ le_rfl]
    simp
  · exact (continuousWithinAt_const (b := σ_sq * (γ / (1 - γ)))).congr
      (fun δ hδ => undercomplete_saturated_flat_segment hγ₁ hδ)
      (undercomplete_saturated_flat_segment hγ₁ le_rfl)

/-- **No jump at the ambient boundary**, as a left limit: `R(δ) → σ² γ / (1 - γ)` as `δ ↑ γ`. -/
theorem undercomplete_continuous_transition_at_gamma (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    Tendsto (fun δ => asymptoticTotalRisk σ_sq ρ_star γ δ) (𝓝[<] γ)
      (𝓝 (σ_sq * (γ / (1 - γ)))) := by
  have h := (undercomplete_continuousAt_gamma (σ_sq := σ_sq) (ρ_star := ρ_star) hγ₀ hγ₁).tendsto
  rw [undercomplete_saturated_flat_segment hγ₁ le_rfl] at h
  exact h.mono_left nhdsWithin_le_nhds

end Undercomplete

end LinearRegression.DoubleDescent

end
