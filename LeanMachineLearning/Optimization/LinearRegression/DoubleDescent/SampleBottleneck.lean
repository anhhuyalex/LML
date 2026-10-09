/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.Basic
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FeatureBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomFeatures

/-!
# The sample-bottleneck regime

Random-feature regression with `m` samples, `n` random features and ambient dimension `n₀` in the
overparameterized regime `m < n₀` and `m < n` (`γ = n₀ / m > 1`, `δ = n / m > 1`): the projected
design `Z = X S ∈ ℝ^{m × n}` has full row rank, so `Z Zᵀ` is invertible and the fit is the
minimum-norm interpolator `η̂ = Zᵀ (Z Zᵀ)⁻¹ y`, `θ̂ = S η̂ = M y` with `M = S Zᵀ (Z Zᵀ)⁻¹`
([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]).

The interpolation and minimum-norm properties of `η̂` are `rightInverse_interpolates`,
`rightInverse_norm_sq_decomp` and `eq_rightInverse_of_norm_le` of `RandomFeatures.lean`. This file
contains the remaining exact finite-sample reduction and the deterministic limits:

* `sampleBottleneck_interpolates_training_targets`: the random-feature predictor `x ↦ x ⬝ θ̂`
  reproduces every training target, `X θ̂ = y`;
* `trace_operator_transpose_mul_self_eq_sampleBottleneck`: `Tr (Mᵀ M) = Tr ((Z Zᵀ)⁻¹ (Z Sᵀ S Zᵀ)
  (Z Zᵀ)⁻¹)` by cyclic invariance of the trace;
* `sampleBottleneck_variance_eq_trace`: with isotropic noise of variance `σ²` the variance of `θ̂`
  (`LinearRegression.varianceOfLinearEstimator`) is `σ²` times that trace, from
  `linearEstimator_bias_variance_isotropic`;
* `tendsto_ratio_div_sub_sub_one`, `sampleBottleneck_asymptotic_variance_limit`: the finite-sample
  variance `σ² (m / (n₀ - m - 1) + m / (n - m - 1))` of the two inverse-Wishart terms tends to
  `σ² ((γ - 1)⁻¹ + (δ - 1)⁻¹)` along `n₀ / m → γ`, `n / m → δ`;
* `sampleBottleneck_asymptotic_bias_limit`: `(1 - m / n₀) (n / m) / (n / m - 1) ‖θ⋆‖² →
  (1 - γ⁻¹) δ / (δ - 1) ‖θ⋆‖²`.

The two limits are pure analysis on the ratio sequences. The identification of the finite-sample
variance and bias with these closed forms (inverse-Wishart mean, Haar-projector bias) is the
probabilistic input of Milestone 3b and is not proved here.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix MeasureTheory Filter Topology
open scoped Matrix

section Algebra

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq m]

/-- **The random-feature fit interpolates the training targets.** If the projected design
`Z = X S` has full row rank (`Z Zᵀ` invertible), then the predictor `θ̂ = S Zᵀ (Z Zᵀ)⁻¹ y` fits the
data exactly: `X θ̂ = y`. -/
theorem sampleBottleneck_interpolates_training_targets (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hZ : IsUnit ((X * S) * (X * S)ᵀ).det) (y : m → ℝ) :
    X *ᵥ (S *ᵥ (((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) *ᵥ y)) = y := by
  have h := rightInverse_interpolates (X * S) hZ y
  rwa [← Matrix.mulVec_mulVec _ X S] at h

/-- **Variance trace reduction in the sample-bottleneck regime.** For the measurement operator
`M = S (Zᵀ (Z Zᵀ)⁻¹)` of the minimum-norm interpolator, cyclic invariance of the trace gives
`Tr (Mᵀ M) = Tr ((Z Zᵀ)⁻¹ (Z Sᵀ S Zᵀ) (Z Zᵀ)⁻¹)`. -/
theorem trace_operator_transpose_mul_self_eq_sampleBottleneck (S : Matrix n₀ n ℝ)
    (Z : Matrix m n ℝ) :
    Matrix.trace ((S * (Zᵀ * (Z * Zᵀ)⁻¹))ᵀ * (S * (Zᵀ * (Z * Zᵀ)⁻¹))) =
      Matrix.trace ((Z * Zᵀ)⁻¹ * (Z * (Sᵀ * S) * Zᵀ) * (Z * Zᵀ)⁻¹) := by
  have hM : (S * (Zᵀ * (Z * Zᵀ)⁻¹))ᵀ = (Z * Zᵀ)⁻¹ * (Z * Sᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [hM]
  simp only [Matrix.mul_assoc]

end Algebra

section Variance

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq m] [DecidableEq n₀]

/-- **Variance of the sample-bottleneck estimator.** In the model `y = X θ⋆ + ε` with centered
isotropic noise `Cov ε = σ² I`, the random-feature estimator `θ̂ = S (Zᵀ (Z Zᵀ)⁻¹ y)`, `Z = X S`,
has `LinearRegression.varianceOfLinearEstimator` equal to
`σ² Tr ((Z Zᵀ)⁻¹ (Z Sᵀ S Zᵀ) (Z Zᵀ)⁻¹)`. -/
theorem sampleBottleneck_variance_eq_trace (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (θ : EuclideanSpace ℝ n₀) (σ_sq : ℝ) (P : Measure (m → ℝ)) [IsProbabilityMeasure P]
    (hε : ∀ i, MemLp (fun ε : m → ℝ => ε i) 2 P) (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (m → ℝ) → EuclideanSpace ℝ n₀)
    (hβ : ∀ ε, (β_hat ε).ofLp =
      (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) *ᵥ (X *ᵥ θ.ofLp + ε)) :
    LinearRegression.varianceOfLinearEstimator (1 : Matrix n₀ n₀ ℝ) P β_hat =
      σ_sq * Matrix.trace (((X * S) * (X * S)ᵀ)⁻¹ * ((X * S) * (Sᵀ * S) * (X * S)ᵀ) *
        ((X * S) * (X * S)ᵀ)⁻¹) := by
  rw [(linearEstimator_bias_variance_isotropic (S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) X θ 1
    σ_sq P hε h_mean h_cov β_hat hβ).2.1,
    ← trace_operator_transpose_mul_self_eq_sampleBottleneck S (X * S), Matrix.mul_one]
  congr 1
  exact Matrix.trace_mul_comm _ _

end Variance

section Asymptotics

/-- If `b k / m k → c` with `1 < c` and `m k → ∞`, then `b k → ∞` (eventually `b k > m k`). -/
theorem tendsto_atTop_of_tendsto_ratio_gt_one {c : ℝ} (hc : 1 < c) (b m : ℕ → ℕ)
    (h_ratio : Tendsto (fun k => (b k : ℝ) / (m k : ℝ)) atTop (𝓝 c))
    (h_m_top : Tendsto (fun k => (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => (b k : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ h_m_top
  filter_upwards [h_m_top.eventually_gt_atTop 0, h_ratio.eventually (lt_mem_nhds hc)] with k hk hr
  exact ((one_lt_div hk).mp hr).le

/-- **The sample-bottleneck inverse-Wishart term.** If `b / m → c > 1` and `m → ∞`, then
`m / (b - m - 1) → (c - 1)⁻¹`. This is `featureBottleneck_asymptotic_variance_limit` with the roles
of `n` and `m` exchanged (`m / b → c⁻¹`), the sample-bottleneck term being `n / (m - n - 1)` for
`n := m` samples against `m := b` columns. -/
theorem tendsto_ratio_div_sub_sub_one {c : ℝ} (hc : 1 < c) (b m : ℕ → ℕ)
    (h_ratio : Tendsto (fun k => (b k : ℝ) / (m k : ℝ)) atTop (𝓝 c))
    (h_m_top : Tendsto (fun k => (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => (m k : ℝ) / ((b k : ℝ) - m k - 1)) atTop (𝓝 (c - 1)⁻¹) := by
  have hc0 : c ≠ 0 := by positivity
  have h := featureBottleneck_asymptotic_variance_limit 1 c⁻¹ (by
    intro h
    have := (inv_eq_one.mp h)
    linarith) m b (by simpa [inv_div] using h_ratio.inv₀ hc0)
    (tendsto_atTop_of_tendsto_ratio_gt_one hc b m h_ratio h_m_top)
  have heq : 1 * (c⁻¹ / (1 - c⁻¹)) = (c - 1)⁻¹ := by
    have : c - 1 ≠ 0 := by linarith
    field_simp
  simpa [heq] using h

/-- **Asymptotic variance in the sample-bottleneck regime.** If `n₀ / m → γ > 1`, `n / m → δ > 1`
and `m → ∞`, then `σ² (m / (n₀ - m - 1) + m / (n - m - 1)) → σ² ((γ - 1)⁻¹ + (δ - 1)⁻¹)`: the
ambient and the feature inverse-Wishart terms add. -/
theorem sampleBottleneck_asymptotic_variance_limit (σ_sq γ δ : ℝ) (hγ : 1 < γ) (hδ : 1 < δ)
    (n₀ n m : ℕ → ℕ)
    (h_ratio_γ : Tendsto (fun k => (n₀ k : ℝ) / (m k : ℝ)) atTop (𝓝 γ))
    (h_ratio_δ : Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 δ))
    (h_m_top : Tendsto (fun k => (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => σ_sq * ((m k : ℝ) / ((n₀ k : ℝ) - m k - 1) +
      (m k : ℝ) / ((n k : ℝ) - m k - 1))) atTop (𝓝 (σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹))) :=
  ((tendsto_ratio_div_sub_sub_one hγ n₀ m h_ratio_γ h_m_top).add
    (tendsto_ratio_div_sub_sub_one hδ n m h_ratio_δ h_m_top)).const_mul σ_sq

/-- **Asymptotic bias in the sample-bottleneck regime.** If `n₀ / m → γ ≠ 0` and `n / m → δ ≠ 1`,
then `(1 - m / n₀) ((n / m) / (n / m - 1)) ‖θ⋆‖² → (1 - γ⁻¹) (δ / (δ - 1)) ‖θ⋆‖²`. -/
theorem sampleBottleneck_asymptotic_bias_limit (ρ_star γ δ : ℝ) (hγ : γ ≠ 0) (hδ : δ ≠ 1)
    (n₀ n m : ℕ → ℕ)
    (h_ratio_γ : Tendsto (fun k => (n₀ k : ℝ) / (m k : ℝ)) atTop (𝓝 γ))
    (h_ratio_δ : Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun k => (1 - (m k : ℝ) / (n₀ k : ℝ)) *
      (((n k : ℝ) / (m k : ℝ)) / ((n k : ℝ) / (m k : ℝ) - 1)) * ρ_star) atTop
      (𝓝 ((1 - γ⁻¹) * (δ / (δ - 1)) * ρ_star)) := by
  have hinv : Tendsto (fun k => (m k : ℝ) / (n₀ k : ℝ)) atTop (𝓝 γ⁻¹) := by
    simpa [inv_div] using h_ratio_γ.inv₀ hγ
  exact (((tendsto_const_nhds.sub hinv).mul
    (h_ratio_δ.div (h_ratio_δ.sub tendsto_const_nhds) (sub_ne_zero.mpr hδ))).mul_const ρ_star)

end Asymptotics

end LinearRegression.DoubleDescent

end
