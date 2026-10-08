/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.Basic
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomFeatures

/-!
# The feature-bottleneck regime

Random-feature regression with `m` samples, `n` random features and ambient dimension `n₀`, in the
regime where the features are the bottleneck (`n < m`, `δ = n / m < min {1, γ}`, `γ = n₀ / m`), so
that the projected design `Z = X S` has full column rank and the fit is the left inverse
`η̂ = (Zᵀ Z)⁻¹ Zᵀ y`, `θ̂ = S η̂ = M y` with `M = S (Zᵀ Z)⁻¹ Zᵀ`
([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]).

This file contains the exact finite-sample reduction and the deterministic limits:

* `trace_operator_transpose_mul_self_eq_featureBottleneck`: `Tr (Mᵀ M) = Tr ((Zᵀ Z)⁻¹ Sᵀ S)` by
  cyclic invariance of the trace;
* `featureBottleneck_variance_eq_trace`: with isotropic noise of variance `σ²`, the variance
  of `θ̂` (`LinearRegression.variance_of_linear_estimator`) is `σ² Tr ((Zᵀ Z)⁻¹ Sᵀ S)`, from
  `linearEstimator_bias_variance`;
* `trace_inverseWishartMean_mul_gram`: the algebraic cancellation `Tr ((m-n-1)⁻¹ G⁻¹ · G) =
  n / (m - n - 1)` that turns the inverse-Wishart mean `E[(Zᵀ Z)⁻¹] = (m-n-1)⁻¹ (Sᵀ S)⁻¹` into the
  variance `σ² n / (m - n - 1)`;
* `featureBottleneck_asymptotic_variance_limit`, `featureBottleneck_asymptotic_bias_limit`: the
  limits `σ² δ / (1 - δ)` and `(γ - δ) / (γ (1 - δ)) ‖θ⋆‖²` along `n / m → δ`, `n₀ / m → γ`.

The inverse-Wishart mean itself (the probabilistic input) is not proved here.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix MeasureTheory Filter Topology
open scoped Matrix

section Algebra

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq n]

/-- **Variance trace reduction in the feature-bottleneck regime.** For the measurement operator
`M = S (Zᵀ Z)⁻¹ Zᵀ` of the left-inverse fit, cyclic invariance of the trace gives
`Tr (Mᵀ M) = Tr ((Zᵀ Z)⁻¹ Sᵀ S)`. -/
theorem trace_operator_transpose_mul_self_eq_featureBottleneck (S : Matrix n₀ n ℝ)
    (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) :
    Matrix.trace ((S * ((Zᵀ * Z)⁻¹ * Zᵀ))ᵀ * (S * ((Zᵀ * Z)⁻¹ * Zᵀ))) =
      Matrix.trace ((Zᵀ * Z)⁻¹ * (Sᵀ * S)) := by
  have hM : (S * ((Zᵀ * Z)⁻¹ * Zᵀ))ᵀ = Z * ((Zᵀ * Z)⁻¹ * Sᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have hBA : S * ((Zᵀ * Z)⁻¹ * Zᵀ) * (Z * ((Zᵀ * Z)⁻¹ * Sᵀ)) = S * ((Zᵀ * Z)⁻¹ * Sᵀ) := by
    calc S * ((Zᵀ * Z)⁻¹ * Zᵀ) * (Z * ((Zᵀ * Z)⁻¹ * Sᵀ))
        = S * (((Zᵀ * Z)⁻¹ * Zᵀ) * Z) * ((Zᵀ * Z)⁻¹ * Sᵀ) := by simp only [Matrix.mul_assoc]
      _ = S * ((Zᵀ * Z)⁻¹ * Sᵀ) := by rw [leftInverse_mul_self Z hZ, Matrix.mul_one]
  rw [hM, Matrix.trace_mul_comm, hBA, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- **Trace cancellation against an inverse Gram matrix.** If `G` is invertible, then
`Tr ((c • G⁻¹) G) = c · card n`, whatever the scalar `c`. -/
theorem trace_smul_inv_mul_self (c : ℝ) (G : Matrix n n ℝ) (hG : IsUnit G.det) :
    Matrix.trace ((c • G⁻¹) * G) = c * (Fintype.card n : ℝ) := by
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hG, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul]

/-- **Algebraic core of the Wishart cancellation.** With `c = (m - n - 1)⁻¹`, the mean
`(m-n-1)⁻¹ (Sᵀ S)⁻¹` of `(Zᵀ Z)⁻¹` against `G = Sᵀ S` gives `Tr (· G) = n / (m - n - 1)`
(`trace_smul_inv_mul_self`). -/
theorem trace_inverseWishartMean_mul_gram (m : ℕ) (G : Matrix n n ℝ) (hG : IsUnit G.det) :
    Matrix.trace ((((m : ℝ) - Fintype.card n - 1)⁻¹ • G⁻¹) * G) =
      (Fintype.card n : ℝ) / ((m : ℝ) - Fintype.card n - 1) := by
  rw [trace_smul_inv_mul_self _ G hG, div_eq_inv_mul]

end Algebra

section Variance

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq m] [DecidableEq n]
  [DecidableEq n₀]

/-- **Variance of the feature-bottleneck estimator.** In the model `y = X θ⋆ + ε` with centered
isotropic noise `Cov ε = σ² I`, the random-feature estimator `θ̂ = S (Zᵀ Z)⁻¹ Zᵀ y`, `Z = X S`,
has `LinearRegression.variance_of_linear_estimator` equal to `σ² Tr ((Zᵀ Z)⁻¹ Sᵀ S)`. -/
theorem featureBottleneck_variance_eq_trace (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hZ : IsUnit ((X * S)ᵀ * (X * S)).det) (θ : EuclideanSpace ℝ n₀) (σ_sq : ℝ)
    (P : Measure (m → ℝ)) [IsProbabilityMeasure P] (hε : ∀ i, MemLp (fun ε : m → ℝ => ε i) 2 P)
    (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (m → ℝ) → EuclideanSpace ℝ n₀)
    (hβ : ∀ ε, (β_hat ε).ofLp =
      (S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ)) *ᵥ (X *ᵥ θ.ofLp + ε)) :
    LinearRegression.variance_of_linear_estimator (1 : Matrix n₀ n₀ ℝ) P β_hat =
      σ_sq * Matrix.trace (((X * S)ᵀ * (X * S))⁻¹ * (Sᵀ * S)) := by
  rw [(linearEstimator_bias_variance_isotropic (S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ)) X θ 1
    σ_sq P hε h_mean h_cov β_hat hβ).2.1,
    ← trace_operator_transpose_mul_self_eq_featureBottleneck S (X * S) hZ, Matrix.mul_one]
  congr 1
  exact Matrix.trace_mul_comm _ _

end Variance

section Asymptotics

/-- **Asymptotic variance in the feature-bottleneck regime.** If `n / m → δ ≠ 1` and `m → ∞`, then
`σ² n / (m - n - 1) → σ² δ / (1 - δ)`, since `n / (m - n - 1) = (n / m) / (1 - n / m - 1 / m)`.
(Only `δ ≠ 1` is needed; the regime of interest is `0 < δ < 1`.) -/
theorem featureBottleneck_asymptotic_variance_limit (σ_sq δ : ℝ) (hδ : δ ≠ 1) (n m : ℕ → ℕ)
    (h_ratio : Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 δ))
    (h_m_top : Tendsto (fun k => (m k : ℝ)) atTop atTop) :
    Tendsto (fun k => σ_sq * ((n k : ℝ) / ((m k : ℝ) - n k - 1))) atTop
      (𝓝 (σ_sq * (δ / (1 - δ)))) := by
  have hinv : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h_m_top
  have hden : Tendsto (fun k => 1 - (n k : ℝ) / (m k : ℝ) - 1 / (m k : ℝ)) atTop
      (𝓝 (1 - δ - 0)) := (tendsto_const_nhds.sub h_ratio).sub hinv
  have hq := h_ratio.div hden (by rwa [sub_zero, sub_ne_zero, Ne, eq_comm])
  have heq : ∀ᶠ k in atTop, (n k : ℝ) / (m k : ℝ) /
      (1 - (n k : ℝ) / (m k : ℝ) - 1 / (m k : ℝ)) = (n k : ℝ) / ((m k : ℝ) - n k - 1) := by
    filter_upwards [h_m_top.eventually_gt_atTop 0] with k hk
    rw [← div_div_div_cancel_right₀ hk.ne' (n k : ℝ) ((m k : ℝ) - n k - 1)]
    congr 1
    field_simp
  rw [sub_zero] at hq
  exact (hq.congr' heq).const_mul σ_sq

/-- **Asymptotic bias in the feature-bottleneck regime.** If `n₀ / m → γ ≠ 0` and `n / m → δ ≠ 1`,
then `(n₀/m - n/m) / ((n₀/m)(1 - n/m)) ‖θ⋆‖² → (γ - δ) / (γ (1 - δ)) ‖θ⋆‖²`. -/
theorem featureBottleneck_asymptotic_bias_limit (ρ_star γ δ : ℝ) (hγ : γ ≠ 0) (hδ : δ ≠ 1)
    (n₀ n m : ℕ → ℕ)
    (h_ratio_γ : Tendsto (fun k => (n₀ k : ℝ) / (m k : ℝ)) atTop (𝓝 γ))
    (h_ratio_δ : Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun k => ((n₀ k : ℝ) / (m k : ℝ) - (n k : ℝ) / (m k : ℝ)) /
      ((n₀ k : ℝ) / (m k : ℝ) * (1 - (n k : ℝ) / (m k : ℝ))) * ρ_star) atTop
      (𝓝 (((γ - δ) / (γ * (1 - δ))) * ρ_star)) :=
  ((h_ratio_γ.sub h_ratio_δ).div (h_ratio_γ.mul (tendsto_const_nhds.sub h_ratio_δ))
    (mul_ne_zero hγ (sub_ne_zero.mpr (Ne.symm hδ)))).mul_const ρ_star

end Asymptotics

end LinearRegression.DoubleDescent

end
