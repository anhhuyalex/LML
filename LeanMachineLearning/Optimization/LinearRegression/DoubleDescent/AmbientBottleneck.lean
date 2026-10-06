/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.Basic
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomFeatures

/-!
# The ambient-bottleneck regime

Random-feature regression with `m` samples, `n` random features and ambient dimension `n₀ ≤ n`
(`γ = n₀ / m ≤ δ = n / m`, `γ < 1`): the random projection `S ∈ ℝ^{n₀ × n}` has full row rank, so
`Z = X S` has the same column space as `X` and the random-feature fit is classical OLS
([Bach, 2024]; [Hastie et al., 2022]).

For `n > n₀` the Gram matrix `Zᵀ Z` is singular, so the left-inverse formula of
`RandomFeatures.lean` is unavailable; the fitted coefficients are the *minimum-norm* least-squares
solution `ηh = Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y` (no pseudoinverse is defined: it is the composite of the
right inverse of `S` and the left inverse of `X`).

* `range_mulVecLin_mul_eq`: `range (X S) = range X` when `S Sᵀ` is invertible;
* `ambientBottleneck_isMinOn`, `ambientBottleneck_norm_sq_decomp`,
  `eq_ambientBottleneck_of_norm_le`: `ηh` minimizes `‖Z η - y‖`, and is the unique such minimizer of
  minimum norm; the projected estimator `θ̂ = S ηh` is the OLS fit `(Xᵀ X)⁻¹ Xᵀ y`
  (`rightInverse_interpolates`);
* `ambientBottleneck_bias_variance`: the estimator is unbiased and its variance (`LinearRegression
  .variance`) is `σ² Tr ((Xᵀ X)⁻¹ Σ)`.

The limit `σ² n₀ / (m - n₀ - 1) → σ² γ / (1 - γ)` is
`featureBottleneck_asymptotic_variance_limit` with `n := n₀`: the ambient-bottleneck variance does
not depend on `δ`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix MeasureTheory NTK
open scoped Matrix RealInnerProductSpace

section Saturation

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq n₀]

omit [Fintype m] in
/-- **Subspace saturation.** If `S Sᵀ` is invertible (`S` has full row rank, `n₀ ≤ n`), then the
projected design `X S` has the same column space as `X`. -/
theorem range_mulVecLin_mul_eq (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hS : IsUnit (S * Sᵀ).det) :
    LinearMap.range (X * S).mulVecLin = LinearMap.range X.mulVecLin := by
  ext v
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨S *ᵥ w, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(Sᵀ * (S * Sᵀ)⁻¹) *ᵥ u, by
      rw [← Matrix.mulVec_mulVec, rightInverse_interpolates S hS]⟩

end Saturation

section MinNorm

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq n₀]
  (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ) (hX : IsUnit (Xᵀ * X).det) (hS : IsUnit (S * Sᵀ).det)
  (y : EuclideanSpace ℝ m)

include hS

omit hX in
/-- **The projected design fits like OLS.** For the minimum-norm coefficients
`ηh = Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y`, the fitted values are the OLS fit `Z ηh = X (Xᵀ X)⁻¹ Xᵀ y`. -/
theorem mulVec_ambientBottleneck :
    (X * S) *ᵥ ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp)) =
      X *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp) := by
  rw [← Matrix.mulVec_mulVec, rightInverse_interpolates S hS]

include hX

/-- **Ambient-bottleneck estimator is a global minimizer.** The minimum-norm coefficients
`ηh = Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y` minimize the residual norm `‖Z η - y‖`, `Z = X S`, equivalently
`NTK.mseLoss` of the linear model (`mseLoss_linear`). -/
theorem ambientBottleneck_isMinOn :
    IsMinOn (fun η : EuclideanSpace ℝ n => ‖WithLp.toLp 2 ((X * S) *ᵥ η.ofLp) - y‖) Set.univ
      (WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp))) := by
  refine isMinOn_iff.mpr fun η _ => ?_
  change ‖_ - y‖ ≤ ‖WithLp.toLp 2 ((X * S) *ᵥ η.ofLp) - y‖
  rw [mulVec_ambientBottleneck X S hS y, ← Matrix.mulVec_mulVec η.ofLp X S]
  exact isMinOn_iff.mp (leftInverse_isMinOn X hX y) (WithLp.toLp 2 (S *ᵥ η.ofLp)) trivial

/-- **Pythagoras for the minimum-norm fit.** Every minimizer `η` of the residual norm
(`‖Z η - y‖ ≤ ‖Z ηh - y‖`) satisfies `‖η‖² = ‖ηh‖² + ‖η - ηh‖²` for the minimum-norm coefficients
`ηh = Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y`: its projection `S η` is forced to be the OLS fit
(`eq_leftInverse_of_norm_residual_le`), so `η - ηh ∈ ker S`, which is orthogonal to `range Sᵀ`. -/
theorem ambientBottleneck_norm_sq_decomp {η : EuclideanSpace ℝ n}
    (h : ‖WithLp.toLp 2 ((X * S) *ᵥ η.ofLp) - y‖ ≤
      ‖WithLp.toLp 2 ((X * S) *ᵥ ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp))) - y‖) :
    ‖η‖ ^ 2 =
      ‖(WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp)) :
        EuclideanSpace ℝ n)‖ ^ 2 +
      ‖η - WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp))‖ ^ 2 := by
  set w : n₀ → ℝ := ((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp with hw
  set ηh : EuclideanSpace ℝ n := WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ w) with hηh
  have hSη : S *ᵥ η.ofLp = w := by
    have h' := h
    rw [mulVec_ambientBottleneck X S hS y, ← Matrix.mulVec_mulVec η.ofLp X S] at h'
    have := eq_leftInverse_of_norm_residual_le X hX y (WithLp.toLp 2 (S *ᵥ η.ofLp)) h'
    simpa using congrArg WithLp.ofLp this
  have hd : S *ᵥ (η - ηh).ofLp = 0 := by
    simp [hηh, Matrix.mulVec_sub, hSη, rightInverse_interpolates S hS]
  have horth : ⟪ηh, η - ηh⟫ = 0 := by
    rw [real_inner_eq_dotProduct, hηh, WithLp.ofLp_toLp, dotProduct_comm, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_zero, zero_dotProduct]
  have hsplit : η = ηh + (η - ηh) := by abel
  conv_lhs => rw [hsplit]
  rw [norm_add_sq_real, horth]
  ring

/-- **Ambient-bottleneck estimator is the unique minimum-norm minimizer.** A minimizer `η` of
`‖Z η - y‖` with `‖η‖ ≤ ‖ηh‖` equals `ηh = Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y`. -/
theorem eq_ambientBottleneck_of_norm_le {η : EuclideanSpace ℝ n}
    (h : ‖WithLp.toLp 2 ((X * S) *ᵥ η.ofLp) - y‖ ≤
      ‖WithLp.toLp 2 ((X * S) *ᵥ ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp))) - y‖)
    (hle : ‖η‖ ≤
      ‖(WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp)) :
        EuclideanSpace ℝ n)‖) :
    η = WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp)) := by
  have h2 := ambientBottleneck_norm_sq_decomp X S hX hS y h
  have h3 : ‖η - WithLp.toLp 2 ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y.ofLp))‖ ^ 2 ≤ 0 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hle 2]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h3 (sq_nonneg _))))

end MinNorm

section BiasVariance

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq m] [DecidableEq n₀]

/-- **Bias and variance of the ambient-bottleneck estimator.** In the model `y = X θ⋆ + ε` with
centered noise `Cov ε = σ² I`, if `Xᵀ X` and `S Sᵀ` are invertible then the random-feature
estimator `θ̂ = S (Sᵀ (S Sᵀ)⁻¹ (Xᵀ X)⁻¹ Xᵀ y)` is classical OLS: it is exactly unbiased and, for
any weighting `Σ`, has variance `σ² Tr ((Xᵀ X)⁻¹ Σ)` and risk equal to this variance. -/
theorem ambientBottleneck_bias_variance (X : Matrix m n₀ ℝ) (S : Matrix n₀ n ℝ)
    (hX : IsUnit (Xᵀ * X).det) (hS : IsUnit (S * Sᵀ).det) (θ : EuclideanSpace ℝ n₀)
    (Sigma : Matrix n₀ n₀ ℝ) (σ_sq : ℝ) (P : Measure (m → ℝ)) [IsProbabilityMeasure P]
    (hε : ∀ i, MemLp (fun ε : m → ℝ => ε i) 2 P) (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (m → ℝ) → EuclideanSpace ℝ n₀)
    (hβ : ∀ ε, (β_hat ε).ofLp =
      S *ᵥ ((Sᵀ * (S * Sᵀ)⁻¹) *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ (X *ᵥ θ.ofLp + ε)))) :
    LinearRegression.bias Sigma P β_hat θ = 0 ∧
      LinearRegression.variance Sigma P β_hat = σ_sq * Matrix.trace ((Xᵀ * X)⁻¹ * Sigma) ∧
      LinearRegression.risk Sigma P β_hat θ = σ_sq * Matrix.trace ((Xᵀ * X)⁻¹ * Sigma) := by
  have hOLS := leftInverse_mul_self X hX
  obtain ⟨hb, hv, hr⟩ := linearEstimator_bias_variance ((Xᵀ * X)⁻¹ * Xᵀ) X θ Sigma
    (σ_sq • (1 : Matrix m m ℝ)) P hε h_mean (fun i j => by
      simpa [Matrix.one_apply] using h_cov i j) β_hat (fun ε => by
        rw [hβ, rightInverse_interpolates S hS])
  have hvar : Matrix.trace (((Xᵀ * X)⁻¹ * Xᵀ) * (σ_sq • (1 : Matrix m m ℝ)) *
      ((Xᵀ * X)⁻¹ * Xᵀ)ᵀ * Sigma) = σ_sq * Matrix.trace ((Xᵀ * X)⁻¹ * Sigma) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul,
      leftInverse_mul_transpose X hX, Matrix.trace_smul, smul_eq_mul]
  rw [hOLS, sub_self, Matrix.zero_mulVec, Matrix.mulVec_zero, dotProduct_zero] at hb hr
  rw [hvar] at hv hr
  exact ⟨hb, hv, by simpa using hr⟩

end BiasVariance

end LinearRegression.DoubleDescent

end
