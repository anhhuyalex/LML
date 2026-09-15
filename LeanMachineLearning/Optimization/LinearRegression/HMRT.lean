/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import LeanMachineLearning.Optimization.ConvexOpt.Basic

/-!
# Linear Models, Prediction Risk, and Ridgeless Least Squares

This file formalizes the linear model setup, prediction risk, bias-variance
decomposition, and the ridgeless least squares estimator following Section 2 of
Hastie, Montanari, Rosset, and Tibshirani (HMRT, 2022).
-/

@[expose] public section

namespace LinearRegression

open MeasureTheory ProbabilityTheory
open scoped Matrix ProbabilityTheory

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq p]

/-- Distributional assumptions on features $P_x$ and noise $P_\epsilon$:
$\mathbb{E}[x_i] = 0$, $\operatorname{Cov}(x_i) = \Sigma$,
$\mathbb{E}[\epsilon_i] = 0$, and $\operatorname{Var}(\epsilon_i) = \sigma^2$. -/
structure ModelDistribution (Px : Measure (EuclideanSpace ℝ p)) (Pε : Measure ℝ)
    (Sigma : Matrix p p ℝ) (σ_sq : ℝ) : Prop where
  prob_Px : IsProbabilityMeasure Px
  prob_Pε : IsProbabilityMeasure Pε
  mean_Px : ∀ j : p, ∫ x, x j ∂Px = (0 : ℝ)
  cov_Px : ∀ j k : p, cov[fun x => x j, fun x => x k; Px] = Sigma j k
  mean_Pε : ∫ ε, ε ∂Pε = (0 : ℝ)
  var_Pε : Var[id; Pε] = σ_sq

/-- Out-of-sample prediction risk conditional on $X$:
$$ R_X(\hat{\beta}; \beta) = \mathbb{E}[\|\hat{\beta} - \beta\|_\Sigma^2 \mid X] $$ -/
noncomputable def risk {Ω : Type*} [MeasurableSpace Ω] (Sigma : Matrix p p ℝ) (μ : Measure Ω)
    (β_hat : Ω → EuclideanSpace ℝ p) (β : EuclideanSpace ℝ p) : ℝ :=
  ∫ ω, (β_hat ω - β : p → ℝ) ⬝ᵥ (Sigma *ᵥ (β_hat ω - β)) ∂μ

/-- Bias term conditional on $X$:
$$ B_X(\hat{\beta}; \beta) = \|\mathbb{E}(\hat{\beta} \mid X) - \beta\|_\Sigma^2 $$ -/
noncomputable def bias {Ω : Type*} [MeasurableSpace Ω] (Sigma : Matrix p p ℝ) (μ : Measure Ω)
    (β_hat : Ω → EuclideanSpace ℝ p) (β : EuclideanSpace ℝ p) : ℝ :=
  ((∫ ω, β_hat ω ∂μ) - β : p → ℝ) ⬝ᵥ (Sigma *ᵥ ((∫ ω, β_hat ω ∂μ) - β))

/-- Covariance matrix of $\hat{\beta}$ conditional on $X$:
`[Cov(β_hat | X)]_{j, k} = Cov(β_hat_j, β_hat_k | X)`. -/
noncomputable def covCondX {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β_hat : Ω → EuclideanSpace ℝ p) : Matrix p p ℝ :=
  fun j k => cov[fun ω => β_hat ω j, fun ω => β_hat ω k; μ]

/-- Variance term conditional on $X$:
$$ V_X(\hat{\beta}; \beta) = \operatorname{Tr}[\operatorname{Cov}(\hat{\beta} \mid X) \Sigma] $$ -/
noncomputable def variance {Ω : Type*} [MeasurableSpace Ω] (Sigma : Matrix p p ℝ) (μ : Measure Ω)
    (β_hat : Ω → EuclideanSpace ℝ p) : ℝ :=
  Matrix.trace (covCondX μ β_hat * Sigma)

/-- Least squares loss $\|y - X b\|_2^2$. -/
noncomputable def leastSquaresLoss (X : Matrix n p ℝ) (y : EuclideanSpace ℝ n)
    (b : EuclideanSpace ℝ p) : ℝ :=
  ‖y - (WithLp.equiv 2 (n → ℝ)).symm (X *ᵥ b)‖ ^ 2

/-- Ridgeless least squares (min-norm least squares) regression estimator:
$$ \hat{\beta} = \arg\min \{\|b\|_2 : b \text{ minimizes } \|y - X b\|_2^2\} $$ -/
def IsMinNormLeastSquares (X : Matrix n p ℝ) (y : EuclideanSpace ℝ n)
    (b : EuclideanSpace ℝ p) : Prop :=
  IsMinOn (fun b' => ‖b'‖) {b' | IsMinOn (leastSquaresLoss X y) Set.univ b'} b

/-! ### 6. Lemma 1: Bias and Variance of Ridgeless Least Squares -/

/-- The uncentered sample covariance of $X$: $\hat{\Sigma} = X^T X / n$. -/
noncomputable def sampleCov (X : Matrix n p ℝ) : Matrix p p ℝ :=
  (1 / (Fintype.card n : ℝ)) • (Xᵀ * X)

/-- Lemma 1 (Bias). Under the linear model,
if $\mathbb{E}[\hat{\beta} \mid X] = \hat{\Sigma}^+ \hat{\Sigma} \beta$
and $\Pi = I - \hat{\Sigma}^+ \hat{\Sigma}$ is symmetric, then
$$ B_X(\hat{\beta}; \beta) = \beta^T \Pi \Sigma \Pi \beta $$ -/
theorem lemma1_bias
    (Sigma : Matrix p p ℝ) (Sigma_hat Sigma_hat_dagger : Matrix p p ℝ)
    (h_symm : (1 - Sigma_hat_dagger * Sigma_hat).IsSymm)
    (m β : EuclideanSpace ℝ p)
    (hm : (m : p → ℝ) = (Sigma_hat_dagger * Sigma_hat) *ᵥ β) :
    (m - β : p → ℝ) ⬝ᵥ (Sigma *ᵥ (m - β)) =
      (β : p → ℝ) ⬝ᵥ (((1 - Sigma_hat_dagger * Sigma_hat) * Sigma *
        (1 - Sigma_hat_dagger * Sigma_hat)) *ᵥ β) := by
  set Pi := 1 - Sigma_hat_dagger * Sigma_hat
  have h_diff : (m : p → ℝ) - β = - (Pi *ᵥ β) := by
    ext i
    have hm_i : (m : p → ℝ) i = ((Sigma_hat_dagger * Sigma_hat) *ᵥ β) i := congr_fun hm i
    dsimp [Pi]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change (m : p → ℝ) i - (β : p → ℝ) i =
      - ((β : p → ℝ) i - ((Sigma_hat_dagger * Sigma_hat) *ᵥ β) i)
    rw [hm_i]
    ring
  rw [h_diff, Matrix.mulVec_neg]
  rw [neg_dotProduct, dotProduct_neg, neg_neg]
  rw [dotProduct_comm (Pi *ᵥ β) (Sigma *ᵥ (Pi *ᵥ β))]
  rw [← Matrix.dotProduct_transpose_mulVec Pi β (Sigma *ᵥ (Pi *ᵥ β))]
  rw [h_symm.eq]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

omit [DecidableEq p] in
/-- Lemma 1 (Variance). Under the linear model,
if $\operatorname{Cov}(\hat{\beta} \mid X) = \frac{\sigma^2}{n} \hat{\Sigma}^+$, then
$$ V_X(\hat{\beta}; \beta) = \frac{\sigma^2}{n} \operatorname{Tr}(\hat{\Sigma}^+ \Sigma) $$ -/
theorem lemma1_variance
    (Sigma : Matrix p p ℝ) (Sigma_hat_dagger : Matrix p p ℝ)
    (σ_sq : ℝ) (cov_mat : Matrix p p ℝ)
    (h_cov : cov_mat = (σ_sq / (Fintype.card n : ℝ)) • Sigma_hat_dagger) :
    Matrix.trace (cov_mat * Sigma) =
      (σ_sq / (Fintype.card n : ℝ)) * Matrix.trace (Sigma_hat_dagger * Sigma) := by
  rw [h_cov, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Lemma 1 (Hastie et al., 2022).
Under the linear model $y = X \beta + \epsilon$, the min-norm least squares estimator $\hat{\beta}$
has conditional bias and variance:
$$ B_X(\hat{\beta}; \beta) = \beta^T \Pi \Sigma \Pi \beta \quad \text{and} \quad
   V_X(\hat{\beta}; \beta) = \frac{\sigma^2}{n} \operatorname{Tr}(\hat{\Sigma}^+ \Sigma) $$
where $\hat{\Sigma} = X^T X / n$ and $\Pi = I - \hat{\Sigma}^+ \hat{\Sigma}$. -/
theorem lemma1
    (Sigma : Matrix p p ℝ) (Sigma_hat Sigma_hat_dagger : Matrix p p ℝ)
    (h_symm : (1 - Sigma_hat_dagger * Sigma_hat).IsSymm)
    (σ_sq : ℝ) (m β : EuclideanSpace ℝ p)
    (hm : (m : p → ℝ) = (Sigma_hat_dagger * Sigma_hat) *ᵥ β)
    (cov_mat : Matrix p p ℝ)
    (h_cov : cov_mat = (σ_sq / (Fintype.card n : ℝ)) • Sigma_hat_dagger) :
    (m - β : p → ℝ) ⬝ᵥ (Sigma *ᵥ (m - β)) =
      (β : p → ℝ) ⬝ᵥ (((1 - Sigma_hat_dagger * Sigma_hat) * Sigma *
        (1 - Sigma_hat_dagger * Sigma_hat)) *ᵥ β) ∧
    Matrix.trace (cov_mat * Sigma) =
      (σ_sq / (Fintype.card n : ℝ)) * Matrix.trace (Sigma_hat_dagger * Sigma) :=
  ⟨lemma1_bias Sigma Sigma_hat Sigma_hat_dagger h_symm m β hm,
   lemma1_variance Sigma Sigma_hat_dagger σ_sq cov_mat h_cov⟩

end LinearRegression

end
