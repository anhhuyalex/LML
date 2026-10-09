/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.MulTranspose
public import LeanMachineLearning.Optimization.LinearRegression.HMRT

/-!
# Non-asymptotic foundations for double descent

Exact, finite-sample facts about linear estimators `θ̂ = M y` in the model `y = X θ⋆ + ε`, used by
the double-descent analysis of random-feature regression (Bach 2024; Hastie–Montanari–Rosset–
Tibshirani 2022; Belkin–Hsu–Ma–Mandal 2019). Everything is stated in terms of the existing
`LinearRegression.risk`, `LinearRegression.biasOfLinearEstimator` and
`LinearRegression.varianceOfLinearEstimator`, and no new
definitions are introduced: the measurement operator is just the matrix `M` (for random features
`M = S Z†`).

* `integral_dotProduct_mulVec_self`, `integral_dotProduct_mul_dotProduct`: second-moment
  identities `E[xᵀ S x] = Tr (S Γ)` and `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`, where `Γ` is the
  second-moment matrix of a square-integrable random vector `x`;
* `excess_prediction_risk_eq_mahalanobis`, `excess_prediction_risk_eq_param_risk_isotropic`:
  `E_{x_new}[(x_new ⬝ (θ̂ - θ⋆))²]` is the `Σ`-norm (resp. squared Euclidean norm) of `θ̂ - θ⋆`;
* `risk_eq_bias_add_variance`: `R = B + V` for any estimator with square-integrable coordinates;
* `linearEstimator_bias_variance`: for centered noise of covariance `Γ`, the error splits as
  `θ̂ - θ⋆ = (M X - I) θ⋆ + M ε` (a fixed part and a centered part), so
  `B = ‖(M X - I) θ⋆‖²_Σ` and `V = Tr (M Γ Mᵀ Σ)`;
* `linearEstimator_bias_variance_isotropic`: the isotropic case `Γ = σ² I`, where for `Σ = I` the
  risk is `E ‖θ̂ - θ⋆‖² = ‖(M X - I) θ⋆‖² + σ² Tr (Mᵀ M)`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory
open scoped Matrix

variable {Ω p n : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype p] [Fintype n]

/-- Quadratic forms of a square-integrable random vector integrate against its second-moment
matrix. -/
theorem integral_dotProduct_mulVec_self (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (S : Matrix p p ℝ) :
    ∫ ω, x ω ⬝ᵥ (S *ᵥ x ω) ∂μ = Matrix.trace (S * Γ) := by
  have hexp : ∀ ω, x ω ⬝ᵥ (S *ᵥ x ω) = ∑ j, ∑ k, S j k * (x ω j * x ω k) := fun ω => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ j k, Integrable (fun ω => S j k * (x ω j * x ω k)) μ := fun j k =>
    ((hx j).integrable_mul (hx k)).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k, integral_const_mul, hΓ]
  have hsymm : ∀ j k, Γ k j = Γ j k := fun j k => by
    rw [← hΓ, ← hΓ]; exact integral_congr_ae (.of_forall fun ω => mul_comm _ _)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hsymm]


/-- Bilinear second-moment identity: `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`. -/
theorem integral_dotProduct_mul_dotProduct (x : Ω → p → ℝ) (hx : ∀ j, MemLp (fun ω => x ω j) 2 μ)
    (Γ : Matrix p p ℝ) (hΓ : ∀ j k, ∫ ω, x ω j * x ω k ∂μ = Γ j k) (a b : p → ℝ) :
    ∫ ω, (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) ∂μ = a ⬝ᵥ (Γ *ᵥ b) := by
  have h := integral_dotProduct_mulVec_self x hx Γ hΓ (Matrix.vecMulVec b a)
  have hpt : ∀ ω, x ω ⬝ᵥ (Matrix.vecMulVec b a *ᵥ x ω) = (x ω ⬝ᵥ a) * (x ω ⬝ᵥ b) := fun ω => by
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct_comm]
  simp_rw [hpt] at h
  rw [h, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- **Excess prediction risk is the `Σ`-norm of the parameter error**: for a square-integrable
feature law `P` with second-moment matrix `Σ`, `E[(x ⬝ v)²] = v ⬝ Σ v`. -/
theorem excess_prediction_risk_eq_mahalanobis (P : Measure (p → ℝ))
    (hP : ∀ j, MemLp (fun x : p → ℝ => x j) 2 P) (Sigma : Matrix p p ℝ)
    (h_cov : ∀ j k, ∫ x, x j * x k ∂P = Sigma j k) (v : p → ℝ) :
    ∫ x, (x ⬝ᵥ v) ^ 2 ∂P = v ⬝ᵥ (Sigma *ᵥ v) := by
  simpa [sq] using integral_dotProduct_mul_dotProduct (μ := P) id hP Sigma h_cov v v

/-- Isotropic case `Σ = I`: excess prediction risk equals the squared parameter error. -/
theorem excess_prediction_risk_eq_param_risk_isotropic [DecidableEq p] (P : Measure (p → ℝ))
    (hP : ∀ j, MemLp (fun x : p → ℝ => x j) 2 P)
    (h_cov : ∀ j k, ∫ x, x j * x k ∂P = if j = k then 1 else 0) (v : p → ℝ) :
    ∫ x, (x ⬝ᵥ v) ^ 2 ∂P = v ⬝ᵥ v := by
  simpa using excess_prediction_risk_eq_mahalanobis P hP 1 (fun j k => by
    simpa [Matrix.one_apply] using h_cov j k) v

/-- Second moment of a shifted pair of square-integrable variables. -/
theorem integral_sub_mul_sub [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (a b : ℝ) :
    ∫ ω, (f ω - a) * (g ω - b) ∂μ = cov[f, g; μ] + (μ[f] - a) * (μ[g] - b) := by
  have h1 : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  have h2 : Integrable (fun ω => b * f ω) μ := (hf.integrable (by simp)).const_mul _
  have h3 : Integrable (fun ω => a * g ω) μ := (hg.integrable (by simp)).const_mul _
  have : (fun ω => (f ω - a) * (g ω - b)) = fun ω => (f ω * g ω - b * f ω) - (a * g ω - a * b) :=
    funext fun ω => by ring
  have h4 : Integrable (fun ω => f ω * g ω - b * f ω) μ := h1.sub h2
  have h5 : Integrable (fun ω => a * g ω - a * b) μ := h3.sub (integrable_const _)
  rw [this, integral_sub h4 h5, integral_sub h1 h2, integral_sub h3 (integrable_const _),
    integral_const_mul, integral_const_mul, covariance_eq_sub hf hg]
  simp
  ring


/-- **Bias–variance decomposition of the prediction risk** for any estimator whose coordinates are
square-integrable: `R = B + V`. -/
theorem risk_eq_bias_add_variance [IsProbabilityMeasure μ] (Sigma : Matrix p p ℝ)
    (β_hat : Ω → EuclideanSpace ℝ p) (β : EuclideanSpace ℝ p)
    (h : ∀ j, MemLp (fun ω => β_hat ω j) 2 μ) :
    risk Sigma μ β_hat β =
      biasOfLinearEstimator Sigma μ β_hat β + varianceOfLinearEstimator Sigma μ β_hat := by
  set d : p → ℝ := fun j => μ[fun ω => β_hat ω j] - β j with hd
  have hx : ∀ j, MemLp (fun ω => (β_hat ω - β).ofLp j) 2 μ := fun j => by
    exact (h j).sub (memLp_const (β j))
  have hΓ := fun j k => integral_sub_mul_sub (h j) (h k) (β j) (β k)
  have hrisk := integral_dotProduct_mulVec_self (μ := μ) (fun ω => (β_hat ω - β).ofLp) hx
    (covCondXOfLinearEstimator μ β_hat + Matrix.vecMulVec d d) (fun j k => by
      simpa [covCondXOfLinearEstimator, Matrix.vecMulVec_apply, hd] using hΓ j k) Sigma
  have hbias : ((∫ ω, β_hat ω ∂μ) - β : p → ℝ) = d := funext fun j => by
    simp [hd, eval_integral_piLp (fun j => (h j).integrable (by simp))]
  unfold risk biasOfLinearEstimator varianceOfLinearEstimator
  rw [hbias]
  refine hrisk.trans ?_
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_comm, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm, add_comm]


/-- **Exact conditional bias–variance decomposition for a linear estimator** `θ̂ = M (X θ⋆ + ε)`
with centered noise of covariance `Γ`: the bias is `‖(M X - I) θ⋆‖²_Σ` and the variance is
`Tr (M Γ Mᵀ Σ)`; in particular `R = B + V`. -/
theorem linearEstimator_bias_variance [DecidableEq p] (M : Matrix p n ℝ) (X : Matrix n p ℝ)
    (θ : EuclideanSpace ℝ p) (Sigma : Matrix p p ℝ) (Γ : Matrix n n ℝ)
    (P : Measure (n → ℝ)) [IsProbabilityMeasure P] (hε : ∀ i, MemLp (fun ε : n → ℝ => ε i) 2 P)
    (h_mean : ∀ i, ∫ ε, ε i ∂P = 0) (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = Γ i j)
    (β_hat : (n → ℝ) → EuclideanSpace ℝ p) (hβ : ∀ ε, (β_hat ε).ofLp = M *ᵥ (X *ᵥ θ.ofLp + ε)) :
    biasOfLinearEstimator Sigma P β_hat θ =
        ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) ∧
      varianceOfLinearEstimator Sigma P β_hat = Matrix.trace (M * Γ * Mᵀ * Sigma) ∧
      risk Sigma P β_hat θ =
        ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) +
          Matrix.trace (M * Γ * Mᵀ * Sigma) := by
  have hMε : ∀ j, MemLp (fun ε : n → ℝ => (M *ᵥ ε) j) 2 P := fun j => by
    simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun i _ => (hε i).const_mul _
  have hcoord : ∀ ε j, (β_hat ε).ofLp j = ((M * X) *ᵥ θ.ofLp) j + (M *ᵥ ε) j := fun ε j => by
    rw [hβ, Matrix.mulVec_add, Matrix.mulVec_mulVec]; rfl
  have hβ_mem : ∀ j, MemLp (fun ε => (β_hat ε).ofLp j) 2 P := fun j => by
    have h := (memLp_const (((M * X) *ᵥ θ.ofLp) j)).add (hMε j)
    refine h.ae_eq (.of_forall fun ε => ?_)
    simp [hcoord]
  have hMmean : ∀ j, ∫ ε, (M *ᵥ ε) j ∂P = 0 := fun j => by
    simp only [Matrix.mulVec, dotProduct]
    rw [integral_finsetSum _ fun i _ => ((hε i).const_mul _).integrable (by simp)]
    simp [integral_const_mul, h_mean]
  have hmean : ∀ j, ∫ ε, (β_hat ε).ofLp j ∂P = ((M * X) *ᵥ θ.ofLp) j := fun j => by
    simp_rw [hcoord]
    rw [integral_add (integrable_const _) ((hMε j).integrable (by simp)), hMmean]; simp
  have hbias : biasOfLinearEstimator Sigma P β_hat θ =
      ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) := by
    unfold biasOfLinearEstimator
    congr 2 <;>
    · funext j
      simp [eval_integral_piLp (fun j => (hβ_mem j).integrable (by simp)), hmean,
        Matrix.sub_mulVec]
  have hvar : varianceOfLinearEstimator Sigma P β_hat = Matrix.trace (M * Γ * Mᵀ * Sigma) := by
    unfold varianceOfLinearEstimator
    congr 1
    congr 1
    ext j k
    have := integral_dotProduct_mul_dotProduct (μ := P) (fun ε : n → ℝ => ε) hε Γ h_cov (M j) (M k)
    simp only [covCondXOfLinearEstimator, covariance, hmean]
    have hpt : ∀ ω : n → ℝ, ((β_hat ω).ofLp j - ((M * X) *ᵥ θ.ofLp) j) *
        ((β_hat ω).ofLp k - ((M * X) *ᵥ θ.ofLp) k) = (ω ⬝ᵥ M j) * (ω ⬝ᵥ M k) := fun ω => by
      rw [hcoord, hcoord, add_sub_cancel_left, add_sub_cancel_left, dotProduct_comm ω,
        dotProduct_comm ω]
      rfl
    simp_rw [hpt]
    rw [this]
    exact (Matrix.mul_mul_transpose_apply M Γ j k).symm
  exact ⟨hbias, hvar, by rw [risk_eq_bias_add_variance Sigma β_hat θ hβ_mem, hbias, hvar]⟩


/-- **Bias–variance decomposition for isotropic noise.** For centered noise with `Cov ε = σ² I`, the
estimator `θ̂ = M (X θ⋆ + ε)` has bias `‖(M X - I) θ⋆‖²_Σ`, variance `σ² Tr (M Mᵀ Σ)`, and risk
their sum. This is `linearEstimator_bias_variance` with `Γ = σ² I`. -/
theorem linearEstimator_bias_variance_isotropic [DecidableEq p] [DecidableEq n]
    (M : Matrix p n ℝ) (X : Matrix n p ℝ) (θ : EuclideanSpace ℝ p) (Sigma : Matrix p p ℝ)
    (σ_sq : ℝ) (P : Measure (n → ℝ)) [IsProbabilityMeasure P]
    (hε : ∀ i, MemLp (fun ε : n → ℝ => ε i) 2 P) (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (n → ℝ) → EuclideanSpace ℝ p) (hβ : ∀ ε, (β_hat ε).ofLp = M *ᵥ (X *ᵥ θ.ofLp + ε)) :
    biasOfLinearEstimator Sigma P β_hat θ =
        ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) ∧
      varianceOfLinearEstimator Sigma P β_hat = σ_sq * Matrix.trace (M * Mᵀ * Sigma) ∧
      risk Sigma P β_hat θ =
        ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) +
          σ_sq * Matrix.trace (M * Mᵀ * Sigma) := by
  have h := linearEstimator_bias_variance M X θ Sigma (σ_sq • (1 : Matrix n n ℝ)) P hε h_mean
    (fun i j => by simpa [Matrix.one_apply] using h_cov i j) β_hat hβ
  have htr : Matrix.trace (M * (σ_sq • (1 : Matrix n n ℝ)) * Mᵀ * Sigma) =
      σ_sq * Matrix.trace (M * Mᵀ * Sigma) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul]
  rwa [htr] at h

/-- **HMRT Lemma 1 from the linear model.** In `y = X θ + ε` with centered isotropic noise
`Cov ε = σ² I`, the estimator `θ̂ = Σ̂⁺ Xᵀ y / n` with `Σ̂ = Xᵀ X / n` and a symmetric
pseudo-inverse `Σ̂⁺` (`Σ̂⁺ Σ̂ Σ̂⁺ = Σ̂⁺`, `Σ̂⁺ Σ̂` symmetric) has conditional bias
`θᵀ Π Σ Π θ` (`Π = 1 - Σ̂⁺ Σ̂`) and variance `σ² / n · Tr (Σ̂⁺ Σ)`.

This derives the bias and variance assumed in `LinearRegression.lemma1` (`E θ̂ = Σ̂⁺ Σ̂ θ`,
`Cov θ̂ = σ² / n · Σ̂⁺`) from `linearEstimator_bias_variance_isotropic`, with `M = Σ̂⁺ Xᵀ / n`:
`M X = Σ̂⁺ Σ̂` and `M Mᵀ = Σ̂⁺ Σ̂ Σ̂⁺ / n = Σ̂⁺ / n`. -/
theorem lemma1_of_linear_model [DecidableEq p] [DecidableEq n] (X : Matrix n p ℝ)
    (Sigma Sigma_dagger : Matrix p p ℝ) (hn : 0 < Fintype.card n) (h_sym : Sigma_dagger.IsSymm)
    (h_pinv : Sigma_dagger * ((1 / (Fintype.card n : ℝ)) • (Xᵀ * X)) * Sigma_dagger = Sigma_dagger)
    (h_proj : (1 - Sigma_dagger * ((1 / (Fintype.card n : ℝ)) • (Xᵀ * X))).IsSymm)
    (θ : EuclideanSpace ℝ p) (σ_sq : ℝ)
    (P : Measure (n → ℝ)) [IsProbabilityMeasure P] (hε : ∀ i, MemLp (fun ε : n → ℝ => ε i) 2 P)
    (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (n → ℝ) → EuclideanSpace ℝ p)
    (hβ : ∀ ε, (β_hat ε).ofLp =
      ((Fintype.card n : ℝ)⁻¹ • (Sigma_dagger * Xᵀ)) *ᵥ (X *ᵥ θ.ofLp + ε)) :
    biasOfLinearEstimator Sigma P β_hat θ =
        θ.ofLp ⬝ᵥ (((1 - Sigma_dagger * ((1 / (Fintype.card n : ℝ)) • (Xᵀ * X))) * Sigma *
          (1 - Sigma_dagger * ((1 / (Fintype.card n : ℝ)) • (Xᵀ * X)))) *ᵥ θ.ofLp) ∧
      varianceOfLinearEstimator Sigma P β_hat =
        (σ_sq / (Fintype.card n : ℝ)) * Matrix.trace (Sigma_dagger * Sigma) := by
  set Sh : Matrix p p ℝ := (1 / (Fintype.card n : ℝ)) • (Xᵀ * X) with hSh
  set c : ℝ := (Fintype.card n : ℝ)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  have hMX : (c • (Sigma_dagger * Xᵀ)) * X = Sigma_dagger * Sh := by
    rw [hSh, one_div, ← hc, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_smul]
  obtain ⟨hbias, hvar, -⟩ := linearEstimator_bias_variance_isotropic (c • (Sigma_dagger * Xᵀ)) X
    θ Sigma σ_sq P hε h_mean h_cov β_hat hβ
  refine ⟨?_, ?_⟩
  · rw [hbias, hMX]
    have := lemma1_bias Sigma Sh Sigma_dagger h_proj
      (WithLp.toLp 2 ((Sigma_dagger * Sh) *ᵥ θ.ofLp)) θ rfl
    simpa [Matrix.sub_mulVec] using this
  · rw [hvar]
    have hMM : (c • (Sigma_dagger * Xᵀ)) * (c • (Sigma_dagger * Xᵀ))ᵀ = c • Sigma_dagger := by
      have hXX : Xᵀ * X = c⁻¹ • Sh := by
        rw [hSh, one_div, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      calc (c • (Sigma_dagger * Xᵀ)) * (c • (Sigma_dagger * Xᵀ))ᵀ
          = c • c • (Sigma_dagger * (Xᵀ * X) * Sigma_dagger) := by
            simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
              h_sym.eq, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
        _ = c • Sigma_dagger := by
            rw [hXX]
            simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, h_pinv]
            rw [mul_inv_cancel₀ hc0, mul_one]
    rw [hMM, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hc]
    ring

end LinearRegression.DoubleDescent

end
