/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import LeanMachineLearning.Optimization.LinearRegression.HMRT

/-!
# Non-asymptotic foundations for double descent

Exact, finite-sample facts about linear estimators `θ̂ = M y` in the model `y = X θ⋆ + ε`, used by
the double-descent analysis of random-feature regression (Bach 2024; Hastie–Montanari–Rosset–
Tibshirani 2022; Belkin–Hsu–Ma–Mandal 2019). Everything is stated in terms of the existing
`LinearRegression.risk`, `LinearRegression.bias` and `LinearRegression.variance`, and no new
definitions are introduced: the measurement operator is just the matrix `M` (for random features
`M = S Z†`).

* `integral_dotProduct_mulVec_self`, `integral_dotProduct_mul_dotProduct`: second-moment
  identities `E[xᵀ S x] = Tr (S Γ)` and `E[(x ⬝ a)(x ⬝ b)] = a ⬝ Γ b`, where `Γ` is the
  second-moment matrix of a square-integrable random vector `x`;
* `excess_prediction_risk_eq_mahalanobis`, `excess_prediction_risk_eq_param_risk_isotropic`:
  `E_{x_new}[(x_new ⬝ (θ̂ - θ⋆))²]` is the `Σ`-norm (resp. squared Euclidean norm) of `θ̂ - θ⋆`;
* `risk_eq_bias_add_variance`: `R = B + V` for any estimator with square-integrable coordinates;
* `linear_estimator_error_partition`: `θ̂ - θ⋆ = (M X - I) θ⋆ + M ε`;
* `linearEstimator_bias_variance`: for centered noise of covariance `Γ`,
  `B = ‖(M X - I) θ⋆‖²_Σ` and `V = Tr (M Γ Mᵀ Σ)`;
* `exact_conditional_bias_variance_decomposition`: the isotropic case
  `E ‖θ̂ - θ⋆‖² = ‖(M X - I) θ⋆‖² + σ² Tr (Mᵀ M)`.
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

/-- Error vector partition for an arbitrary linear estimator `θ̂ = M y`, `y = X θ⋆ + ε`. -/
theorem linear_estimator_error_partition [DecidableEq p]
    (M : Matrix p n ℝ) (X : Matrix n p ℝ) (θ_star : p → ℝ) (ε : n → ℝ) :
    M *ᵥ (X *ᵥ θ_star + ε) - θ_star = (M * X - 1) *ᵥ θ_star + M *ᵥ ε := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

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
    risk Sigma μ β_hat β = bias Sigma μ β_hat β + variance Sigma μ β_hat := by
  set d : p → ℝ := fun j => μ[fun ω => β_hat ω j] - β j with hd
  have hx : ∀ j, MemLp (fun ω => (β_hat ω - β).ofLp j) 2 μ := fun j => by
    exact (h j).sub (memLp_const (β j))
  have hΓ := fun j k => integral_sub_mul_sub (h j) (h k) (β j) (β k)
  have hrisk := integral_dotProduct_mulVec_self (μ := μ) (fun ω => (β_hat ω - β).ofLp) hx
    (covCondX μ β_hat + Matrix.vecMulVec d d) (fun j k => by
      simpa [covCondX, Matrix.vecMulVec_apply, hd] using hΓ j k) Sigma
  have hbias : ((∫ ω, β_hat ω ∂μ) - β : p → ℝ) = d := funext fun j => by
    simp [hd, eval_integral_piLp (fun j => (h j).integrable (by simp))]
  unfold risk bias variance
  rw [hbias]
  refine hrisk.trans ?_
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_comm, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm, add_comm]


omit [Fintype p] in
/-- Entries of `M Γ Mᵀ` are bilinear forms in the rows of `M`: `M j ⬝ Γ (M k) = (M Γ Mᵀ) j k`. -/
private theorem dotProduct_mulVec_row_eq (M : Matrix p n ℝ) (Γ : Matrix n n ℝ) (j k : p) :
    M j ⬝ᵥ (Γ *ᵥ M k) = (M * Γ * Mᵀ) j k := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

/-- **Exact conditional bias–variance decomposition for a linear estimator** `θ̂ = M (X θ⋆ + ε)`
with centered noise of covariance `Γ`: the bias is `‖(M X - I) θ⋆‖²_Σ` and the variance is
`Tr (M Γ Mᵀ Σ)`; in particular `R = B + V`. -/
theorem linearEstimator_bias_variance [DecidableEq p] (M : Matrix p n ℝ) (X : Matrix n p ℝ)
    (θ : EuclideanSpace ℝ p) (Sigma : Matrix p p ℝ) (Γ : Matrix n n ℝ)
    (P : Measure (n → ℝ)) [IsProbabilityMeasure P] (hε : ∀ i, MemLp (fun ε : n → ℝ => ε i) 2 P)
    (h_mean : ∀ i, ∫ ε, ε i ∂P = 0) (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = Γ i j)
    (β_hat : (n → ℝ) → EuclideanSpace ℝ p) (hβ : ∀ ε, (β_hat ε).ofLp = M *ᵥ (X *ᵥ θ.ofLp + ε)) :
    bias Sigma P β_hat θ =
        ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) ∧
      variance Sigma P β_hat = Matrix.trace (M * Γ * Mᵀ * Sigma) ∧
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
  have hbias : bias Sigma P β_hat θ =
      ((M * X - 1) *ᵥ θ.ofLp) ⬝ᵥ (Sigma *ᵥ ((M * X - 1) *ᵥ θ.ofLp)) := by
    unfold bias
    congr 2 <;>
    · funext j
      simp [eval_integral_piLp (fun j => (hβ_mem j).integrable (by simp)), hmean,
        Matrix.sub_mulVec]
  have hvar : variance Sigma P β_hat = Matrix.trace (M * Γ * Mᵀ * Sigma) := by
    unfold variance
    congr 1
    congr 1
    ext j k
    have := integral_dotProduct_mul_dotProduct (μ := P) (fun ε : n → ℝ => ε) hε Γ h_cov (M j) (M k)
    simp only [covCondX, covariance, hmean]
    have hpt : ∀ ω : n → ℝ, ((β_hat ω).ofLp j - ((M * X) *ᵥ θ.ofLp) j) *
        ((β_hat ω).ofLp k - ((M * X) *ᵥ θ.ofLp) k) = (ω ⬝ᵥ M j) * (ω ⬝ᵥ M k) := fun ω => by
      rw [hcoord, hcoord, add_sub_cancel_left, add_sub_cancel_left, dotProduct_comm ω,
        dotProduct_comm ω]
      rfl
    simp_rw [hpt]
    rw [this]
    exact dotProduct_mulVec_row_eq M Γ j k
  exact ⟨hbias, hvar, by rw [risk_eq_bias_add_variance Sigma β_hat θ hβ_mem, hbias, hvar]⟩


/-- **Exact conditional bias–variance decomposition (isotropic noise, parameter risk).**
`E_ε ‖M (X θ⋆ + ε) - θ⋆‖² = ‖(M X - I) θ⋆‖² + σ² Tr (Mᵀ M)` for noise with `E ε = 0`,
`Cov ε = σ² I`. -/
theorem exact_conditional_bias_variance_decomposition [DecidableEq p] [DecidableEq n]
    (M : Matrix p n ℝ) (X : Matrix n p ℝ) (θ : EuclideanSpace ℝ p) (σ_sq : ℝ)
    (P : Measure (n → ℝ)) [IsProbabilityMeasure P] (hε : ∀ i, MemLp (fun ε : n → ℝ => ε i) 2 P)
    (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (n → ℝ) → EuclideanSpace ℝ p) (hβ : ∀ ε, (β_hat ε).ofLp = M *ᵥ (X *ᵥ θ.ofLp + ε)) :
    ∫ ε, ‖β_hat ε - θ‖ ^ 2 ∂P =
      ‖(WithLp.toLp 2 ((M * X - 1) *ᵥ θ.ofLp) : EuclideanSpace ℝ p)‖ ^ 2 +
        σ_sq * Matrix.trace (Mᵀ * M) := by
  have hsq : ∀ v : EuclideanSpace ℝ p,
      ‖v‖ ^ 2 = v.ofLp ⬝ᵥ (1 : Matrix p p ℝ) *ᵥ v.ofLp := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; simp [dotProduct, sq]
  obtain ⟨-, -, hrisk⟩ := linearEstimator_bias_variance M X θ 1 (σ_sq • (1 : Matrix n n ℝ)) P hε
    h_mean (fun i j => by simpa [Matrix.one_apply] using h_cov i j) β_hat hβ
  simp_rw [hsq]
  simp only [risk] at hrisk
  rw [show ∫ ε, (β_hat ε - θ).ofLp ⬝ᵥ (1 : Matrix p p ℝ) *ᵥ (β_hat ε - θ).ofLp ∂P = _ from hrisk]
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm M]

end LinearRegression.DoubleDescent

end
