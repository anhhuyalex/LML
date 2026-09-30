/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Kernel
public import LeanMachineLearning.Optimization.NTK.Initialization
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# The Infinite-Width NTK Regime and Linearized Dynamics

This file formalizes the infinite-width Neural Tangent Kernel (NTK) regime and its exact
linearized training dynamics, corresponding to Jacot et al. (2018) and Lee et al. (2019).

## Mathematical Formulation

* **Proposition 2.15 (Finite-Width Output/Residual ODE under Gradient Flow)**: For the empirical
  MSE loss `L(θ) = (1 / 2m) ‖f(θ) - y‖²`, continuous gradient flow `∂_t θ(t) = -∇_θ L(θ(t))`
  induces the exact finite-width function-space dynamics:
    `∂_t f(t) = - (1 / m) K_t (f(t) - y) = - (1 / m) K_t r(t)`
    `∂_t r(t) = - (1 / m) K_t r(t)`
  where `K_t = J(θ(t)) J(θ(t))ᵀ` is the empirical NTK Gram matrix at time `t`, proved by a
  five-step multivariate-chain-rule derivation.

* **Generalization to Arbitrary Differentiable Loss Functions**: Proposition 2.15 specializes the
  empirical risk to the squared loss `ℓ(f,y) = (1/2)(f-y)²`. For any pointwise loss
  `ℓ : ℝ → ℝ → ℝ` differentiable in its first argument, with generalized empirical risk
  `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)` and generalized residual `r^α(t) = ∂_f ℓ(f^α(t), y^α)`
  (squared loss gives `r^α = f^α - y^α`; logistic loss `ℓ(f,y) = log(1+exp(-yf))` gives
  `r^α = -y^α σ(-y^α f^α)`; exponential loss `ℓ(f,y) = exp(-yf)` gives `r^α = -y^α exp(-y^α f^α)`),
  gradient flow induces the generalized output evolution `∂_t f(t) = - (1/m) K_t r(t)`. Proposition
  2.15's squared-loss theorems are proved as corollaries of this general result.

* **Proposition 2.17 (Risk Dissipation Identity)**: Along continuous gradient flow for the
  generalized empirical risk `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)`, the instantaneous rate of risk
  dissipation is:
    `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
  * **Step 1 (Chain Rule on Empirical Risk)**: `∂_t L(θ(t)) = (1/m) ∑_α r^α(t) ∂_t f^α(t)
    = (1/m) r(t)ᵀ ∂_t f(t)`.
  * **Step 2 (Substitution of Output Dynamics)**: insert `∂_t f(t) = - (1/m) K_t r(t)` to get
    `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
  * **Geometric and Stability Implications**: since `K_t` is positive semidefinite for every
    parameter state, the quadratic form `r(t)ᵀ K_t r(t) ≥ 0`, so the empirical risk is
    monotonically non-increasing: `∂_t L(θ(t)) ≤ 0`. If the smallest Rayleigh quotient of `K_t` is
    bounded below by `lambda_min > 0`, the dissipation rate is bounded strictly away from zero
    whenever `r(t) ≠ 0`: `∂_t L(θ(t)) ≤ - (lambda_min / m²) ‖r(t)‖²`.

* **Asymptotic Properties in the Infinite-Width Limit ($n \to \infty$)**:
  * **Property 1 (Deterministic Initialization)**: As width $n \to \infty$, the initial empirical
    kernel concentrates entrywise around a deterministic limit:
    `empiricalNTKFromRows σ' rows n x x' → limitingNTK σ' x x'` almost surely and in probability.
  * **Property 2 (Kernel Constancy / Lazy Training)**: Throughout gradient flow, parameter
    displacement satisfies `‖θ(t) - θ₀‖₂ ≤ C / √n`, freezing the empirical kernel in time:
    `‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ L_K * C / √n`.
    As `n → ∞`, the kernel displacement vanishes:
    `lim_{n → ∞} ‖K_t^{(n)} - K_0^{(n)}‖_F = 0`,
    yielding the exact time-invariant differential operator `K_t ≡ K_∞`.

* **Closed-Form Linear Output Dynamics**:
  * In the infinite-width limit, the output differential equation reduces to a linear autonomous
    ODE with constant matrix coefficients:
    `∂_t r(t) = - (1 / m) K_∞ r(t)`.
  * Integration via the matrix exponential operator yields the closed-form trajectory of residuals:
    `r(t) = exp(- (t / m) K_∞) r(0)`.
  * Closed-form trajectory of network predictions:
    `f(t) = y + exp(- (t / m) K_∞) (f(0) - y)`.

* **Theorem (Exponential Convergence of Training Loss)**:
  Assume the limiting NTK Gram matrix satisfies the Rayleigh-Ritz condition with parameter
  `lambda_min > 0` (`vᵀ K_∞ v ≥ lambda_min ‖v‖²`).
  Then the training residual norm and empirical loss decay exponentially to zero:
    `‖r(t)‖₂ ≤ ‖r(0)‖₂ exp(- (lambda_min / m) t)`
    `L(θ(t)) ≤ L(θ₀) exp(- (2 lambda_min / m) t)`.

* **Step-by-Step Proof of Exponential Convergence**:
  * **Step 1**: Compute the time derivative of the squared residual norm `‖r(t)‖²`:
    `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K_∞ r(t)`.
  * **Step 2**: Use the Rayleigh-Ritz variational characterization `rᵀ K_∞ r ≥ lambda_min ‖r‖²`:
    `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`.
  * **Step 3**: Apply Grönwall's differential inequality to obtain the exponential bound:
    `‖r(t)‖² ≤ ‖r(0)‖² exp(- (2 lambda_min / m) t)` and
    `‖r(t)‖ ≤ ‖r(0)‖ exp(- (lambda_min / m) t)`.
  * **Step 4**: Multiply by `1 / (2m)` to obtain the exponential empirical loss bound:
    `L(θ(t)) = (1 / 2m) ‖r(t)‖² ≤ L(θ₀) exp(- (2 lambda_min / m) t)`.

## Main results

* `NTK.hasDerivAt_trainingOutputs_coord` : Step 1 chain rule `∂_t f^α(t) = ⟨∇_θ f^α, ∂_t θ⟩`.
* `NTK.hasDerivAt_trainingOutputs_coord_sum` : Step 1 coordinate-sum chain rule.
* `NTK.hasDerivAt_euclideanSpace` : Helper relating vector- and coordinate-wise `HasDerivAt`.
* `NTK.generalizedEmpiricalRisk` : General empirical risk `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)`.
* `NTK.generalizedResidual` : General residual `r^α := ∂_f ℓ(f^α(θ), y^α)`.
* `NTK.hasDerivAt_squaredLoss` : Concrete example, squared loss residual `r^α = f^α - y^α`.
* `NTK.hasDerivAt_logisticLoss` : Concrete example, logistic loss residual `r^α = -y^α σ(-y^α f^α)`.
* `NTK.hasDerivAt_exponentialLoss` : Concrete example, exponential loss residual.
* `NTK.hasFDerivAt_generalizedLoss_term` : Chain rule for a single generalized loss term.
* `NTK.gradient_generalizedRisk` : Gradient of the generalized empirical risk.
* `NTK.gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad` : Step 2, generalized loss.
* `NTK.gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner` : Step 3, generalized loss.
* `NTK.gradient_flow_generalizedOutput_coord_ode` : Step 4, generalized loss.
* `NTK.gradient_flow_generalizedOutput_vector_ode` : Step 5, generalized output evolution
  `∂_t f(t) = - (1/m) K_t r(t)`.
* `NTK.gradient_flow_output_coord_deriv_eq_inner_grad` : Step 2 (squared loss), corollary.
* `NTK.gradient_flow_output_coord_deriv_eq_sum_inner` : Step 3 (squared loss), corollary.
* `NTK.gradient_flow_output_coord_ode` : Step 4 (squared loss), corollary.
* `NTK.gradient_flow_output_vector_ode` : Step 5 output ODE
  `∂_t f(t) = - (1/m) K_t r(t)`, corollary.
* `NTK.gradient_flow_output_vector_ode_sub_y` : Step 5 output ODE
  `∂_t f(t) = - (1/m) K_t (f(t) - y)`.
* `NTK.gradient_flow_residual_vector_ode` : Step 5 residual ODE `∂_t r(t) = - (1/m) K_t r(t)`.
* `NTK.hasDerivAt_generalizedEmpiricalRisk_coord_sum` : Prop 2.17 Step 1, chain rule
  `∂_t L(θ(t)) = (1/m) r(t)ᵀ ∂_t f(t)`.
* `NTK.risk_dissipation_identity` : **Proposition 2.17**, risk dissipation identity
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
* `NTK.risk_dissipation_nonpos` : Monotone risk dissipation `∂_t L(θ(t)) ≤ 0` via PSD `K_t`.
* `NTK.risk_dissipation_le_of_rayleighRitz` : Strict dissipation bound
  `∂_t L(θ(t)) ≤ - (lambda_min / m²) ‖r(t)‖²` under a Rayleigh-Ritz condition on `K_t`.
* `NTK.gronwall_exponential_decay` : Reusable Grönwall differential inequality for linear decay.
* `NTK.deriv_norm_sq_linear_ode` : Step 1 derivative `(d/dt) ‖r(t)‖² = - (2/m) r(t)ᵀ K_∞ r(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz` : Step 2 bound `(d/dt) ‖r(t)‖² ≤ - (2 λ / m) ‖r(t)‖²`.
* `NTK.residual_norm_sq_exponential_decay` : Step 3 squared residual norm decay.
* `NTK.residual_norm_exponential_decay` : Step 3 residual norm decay.
* `NTK.mse_loss_exponential_decay` : Step 4 empirical MSE loss decay.
* `NTK.gronwall_exponential_decay_Icc` : Interval-restricted Grönwall decay lemma on `[0, T]`.
* `NTK.deriv_norm_sq_timeVarying_ode` : Step 1 derivative for time-varying NTK `K(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz_timeVarying` : Step 2 Rayleigh-Ritz bound for `K(t)`.
* `NTK.residual_norm_sq_exponential_decay_timeVarying` : Step 3 squared residual decay for `K(t)`.
* `NTK.residual_norm_exponential_decay_timeVarying` : Step 3 residual norm decay for `K(t)`.
* `NTK.rayleigh_lower_bound_on_ball`, `NTK.lazy_training_global_bounds_of_ball_hypotheses` :
  Rayleigh bound on the bootstrap ball and the global consequences (displacement, uniform gap,
  kernel drift, exponential residual and loss decay) of the positive-gap bootstrap.
* `NTK.norm_sub_sub_fderiv_le_of_lipschitz_fderiv`,
  `NTK.norm_trainingOutputs_sub_linearization_le` :
  `C^{1,1}` Taylor bound `(L / 2) ‖x - x₀‖²` for any map with an `L`-Lipschitz Fréchet derivative,
  and its instance for the training outputs under an `L`-Lipschitz output Jacobian (Phase 12).
* `NTK.matrixCLM`, `NTK.inner_matrixCLM_transpose`, `NTK.hasDerivAt_affineFlowSolution`,
  `NTK.affineFlow_eq_solution`, `NTK.affine_minNorm_pythagoras`, `NTK.norm_affine_limit_le`,
  `NTK.eq_affine_limit_of_norm_le`, `NTK.tendsto_affineFlowSolution`, `NTK.inner_affine_limit` :
  Phase 14.1 - for an arbitrary matrix `J` with invertible Gram matrix `J Jᵀ`, the closed form of
  the affine gradient flow, its convergence to the minimum-norm interpolant `-Jᵀ (J Jᵀ)⁻¹ r₀`,
  the Pythagoras identity proving minimality, and the kernel-regression form of its prediction.
* `NTK.hasDerivAt_predictionError_abs_le`, `NTK.abs_inner_displacement_add_frozenPrediction_le`,
  `NTK.abs_sub_le_of_abs_deriv_le_exp`,
  `NTK.abs_inner_displacement_add_frozenPrediction_le_of_exp_decay` : Phase 14.2 - deterministic
  test-point prediction error along a gradient flow, on a finite window and uniformly in time under
  exponential residual decay.
* `NTK.tendsto_zero_of_le_mul_exp_neg` : exponential bound implies convergence to zero.
* `NTK.exists_forward_flow`, `NTK.forwardFlow_unique`, `NTK.lipschitz_on_ball_of_locallyLipschitz` :
  Phase 10-11 generic forward-time flow of a field that is Lipschitz on balls and has a priori
  bounds (Mathlib's Picard-Lindelöf on a cutoff field, the bootstrap `le_of_forall_bootstrap`,
  gluing by uniqueness),
  with forward uniqueness; plus small `LocallyLipschitz` algebra helpers.
* `NTK.mseLoss_le_of_hasDerivWithinAt_neg_gradient`, `NTK.gronwallBound_le_mul_exp`,
  `NTK.continuousOn_trainingResidual_comp` : loss monotonicity along a local gradient-flow solution,
  an explicit bound on Mathlib's Grönwall function, and continuity of the residual along a curve.
* `NTK.le_of_forall_bootstrap` : generic continuous-induction principle on `[0, T]` (via Mathlib's
  `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset`), shared by both displacement bootstraps.
* `NTK.displacement_le_integral_of_rayleigh`, `NTK.displacement_bound_of_psd` : displacement
  bounded by the integral of the speed bound; the `lambda_min = 0` case gives the no-gap linear
  bound.
* `NTK.finite_horizon_displacement_bound`, `NTK.finite_horizon_kernel_freeze_bound` : finite-horizon
  bootstrap and kernel freeze on `[0, T]` with no spectral gap.
* `NTK.norm_sub_le_of_linear_ode_perturbation` : **Phase 7** generic stability of `r' = -A(t) r`
  against `s' = -B(t) s` for PSD `A`: `‖r - s‖ ≤ ‖r(0) - s(0)‖ + a t` if `‖A - B‖ ‖s‖ ≤ a`.
* `NTK.residual_sub_frozen_residual_le` : Phase 7 specialization to the NTK residual dynamics with
  coefficients `K(t) / m` and `K_∞ / m`.
* `NTK.mse_loss_exponential_decay_timeVarying` : Step 4 MSE loss decay for `K(t)`.
* `NTK.residual_norm_sq_exponential_decay_timeVarying_Icc` : Local interval squared residual decay.
* `NTK.residual_norm_exponential_decay_timeVarying_Icc` : Local interval residual decay on `[0, T]`.
* `NTK.matrix_exp_residual_trajectory_zero` : Initial condition `r(0) = r₀`.
* `NTK.matrix_exp_output_trajectory_zero` : Initial condition `f(0) = f₀`.
* `NTK.matrix_exp_residual_eq_output_sub_y` : Residual relation `f(t) - y = r(t)`.
* `NTK.matrix_exp_residual_trajectory_hasDerivAt` : Residual ODE satisfaction
  via matrix exponential.
* `NTK.matrix_exp_output_trajectory_hasDerivAt` : Output ODE satisfaction via matrix exponential.
* `NTK.matrix_exp_residual_decay` : Exponential decay for explicit matrix exponential trajectory.
* `NTK.matrix_exp_loss_decay` : Exponential loss decay for explicit matrix exponential trajectory.
* `NTK.empiricalNTKMatrix_sub_le_of_jacobian_bound` : Frobenius norm bound
  `‖K(θ₁) - K(θ₂)‖ ≤ 2 * M * ‖J(θ₁) - J(θ₂)‖`.
* `NTK.empiricalNTKMatrix_sub_le_of_jacobian_lipschitz` : Pointwise Lipschitz propagation
  `‖K(θ₁) - K(θ₂)‖ ≤ (2 * M * L_J) * ‖θ₁ - θ₂‖`.
* `NTK.empiricalNTKMatrix_lipschitz_of_jacobian_bound` : Gap 2 deliverable, deterministic
  Lipschitz propagation on any set `S` around `θ₀`.
* `NTK.empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound` : Kernel freeze bound
  `‖K(θ(t)) - K(θ₀)‖ ≤ (2 * M * L_J) * C` instantiated with Jacobian bounds
  (the `1/√n` decay lives in `L_J`, not in the displacement bound `C` - see `Kernel.lean`'s
  `gradient_mseLoss_norm_le` and this file's Rayleigh-quotient stability theorems below).
* `NTK.abs_dotProduct_mulVec_sub_le` : Quadratic forms of nearby matrices are close:
  `|vᵀ A v - vᵀ B v| ≤ ‖A - B‖ ‖v‖²`.
* `NTK.rayleigh_lower_bound_of_sub_smul_posSemidef` : Shifted positive semidefiniteness implies
  a Rayleigh-quotient lower bound: `(K - λ • 1).PosSemidef ⟹ λ ‖v‖² ≤ vᵀ K v`.
* `NTK.rayleigh_quotient_lower_bound_of_matrix_dist` : Rayleigh-quotient stability under a
  matrix distance bound `‖K - K₀‖ ≤ ε`.
* `NTK.rayleigh_quotient_lower_bound_of_displacement` : Gap 5 Step 2 deliverable - the
  spectral-gap hypothesis at `θ₀` propagates to any `θ` with degraded constant
  `lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖`.
* `NTK.restrictCoords`, `NTK.norm_restrictCoords_gradient_mseLoss_le`,
  `NTK.norm_map_sub_le_integral_of_gfTrajectory` : displacement of a *block of coordinates* (or any
  continuous linear image) of a gradient flow is at most the integral of the speed of that block;
  the block speed under MSE flow is `(1/m) ‖J_block‖ ‖r‖`.
* `NTK.integral_exp_neg_le` : Reusable bound `∫₀ᵀ exp(-c t) dt ≤ 1/c` for `c > 0`.
* `NTK.displacement_integral_bound` : Gap 5 Step 1 deliverable - a `T`-independent displacement
  cap `(M * ‖r₀‖) / lambda_min` given a uniform-in-time Rayleigh bound on `[0, T]`.
* `NTK.lazy_training_displacement_bound` : **Gap 5 deliverable** - the continuous-induction
  bootstrap discharging `hlazy` with a width-independent constant `C`.
* `NTK.lazy_training_kernel_freeze_bound` : Step 2 kernel freeze bound under lazy training.
* `NTK.tendsto_lazy_training_kernel_freeze` : Asymptotic freeze limit as `n → ∞`.
* `NTK.tendsto_lazy_training_kernel_freeze_matrix` : Empirical NTK matrix freeze as `n → ∞`.
* `NTK.deterministic_initialization_empiricalNTK_tendsto_ae` : Property 1 a.s. initialization limit.
* `NTK.deterministic_initialization_empiricalNTKMatrix_tendsto_ae` : Gram matrix a.s. limit.
* `NTK.deterministic_initialization_chebyshev_bound` : Property 1 entrywise Chebyshev bound.
* `NTK.tendsto_empiricalNTK_chebyshev_bound` : Property 1 Chebyshev tail decay in ENNReal.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace NTK

variable {ι : Type*} {d m P : ℕ}

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

local instance (priority := 2000) instCompleteSpaceMatrix (m : ℕ) :
    CompleteSpace (Matrix (Fin m) (Fin m) ℝ) :=
  FiniteDimensional.complete ℝ (Matrix (Fin m) (Fin m) ℝ)

/-! ### Continuous Gradient Flow and Function-Space Dynamics

This section formalizes the exact induced function-space training dynamics along the
continuous gradient flow trajectory:
  `∂_t θ(t) = - ∇_θ L(θ(t))`
under the empirical MSE loss. Across five sequential steps, we prove that the output vector
`f(t) ∈ ℝ^m` and residual error vector `r(t) = f(t) - y` satisfy the closed-form ODEs:
  `∂_t f(t) = - (1 / m) K_t (f(t) - y) = - (1 / m) K_t r(t)`
  `∂_t r(t) = - (1 / m) K_t r(t)`
where `K_t = J(θ(t)) J(θ(t))ᵀ ∈ ℝ^{m × m}` is the empirical NTK Gram matrix at time `t`.
In particular, for neural network architectures parameterized by width `n` (as in
`LeanMachineLearning.Optimization.NTK.Initialization`), `K_t` corresponds to the width-`n`
empirical kernel matrix `K_t^{(n)}`.
-/

/-- Helper: The inner product on `EuclideanSpace ℝ (Fin P)` equals the sum of entrywise products. -/
lemma euclideanSpace_inner_eq_sum (u v : EuclideanSpace ℝ (Fin P)) :
    ⟪u, v⟫ = ∑ j : Fin P, u j * v j := by
  rw [show u = WithLp.toLp 2 u.ofLp by rfl, show v = WithLp.toLp 2 v.ofLp by rfl]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

/-- Step 1 (Multivariate Chain Rule - Inner Product Formulation):
Evaluate the time derivative of component output `f^α(t) ≡ f(x^α; θ(t))`:
  `∂_t f^α(t) = ⟨∇_θ f(x^α; θ(t)), ∂_t θ(t)⟩`. -/
theorem hasDerivAt_trainingOutputs_coord
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P))
    (θ' : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t))
    (hθ : HasDerivAt θ_traj (θ' t) t) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ t := by
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hθ
  have hgrad : fderiv ℝ (fun θ' => f (X α) θ') (θ_traj t) (θ' t) =
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ := by
    rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply]
    rfl
  rw [hgrad] at hcomp
  exact hcomp

/-- Step 1 (Multivariate Chain Rule - Coordinate Sum Formulation):
Along any differentiable parameter curve `θ(t)`, the rate of change of the component
output satisfies:
  `∂_t f^α(t) = ∑_{j=1}^P (∂f(x^α; θ(t)) / ∂θ_j) · (dθ_j(t) / dt) = ⟨∇_θ f(x^α; θ(t)), ∂_t θ(t)⟩`.
-/
theorem hasDerivAt_trainingOutputs_coord_sum
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P))
    (θ' : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t))
    (hθ : HasDerivAt θ_traj (θ' t) t) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (∑ j : Fin P, tangentFeature f (X α) (θ_traj t) j * θ' t j) t := by
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj θ' t α hdiff hθ
  rw [euclideanSpace_inner_eq_sum] at h
  exact h

/-- Helper: a curve into `EuclideanSpace ℝ (Fin m)` has a derivative iff each of its coordinate
functions does, with matching coordinate derivatives. -/
lemma hasDerivAt_euclideanSpace (v : ℝ → EuclideanSpace ℝ (Fin m))
    (v' : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt v v' t ↔ ∀ i : Fin m, HasDerivAt (fun s => v s i) (v' i) t := by
  let e := (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearEquiv
  have h := hasDerivAt_pi (φ := fun s => e (v s)) (φ' := e v') (x := t)
  constructor
  · intro hv i
    have he := (e : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ)).hasFDerivAt.comp_hasDerivAt t hv
    exact (h.mp he) i
  · intro hi
    have he : HasDerivAt (fun s => e (v s)) (e v') t := h.mpr hi
    have h_orig :=
      (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).hasFDerivAt.comp_hasDerivAt t he
    convert h_orig
    · ext s; simp [e]
    · simp [e]

/-! ### Generalization to Arbitrary Differentiable Loss Functions

The residual ODE below (`gradient_flow_output_coord_deriv_eq_inner_grad` through
`gradient_flow_output_vector_ode`) specializes the empirical risk to the squared loss
`ℓ(f,y) = (1/2)(f - y)²`. More generally, for any pointwise loss `ℓ : ℝ → ℝ → ℝ` that is
differentiable in its first argument, define the empirical risk and the generalized scalar
residual:
  `L(θ) = (1/m) ∑_α ℓ(f(x^α; θ), y^α)`
  `r^α(t) = ∂_f ℓ(f^α(t), y^α)`
Concrete examples: squared loss `ℓ(f,y) = (1/2)(f-y)²` gives `r^α = f^α - y^α`; binary
logistic/cross-entropy loss `ℓ(f,y) = log(1 + exp(-y f))` gives `r^α = -y^α σ(-y^α f^α)`, where
`σ` is the sigmoid function; exponential loss `ℓ(f,y) = exp(-y f)` gives
`r^α = -y^α exp(-y^α f^α)`. By the multivariate chain rule, the parameter gradient and the output
evolution generalize to:
  `∇_θ L(θ(t)) = (1/m) ∑_β r^β(t) ∇_θ f(x^β; θ(t))`
  `∂_t f(t) = - (1/m) K_t r(t)`
The squared-loss theorems below are proved as corollaries of the general theorems here,
instantiated at `ℓ(f,y) = (1/2)(f-y)²`.
-/

/-- The generalized empirical risk under a pointwise loss `ℓ`:
  `L(θ) = (1 / m) ∑_α ℓ(f(x^α; θ), y^α)`. -/
noncomputable def generalizedEmpiricalRisk (ℓ : ℝ → ℝ → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) : ℝ :=
  (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ) (y α)

private lemma generalizedEmpiricalRisk_squaredLoss_eq_mseLoss
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) :
    generalizedEmpiricalRisk (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y = mseLoss f X y := by
  funext θ
  rw [generalizedEmpiricalRisk, mseLoss_eq_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The generalized scalar residual `r^α := ∂_f ℓ(f^α(θ), y^α)`. -/
noncomputable def generalizedResidual (ℓ : ℝ → ℝ → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun α => deriv (fun f' => ℓ f' (y α)) (f (X α) θ))

/-- Concrete Example (Squared Loss): for `ℓ(f,y) = (1/2)(f-y)²`, the generalized residual is
`∂_f ℓ(f,y) = f - y`. -/
theorem hasDerivAt_squaredLoss (f y : ℝ) :
    HasDerivAt (fun f' => (1 / 2 : ℝ) * (f' - y) ^ 2) (f - y) f := by
  have h1 : HasDerivAt (fun f' : ℝ => f' - y) 1 f := (hasDerivAt_id f).sub_const y
  have h2 := h1.pow 2
  have h3 := h2.const_mul (1 / 2 : ℝ)
  convert h3 using 1
  push_cast
  ring

private lemma generalizedResidual_squaredLoss_eq_trainingResidual
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) :
    generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ =
      trainingResidual f X y θ := by
  ext α
  change deriv (fun f' => (1 / 2 : ℝ) * (f' - y α) ^ 2) (f (X α) θ) = trainingResidual f X y θ α
  rw [(hasDerivAt_squaredLoss (f (X α) θ) (y α)).deriv]
  rfl

private lemma hasDerivAt_squaredLoss_generalizedResidual
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P)) (β : Fin m) :
    HasDerivAt (fun f' => (1 / 2 : ℝ) * (f' - y β) ^ 2)
      (generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ β)
      (f (X β) θ) := by
  have hval : generalizedResidual (fun f' y' => (1 / 2 : ℝ) * (f' - y') ^ 2) f X y θ β =
      f (X β) θ - y β := by
    rw [generalizedResidual_squaredLoss_eq_trainingResidual]
    rfl
  rw [hval]
  exact hasDerivAt_squaredLoss (f (X β) θ) (y β)

/-- Concrete Example (Binary Logistic / Cross-Entropy Loss): for `ℓ(f,y) = log(1 + exp(-y f))`,
the generalized residual is `∂_f ℓ(f,y) = -y σ(-y f)`, where `σ` is the sigmoid function. -/
theorem hasDerivAt_logisticLoss (f y : ℝ) :
    HasDerivAt (fun f' => Real.log (1 + Real.exp (-y * f'))) (-y * Real.sigmoid (-y * f)) f := by
  have h1 : HasDerivAt (fun f' : ℝ => -y * f') (-y) f := by
    simpa using (hasDerivAt_id f).const_mul (-y)
  have h2 := h1.exp
  have h3 := h2.const_add (1 : ℝ)
  have hpos : (1 : ℝ) + Real.exp (-y * f) ≠ 0 := by positivity
  have h4 := h3.log hpos
  convert h4 using 1
  rw [Real.sigmoid_def, Real.exp_neg (-y * f)]
  have hexp_pos : (0 : ℝ) < Real.exp (-y * f) := Real.exp_pos _
  have hexp_ne : Real.exp (-y * f) ≠ 0 := hexp_pos.ne'
  have h1e_ne : (1 : ℝ) + Real.exp (-y * f) ≠ 0 := by positivity
  have h1einv_ne : (1 : ℝ) + (Real.exp (-y * f))⁻¹ ≠ 0 := by positivity
  field_simp
  ring

/-- Concrete Example (Exponential Loss): for `ℓ(f,y) = exp(-y f)`, the generalized residual is
`∂_f ℓ(f,y) = -y exp(-y f)`. -/
theorem hasDerivAt_exponentialLoss (f y : ℝ) :
    HasDerivAt (fun f' => Real.exp (-y * f')) (-y * Real.exp (-y * f)) f := by
  have h1 : HasDerivAt (fun f' : ℝ => -y * f') (-y) f := by
    simpa using (hasDerivAt_id f).const_mul (-y)
  have h2 := h1.exp
  convert h2 using 1
  ring

/-- Generalizes `hasFDerivAt_sq_diff` (Kernel.lean) to an arbitrary differentiable pointwise loss,
via the scalar-outer/vector-inner chain rule. -/
lemma hasFDerivAt_generalizedLoss_term (θ : EuclideanSpace ℝ (Fin P))
    {g : EuclideanSpace ℝ (Fin P) → ℝ} (hg : DifferentiableAt ℝ g θ)
    {ℓ' : ℝ → ℝ} {r : ℝ} (hℓ : HasDerivAt ℓ' r (g θ)) :
    HasFDerivAt (fun θ' => ℓ' (g θ'))
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P)) (r • gradient g θ)) θ := by
  have h := hℓ.comp_hasFDerivAt θ hg.hasFDerivAt
  have h_eq : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P)) (r • gradient g θ) =
      r • fderiv ℝ g θ := by
    apply ContinuousLinearMap.ext
    intro v
    rw [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
      ← toDual_gradient, InnerProductSpace.toDual_apply_apply, inner_smul_left,
      starRingEnd_apply, star_trivial]
  rw [h_eq]
  exact h

/-- The gradient of the generalized empirical risk with respect to parameters:
  `∇_θ L(θ) = (1 / m) ∑_α r^α(θ) ∇_θ f(x^α; θ)`. -/
theorem gradient_generalizedRisk (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ)
    (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hf : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ)
    (hℓ : ∀ α : Fin m, HasDerivAt (fun f' => ℓ f' (y α))
      (generalizedResidual ℓ f X y θ α) (f (X α) θ)) :
    gradient (generalizedEmpiricalRisk ℓ f X y) θ =
      (m : ℝ)⁻¹ • ∑ α : Fin m, (generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ := by
  have h_term : ∀ α ∈ (Finset.univ : Finset (Fin m)),
      HasFDerivAt (fun θ' => ℓ (f (X α) θ') (y α))
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
          ((generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ)) θ := by
    intro α _
    exact hasFDerivAt_generalizedLoss_term θ (hf α) (hℓ α)
  have h_sum := HasFDerivAt.sum (u := Finset.univ) (A := fun α θ' => ℓ (f (X α) θ') (y α)) h_term
  have h_sum_eq : (∑ α ∈ (Finset.univ : Finset (Fin m)), fun θ' => ℓ (f (X α) θ') (y α)) =
      (fun θ' => ∑ α : Fin m, ℓ (f (X α) θ') (y α)) := by
    ext θ'
    simp only [Finset.sum_apply]
  rw [h_sum_eq] at h_sum
  have h_scaled := h_sum.const_smul (m : ℝ)⁻¹
  have h_risk_eq : generalizedEmpiricalRisk ℓ f X y =
      fun θ' => (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ') (y α) := rfl
  rw [h_risk_eq]
  have h_grad : HasGradientAt (fun θ' => (m : ℝ)⁻¹ * ∑ α : Fin m, ℓ (f (X α) θ') (y α))
      ((m : ℝ)⁻¹ • ∑ α : Fin m, (generalizedResidual ℓ f X y θ α) • tangentFeature f (X α) θ)
      θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h_scaled using 1
    ext v
    simp only [smul_apply, sum_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul,
      inner_smul_left, starRingEnd_apply, star_trivial, sum_inner, Finset.mul_sum]
  exact h_grad.gradient

/-- Step 2 (Substitution of Gradient Flow Law, Generalized Loss):
Insert the continuous gradient flow parameter ODE `∂_t θ(t) = -∇_θ L(θ(t))`:
  `∂_t f^α(t) = - ⟨∇_θ f(x^α; θ(t)), ∇_θ L(θ(t))⟩`. -/
theorem gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (-⟪tangentFeature f (X α) (θ_traj t),
        gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)⟫) t := by
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj
    (fun s => -gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj s)) t α hdiff hflow
  rw [inner_neg_right] at h
  exact h

/-- Step 3 (Insertion of Generalized Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1/m) ∑_β r^β(t) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - (1/m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ r^β(t)`. -/
theorem gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad ℓ f X y t hflow α (hf α)
  rw [gradient_generalizedRisk ℓ f X y (θ_traj t) hf hℓ] at h
  have h_inner : -⟪tangentFeature f (X α) (θ_traj t),
      (m : ℝ)⁻¹ • ∑ β : Fin m,
        (generalizedResidual ℓ f X y (θ_traj t) β) • tangentFeature f (X β) (θ_traj t)⟫ =
      - (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (generalizedResidual ℓ f X y (θ_traj t)) β := by
    rw [inner_smul_right, inner_sum]
    simp only [inner_smul_right]
    rw [neg_mul]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [h_inner] at h
  exact h

/-- Step 4 (Assembly with Empirical NTK, Generalized Loss):
Recognizing the empirical NTK matrix entries `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`:
  `∂_t f^α(t) = - (1/m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_generalizedOutput_coord_ode
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner ℓ f X y t hflow α hf hℓ
  have h_ntk : ∀ β : Fin m,
      ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ =
      empiricalNTKMatrix f X (θ_traj t) α β := by
    intro β
    exact (empiricalNTKMatrix_apply f X (θ_traj t) α β).symm
  simp_rw [h_ntk] at h
  exact h

/-- Step 5 (Generalized Output Evolution):
Along continuous gradient flow under an arbitrary differentiable pointwise loss `ℓ`, the training
output vector satisfies:
  `∂_t f(t) = - (1/m) K_t r(t)`,
where `r(t)` is the generalized residual vector `r^α(t) = ∂_f ℓ(f^α(t), y^α)`. -/
theorem gradient_flow_generalizedOutput_vector_ode
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
          (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t := by
  rw [hasDerivAt_euclideanSpace]
  intro α
  have h_coord := gradient_flow_generalizedOutput_coord_ode ℓ f X y t hflow α hf hℓ
  have h_eq : - (m : ℝ)⁻¹ *
      ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β =
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
          (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) : EuclideanSpace ℝ (Fin m)) α := by
    change - (m : ℝ)⁻¹ *
      ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β =
      (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) α
    have h_row : (empiricalNTKMatrix f X (θ_traj t)).row α =
      empiricalNTKMatrix f X (θ_traj t) α := rfl
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply, dotProduct, h_row]
  rw [h_eq] at h_coord
  exact h_coord

/-- Step 2 (Substitution of Gradient Flow Law):
Insert the continuous gradient flow parameter ODE `∂_t θ(t) = -∇_θ L(θ(t))`:
  `∂_t f^α(t) = - ⟨∇_θ f(x^α; θ(t)), ∇_θ L(θ(t))⟩`. -/
theorem gradient_flow_output_coord_deriv_eq_inner_grad
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (-⟪tangentFeature f (X α) (θ_traj t), gradient (mseLoss f X y) (θ_traj t)⟫) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow ⊢
  exact gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad _ f X y t hflow α hdiff

/-- Step 3 (Insertion of Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - ⟨∇_θ f^α(θ(t)), (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f^β(θ(t))⟩`
              `= - (1 / m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ (f^β(t) - y^β)`. -/
theorem gradient_flow_output_coord_deriv_eq_sum_inner
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner _ f X y t hflow α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 4 (Assembly with Empirical NTK):
Recognizing the empirical NTK matrix entries `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`:
  `∂_t f^α(t) = - (1 / m) ∑_β K_t^{α β} (f^β(t) - y^β) = - (1 / m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_output_coord_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ *
        ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_ode _ f X y t hflow α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 5 (Matrix-Vector Formulation for Output Vector):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_output_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_vector_ode _ f X y t hflow hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 5 (Matrix-Vector Formulation with Explicit `f(t) - y`):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t (f(t) - y)`. -/
theorem gradient_flow_output_vector_ode_sub_y
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        ((trainingOutputs f X (θ_traj t)) - y).ofLp))) t :=
  gradient_flow_output_vector_ode f X y t hflow hdiff

/-- Step 5 (Matrix-Vector Formulation for Residual Vector):
Function-space residual ODE under gradient flow:
  `∂_t r(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_residual_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  have h_out := gradient_flow_output_vector_ode f X y t hflow hdiff
  have h_sub := h_out.sub_const y
  convert h_sub using 1
  ext s
  rfl

/-! ### Proposition 2.17: Risk Dissipation Identity

Along continuous gradient flow for the generalized empirical risk `L(θ) = (1/m) ∑_α ℓ(f^α(θ), y^α)`,
the instantaneous rate of risk dissipation is governed entirely by the empirical NTK Gram matrix
acting on the residual vector:
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`.
Since `K_t` is positive semidefinite (`empiricalNTKMatrix_quad_form_nonneg` in `Kernel.lean`), the
empirical risk is monotonically non-increasing along gradient flow. If the smallest Rayleigh
quotient of `K_t` is bounded below by `lambda_min > 0`, the dissipation rate is in addition bounded
strictly away from zero whenever `r(t) ≠ 0`.
-/

/-- Step 1 (Chain Rule on Empirical Risk):
Along any curve `θ(t)` whose per-sample outputs `f^α(θ(t))` have known time derivatives `f'`, the
time derivative of the generalized empirical risk is the residual-weighted sum of output
derivatives:
  `∂_t L(θ(t)) = (1/m) ∑_α r^α(t) ∂_t f^α(t) = (1/m) r(t)ᵀ ∂_t f(t)`. -/
theorem hasDerivAt_generalizedEmpiricalRisk_coord_sum
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ)
    (f' : Fin m → ℝ)
    (hf' : ∀ α : Fin m, HasDerivAt (fun s => trainingOutputs f X (θ_traj s) α) (f' α) t)
    (hℓ : ∀ α : Fin m, HasDerivAt (fun v => ℓ v (y α))
      (generalizedResidual ℓ f X y (θ_traj t) α) (trainingOutputs f X (θ_traj t) α)) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      ((m : ℝ)⁻¹ * ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ f')) t := by
  have h_term : ∀ α : Fin m,
      HasDerivAt ((fun v => ℓ v (y α)) ∘ fun s => trainingOutputs f X (θ_traj s) α)
        (generalizedResidual ℓ f X y (θ_traj t) α * f' α) t :=
    fun α => HasDerivAt.comp t (hℓ α) (hf' α)
  have h_sum : HasDerivAt
      (fun s => ∑ α : Fin m, ((fun v => ℓ v (y α)) ∘ fun s' => trainingOutputs f X (θ_traj s') α) s)
      (∑ α : Fin m, generalizedResidual ℓ f X y (θ_traj t) α * f' α) t :=
    HasDerivAt.fun_sum (fun α _ => h_term α)
  have h_scaled := h_sum.const_mul (m : ℝ)⁻¹
  have h_rhs_eq :
      (m : ℝ)⁻¹ * ∑ α : Fin m, generalizedResidual ℓ f X y (θ_traj t) α * f' α =
        (m : ℝ)⁻¹ * ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ f') := by
    congr 1
  rw [h_rhs_eq] at h_scaled
  exact h_scaled

/-- Step 2 (Substitution of Output Dynamics):
Insert the generalized output dynamics `∂_t f(t) = - (1/m) K_t r(t)` into the risk derivative
formula, and simplify the resulting double sum into the quadratic form `r(t)ᵀ K_t r(t)`.

**Proposition 2.17 (Risk Dissipation Identity).** Along continuous gradient flow, the instantaneous
rate of risk dissipation satisfies:
  `∂_t L(θ(t)) = - (1/m²) r(t)ᵀ K_t r(t)`. -/
theorem risk_dissipation_identity
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t := by
  set r := generalizedResidual ℓ f X y (θ_traj t) with hr_def
  set K := empiricalNTKMatrix f X (θ_traj t) with hK_def
  set f' : Fin m → ℝ := fun α => - (m : ℝ)⁻¹ * ∑ β : Fin m, K α β * r β with hf'_def
  have hf' : ∀ α : Fin m, HasDerivAt (fun s => trainingOutputs f X (θ_traj s) α) (f' α) t := by
    intro α
    exact gradient_flow_generalizedOutput_coord_ode ℓ f X y t hflow α hf hℓ
  have h_step1 := hasDerivAt_generalizedEmpiricalRisk_coord_sum ℓ f X y θ_traj t f' hf' hℓ
  have h_val : (m : ℝ)⁻¹ * (r.ofLp ⬝ᵥ f') =
      -(((m : ℝ) ^ 2)⁻¹) * (r.ofLp ⬝ᵥ (K *ᵥ r.ofLp)) := by
    have h_sum_eq : r.ofLp ⬝ᵥ f' = - (m : ℝ)⁻¹ * (r.ofLp ⬝ᵥ (K *ᵥ r.ofLp)) := by
      have h_row : ∀ α : Fin m, K.row α = K α := fun _ => rfl
      simp only [dotProduct, hf'_def, Matrix.mulVec_apply, h_row, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring_nf
    rw [h_sum_eq]
    ring
  rw [h_val] at h_step1
  exact h_step1

/-- **Geometric and Stability Implications.**
Since `K_t` is positive semidefinite for any parameter state (`empiricalNTKMatrix_quad_form_nonneg`,
`Kernel.lean`), the quadratic form `r(t)ᵀ K_t r(t)` is non-negative, so the empirical risk is
monotonically non-increasing along gradient flow: `∂_t L(θ(t)) ≤ 0`. -/
theorem risk_dissipation_nonpos
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t ∧
      -(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) ≤ 0 := by
  refine ⟨risk_dissipation_identity ℓ f X y t hflow hf hℓ, ?_⟩
  have h_nonneg := empiricalNTKMatrix_quad_form_nonneg f X (θ_traj t)
    (generalizedResidual ℓ f X y (θ_traj t)).ofLp
  have h_sq_nonneg : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
  have h_mul := mul_nonneg h_sq_nonneg h_nonneg
  linarith

/-- **Geometric and Stability Implications (Rayleigh-Ritz Bound).**
If the smallest Rayleigh quotient of `K_t` is bounded below by `lambda_min > 0`
(`lambda_min * ‖v‖² ≤ vᵀ K_t v` for all `v`), the risk dissipation rate is bounded away
from zero whenever `r(t) ≠ 0`:
  `∂_t L(θ(t)) ≤ - (lambda_min / m²) ‖r(t)‖²`. -/
theorem risk_dissipation_le_of_rayleighRitz
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (t : ℝ) (hflow : HasDerivAt θ_traj (-gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)) t)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun v => ℓ v (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t)))
    (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    HasDerivAt (fun s => generalizedEmpiricalRisk ℓ f X y (θ_traj s))
      (-(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t ∧
      -(((m : ℝ) ^ 2)⁻¹) *
        ((generalizedResidual ℓ f X y (θ_traj t)).ofLp ⬝ᵥ
          ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
            (generalizedResidual ℓ f X y (θ_traj t)).ofLp)) ≤
      -(lambda_min / (m : ℝ) ^ 2) * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2 := by
  refine ⟨risk_dissipation_identity ℓ f X y t hflow hf hℓ, ?_⟩
  have h1 := h_rr (generalizedResidual ℓ f X y (θ_traj t))
  have h_sq_nonneg : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 h_sq_nonneg
  have h3 : ((m : ℝ) ^ 2)⁻¹ * (lambda_min * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2) =
      (lambda_min / (m : ℝ) ^ 2) * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2 := by ring
  rw [h3] at h2
  linarith

/-! ### Reusable Analytic Tool: Grönwall Differential Inequality -/

/-- Interval-Restricted Grönwall Decay Lemma:
If a scalar quantity `E(t)` is continuous on `[0, T]`, differentiable on `(0, T)`, and satisfies
`E'(t) ≤ -c * E(t)` there, then `E(t) ≤ E(0) * exp(-c * t)` for all `t ∈ [0, T]`.
Only interior differentiability is needed, so this applies to forward-time trajectories, and the
localized form enables continuous induction bootstrap arguments where the differential inequality
only holds while the state remains inside a bootstrap region. -/
lemma gronwall_exponential_decay_Icc {E E' : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hEc : ContinuousOn E (Set.Icc 0 T)) (hE : ∀ t ∈ Set.Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, E' t ≤ -c * E t) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    E t ≤ E 0 * Real.exp (-c * t) := by
  let g : ℝ → ℝ := fun s => E s * Real.exp (c * s)
  have hg_deriv : ∀ s ∈ Set.Ioo 0 T,
      HasDerivAt g ((E' s + c * E s) * Real.exp (c * s)) s := by
    intro s hs
    have h1 := hE s hs
    have h2 : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
      have hc : HasDerivAt (fun u => c * u) (c * 1) s := (hasDerivAt_id s).const_mul c
      rw [mul_one] at hc
      exact hc.exp
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_cont : ContinuousOn g (Set.Icc 0 T) := hEc.mul (by fun_prop)
  have hg_within : ∀ s ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt g ((E' s + c * E s) * Real.exp (c * s)) (interior (Set.Icc 0 T)) s :=
    fun s hs => (hg_deriv s (by rwa [interior_Icc] at hs)).hasDerivWithinAt
  have hg_nonpos : ∀ s ∈ interior (Set.Icc 0 T), (E' s + c * E s) * Real.exp (c * s) ≤ 0 := by
    intro s hs
    have hle : E' s + c * E s ≤ 0 := by
      linarith [hbound s (by rwa [interior_Icc] at hs)]
    have hexp : 0 ≤ Real.exp (c * s) := (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg hle hexp
  have h_anti : AntitoneOn g (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hg_cont hg_within hg_nonpos
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have h_le := h_anti h0_mem ht ht.1
  dsimp [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (-c * t)).le
  have h_exp_cancel : E t * Real.exp (c * t) * Real.exp (-c * t) = E t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, mul_one]
  rw [h_exp_cancel] at h_mul
  exact h_mul

/-- Grönwall Differential Inequality for Exponential Decay:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` with `c > 0`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ≥ 0`.
Specialization of `gronwall_exponential_decay_Icc` to the interval `[0, t]`. -/
lemma gronwall_exponential_decay {E E' : ℝ → ℝ} {c : ℝ}
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t, E' t ≤ -c * E t) (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ E 0 * Real.exp (-c * t) :=
  gronwall_exponential_decay_Icc ht (fun s _ => (hE s).continuousAt.continuousWithinAt)
    (fun s _ => hE s) (fun s _ => hbound s) t ⟨ht, le_rfl⟩

/-- Mathlib's Grönwall bound is at most `(δ + ε x) e^{K x}` (for `K, ε ≥ 0`), an expression that is
monotone in the time `x ≥ 0` and easy to use for a priori estimates. -/
lemma gronwallBound_le_mul_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hKpos
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    have hexp : 0 < Real.exp (K * x) := Real.exp_pos _
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h2 := Real.one_sub_le_exp_neg (K * x)
      have h3 : Real.exp (K * x) * Real.exp (-(K * x)) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have h4 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ε * x * Real.exp (K * x) := by field_simp
    nlinarith

/-! ### Step-by-Step Proof of Exponential Convergence of Training Loss -/

/-- A positive semidefinite real matrix has a nonnegative quadratic form on `EuclideanSpace`. -/
lemma dotProduct_mulVec_nonneg_of_posSemidef {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) : 0 ≤ v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
  simpa using hA.dotProduct_mulVec_nonneg v.ofLp

/-- The Euclidean inner product `⟪v, A v⟫` equals the quadratic form `vᵀ A v`. -/
lemma inner_toLp_mulVec_eq_dotProduct (A : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    ⟪v, (WithLp.toLp 2 (A *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))⟫ = v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- Step 1 (Time Derivative of Squared Residual Norm under Time-Varying Kernel):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K(t) r(t)`, the rate of change of
`‖r(t)‖²` is given by:
  `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K(t) r(t)`. -/
theorem deriv_norm_sq_timeVarying_ode
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp))) t := by
  have h_inner : HasDerivAt (fun s => ⟪r s, r s⟫)
      (⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ +
       ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp)), r t⟫) t :=
    HasDerivAt.inner ℝ hr hr
  have h_symm : ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp)), r t⟫ =
      ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ := real_inner_comm _ _
  rw [h_symm, ← two_mul] at h_inner
  have h_dot : ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))⟫ =
      -(m : ℝ)⁻¹ * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp)) := by
    rw [show r t = WithLp.toLp 2 (r t).ofLp by rfl]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial]
    rw [smul_dotProduct, dotProduct_comm]
    ring
  rw [h_dot] at h_inner
  have h_norm_sq : (fun s => ‖r s‖ ^ 2) = (fun s => ⟪r s, r s⟫) := by
    ext s
    exact (real_inner_self_eq_norm_sq (r s)).symm
  rw [h_norm_sq]
  convert h_inner using 1
  ring_nf

/-- Step 1 (Time Derivative of Squared Residual Norm - Autonomous Specialization):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K_inf r(t)`:
  `(d / dt) ‖r(t)‖² = - (2 / m) r(t)ᵀ K_inf r(t)`. -/
theorem deriv_norm_sq_linear_ode
    (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t :=
  deriv_norm_sq_timeVarying_ode (fun _ => K_inf) r t hr

/-- Step 2 (Rayleigh-Ritz Lower Bound with Time-Varying Kernel):
When `vᵀ K(t) v ≥ lambda_min ‖v‖²`, the rate of change is bounded:
  `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`. -/
theorem deriv_norm_sq_le_of_rayleighRitz_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp))) t ∧
      -(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K t *ᵥ (r t).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by
  constructor
  · exact deriv_norm_sq_timeVarying_ode K r t hr
  · have h1 := h_rr (r t)
    have hpos : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : (2 / (m : ℝ)) * (lambda_min * ‖r t‖ ^ 2) =
        (2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by ring
    rw [h3] at h2
    linarith

/-- Step 2 (Rayleigh-Ritz Lower Bound Substitution - Autonomous Specialization):
Using the Rayleigh-Ritz condition `vᵀ K_inf v ≥ lambda_min ‖v‖²`:
  `(d / dt) ‖r(t)‖² ≤ - (2 lambda_min / m) ‖r(t)‖²`. -/
theorem deriv_norm_sq_le_of_rayleighRitz
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t ∧
      -(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 :=
  deriv_norm_sq_le_of_rayleighRitz_timeVarying (fun _ => K_inf) lambda_min r t h_rr hr hm

/-- Grönwall Integration for Squared Residual Norm on a Closed Interval `[0, T]`:
Under a Rayleigh quotient lower bound on `K(s)` holding for all `s ∈ [0, T]`, the squared
residual norm decays exponentially:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)` for any `t ∈ [0, T]`.
The residual ODE is only needed on `(0, T)`, with continuity on `[0, T]`. -/
theorem residual_norm_sq_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hE : ∀ s ∈ Set.Ioo 0 T, HasDerivAt (fun u => ‖r u‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp))) s :=
    fun s hs => deriv_norm_sq_timeVarying_ode K r s (hr s hs)
  have hbound : ∀ s ∈ Set.Ioo 0 T,
      -(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp)) ≤
        -(2 * lambda_min / (m : ℝ)) * ‖r s‖ ^ 2 := by
    intro s hs
    exact (deriv_norm_sq_le_of_rayleighRitz_timeVarying K lambda_min r s
      (h_rr s (Set.Ioo_subset_Icc_self hs)) (hr s hs) hm).2
  exact gronwall_exponential_decay_Icc hT (hrc.norm.pow 2) hE hbound t ht

/-- Exponential Decay of Residual Norm on a Closed Interval `[0, T]`:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)` for any `t ∈ [0, T]`. -/
theorem residual_norm_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have h_sq :=
    residual_norm_sq_exponential_decay_timeVarying_Icc K lambda_min T hT r h_rr hrc hr hm t ht
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul (sq_nonneg _)] at h_sqrt
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  have h_exp_sqrt : Real.sqrt (Real.exp (-(2 * lambda_min / (m : ℝ)) * t)) =
      Real.exp (-(lambda_min / (m : ℝ)) * t) := by
    rw [← Real.exp_half]
    congr 1
    ring
  rw [h_exp_sqrt] at h_sqrt
  exact h_sqrt

/-- Step 3 (Grönwall Integration for Squared Residual Norm under Time-Varying Kernel):
Under a uniform-in-time Rayleigh lower bound on `K(t)`:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  residual_norm_sq_exponential_decay_timeVarying_Icc K lambda_min t ht r
    (fun s _ => h_rr s) (fun s _ => (hr s).continuousAt.continuousWithinAt) (fun s _ => hr s) hm t
    ⟨ht, le_rfl⟩

/-- Step 3 (Exponential Decay of Residual Norm under Time-Varying Kernel):
Taking the square root yields:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) :=
  residual_norm_exponential_decay_timeVarying_Icc K lambda_min t ht r
    (fun s _ => h_rr s) (fun s _ => (hr s).continuousAt.continuousWithinAt) (fun s _ => hr s) hm t
    ⟨ht, le_rfl⟩

/-- Step 4 (Exponential Loss Decay under Time-Varying Kernel):
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay_timeVarying
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ t, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have h := residual_norm_sq_exponential_decay_timeVarying K lambda_min h_rr r hr hm t ht
  have hpos : 0 ≤ (2 * (m : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h_mul := mul_le_mul_of_nonneg_left h hpos
  rw [← mul_assoc] at h_mul
  exact h_mul

/-- Step 3 (Grönwall Integration for Squared Residual Norm - Autonomous Specialization):
Integrating the differential inequality yields:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  residual_norm_sq_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

/-- Step 3 (Exponential Decay of Residual Norm - Autonomous Specialization):
Taking the square root gives:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) :=
  residual_norm_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

/-- Step 4 (Exponential Loss Decay - Autonomous Specialization):
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) :=
  mse_loss_exponential_decay_timeVarying (fun _ => K_inf) lambda_min
    (fun _ => h_rr) r hr hm t ht

/-! ### Closed-Form Linear Output Dynamics via Matrix Exponential -/

/-- Initial condition of the explicit matrix exponential residual trajectory:
  `exp(0) r₀ = r₀`. -/
theorem matrix_exp_residual_trajectory_zero
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) :
    (WithLp.toLp 2 ((NormedSpace.exp (-(0 * (m : ℝ)⁻¹) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
  simp

/-- Initial condition of the network prediction trajectory: `f(0) = f₀`. -/
theorem matrix_exp_output_trajectory_zero
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) :
    y + (WithLp.toLp 2 ((NormedSpace.exp (-(0 * (m : ℝ)⁻¹) • K_inf)) *ᵥ (f₀ - y).ofLp) :
      EuclideanSpace ℝ (Fin m)) = f₀ := by
  simp

/-- Relationship between output and residual trajectories under the closed-form matrix exponential
solution: `f(t) - y = r(t)`. -/
theorem matrix_exp_residual_eq_output_sub_y
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    let f_traj : EuclideanSpace ℝ (Fin m) :=
      y + WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)
    let r_traj : EuclideanSpace ℝ (Fin m) :=
      WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)
    f_traj - y = r_traj := by
  intro f_traj r_traj
  dsimp [f_traj, r_traj]
  abel

/-- Auxiliary lemma: evaluation of a constant continuous linear map preserves derivatives. -/
lemma hasDerivAt_clm_apply_const
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : ℝ → E) (u' : E) (x : ℝ) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => L (u y)) (L u') x := by
  have hc : HasDerivAt (fun _ : ℝ => L) (0 : E →L[ℝ] F) x := hasDerivAt_const x L
  have h := hc.clm_apply hu
  simpa using h

/-- Continuous linear map realizing matrix-vector multiplication into `EuclideanSpace`. -/
noncomputable def toEuclideanVecCLM (v : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ →L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  { toLinearMap := {
      toFun := fun M => WithLp.toLp 2 (M *ᵥ v)
      map_add' := fun M N => by
        ext i
        simp [Matrix.add_mulVec]
      map_smul' := fun c M => by
        ext i
        simp [Matrix.smul_mulVec]
    }
    cont := by fun_prop }

private lemma exp_smul_eq (K_inf : Matrix (Fin m) (Fin m) ℝ) (u : ℝ) :
    u • (-(m : ℝ)⁻¹ • K_inf) = -(u / (m : ℝ)) • K_inf := by
  rw [smul_smul]
  congr 1
  ring

private lemma mat_vec_mul_assoc
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    ((-(m : ℝ)⁻¹ • K_inf) * M) *ᵥ v = -(m : ℝ)⁻¹ • (K_inf *ᵥ (M *ᵥ v)) := by
  rw [Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- The closed-form matrix exponential residual trajectory satisfies the linear autonomous ODE:
  `∂_t r(t) = - (1 / m) K_∞ r(t)`. -/
theorem matrix_exp_residual_trajectory_hasDerivAt
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt
      (fun s => (WithLp.toLp 2 ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) t := by
  have h_exp := @hasDerivAt_exp_smul_const' ℝ (Matrix (Fin m) (Fin m) ℝ) _ _ _
    (instCompleteSpaceMatrix m) (-(m : ℝ)⁻¹ • K_inf) t
  have h_clm := hasDerivAt_clm_apply_const (toEuclideanVecCLM r₀.ofLp)
    (fun u => NormedSpace.exp (u • (-(m : ℝ)⁻¹ • K_inf)))
    ((-(m : ℝ)⁻¹ • K_inf) * NormedSpace.exp (t • (-(m : ℝ)⁻¹ • K_inf))) t h_exp
  change HasDerivAt
    (fun y => WithLp.toLp 2 (NormedSpace.exp (y • (-(m : ℝ)⁻¹ • K_inf)) *ᵥ r₀.ofLp))
    (WithLp.toLp 2 (((-(m : ℝ)⁻¹ • K_inf) *
      NormedSpace.exp (t • (-(m : ℝ)⁻¹ • K_inf))) *ᵥ r₀.ofLp)) t at h_clm
  simp_rw [exp_smul_eq K_inf] at h_clm
  rw [mat_vec_mul_assoc K_inf] at h_clm
  exact h_clm

/-- The closed-form network prediction trajectory satisfies the linear output ODE:
  `∂_t f(t) = - (1 / m) K_∞ (f(t) - y)`. -/
theorem matrix_exp_output_trajectory_hasDerivAt
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (y f₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt
      (fun s => y + (WithLp.toLp 2 ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (f₀ - y).ofLp)))) t := by
  have h_res := matrix_exp_residual_trajectory_hasDerivAt K_inf (f₀ - y) t
  exact h_res.const_add y

/-- Exponential norm decay for the closed-form matrix exponential residual trajectory:
  `‖r(t)‖ ≤ ‖r₀‖ exp(- (lambda_min / m) t)`. -/
theorem matrix_exp_residual_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖(WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m))‖ ≤
      ‖r₀‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have hr : ∀ s, HasDerivAt
      (fun u => (WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) s :=
    fun s => matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h_decay := residual_norm_exponential_decay K_inf lambda_min h_rr
    (fun u => WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp))
    hr hm t ht
  have h0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
    have h_zero : -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) := by ring
    rw [h_zero]
    exact matrix_exp_residual_trajectory_zero K_inf r₀
  rw [h0] at h_decay
  exact h_decay

/-- Exponential loss decay for the closed-form matrix exponential trajectory:
  `(1 / 2m) ‖r(t)‖² ≤ ((1 / 2m) ‖r₀‖²) exp(- (2 lambda_min / m) t)`. -/
theorem matrix_exp_loss_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (r₀ : EuclideanSpace ℝ (Fin m)) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖(WithLp.toLp 2
      ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) : EuclideanSpace ℝ (Fin m))‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r₀‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hr : ∀ s, HasDerivAt
      (fun u => (WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
        EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ
        ((NormedSpace.exp (-(s / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp)))) s :=
    fun s => matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h_decay := mse_loss_exponential_decay K_inf lambda_min h_rr
    (fun u => WithLp.toLp 2 ((NormedSpace.exp (-(u / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp))
    hr hm t ht
  have h0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ r₀.ofLp) :
      EuclideanSpace ℝ (Fin m)) = r₀ := by
    have h_zero : -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) := by ring
    rw [h_zero]
    exact matrix_exp_residual_trajectory_zero K_inf r₀
  rw [h0] at h_decay
  exact h_decay

/-! ### Deterministic Lipschitz Propagation for Empirical NTK (Gap 2)

Under parameter displacement `‖θ - θ₀‖`, the variation in the empirical NTK Gram matrix
`K(θ) = J(θ) J(θ)ᵀ` is controlled by the Jacobian operator/Frobenius norm bound `M`
and the Jacobian Lipschitz constant `L_J`:
  `‖K(θ₁) - K(θ₂)‖_F ≤ (2 * M * L_J) * ‖θ₁ - θ₂‖`.
Combined with lazy training displacement `‖θ(t) - θ₀‖ ≤ C / √n`, this establishes the
kernel freeze bound with explicit constant `L_K = 2 * M * L_J`.
-/

/-- Algebraic decomposition of the difference of two Gram matrices:
`A Aᵀ - B Bᵀ = (A - B) Aᵀ + B (A - B)ᵀ`. -/
lemma matrix_mul_transpose_sub_mul_transpose
    (A B : Matrix (Fin m) (Fin P) ℝ) :
    A * Aᵀ - B * Bᵀ = (A - B) * Aᵀ + B * (A - B)ᵀ := by
  rw [Matrix.sub_mul, Matrix.transpose_sub, Matrix.mul_sub, sub_add_sub_cancel]

/-- Frobenius norm bound on the difference of two Gram matrices given an upper bound `M`
on their factors: `‖A Aᵀ - B Bᵀ‖_F ≤ 2 * M * ‖A - B‖_F`. -/
lemma norm_mul_transpose_sub_mul_transpose_le
    (A B : Matrix (Fin m) (Fin P) ℝ) (M : ℝ)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    ‖A * Aᵀ - B * Bᵀ‖ ≤ 2 * M * ‖A - B‖ := by
  rw [matrix_mul_transpose_sub_mul_transpose]
  have h_add := norm_add_le ((A - B) * Aᵀ) (B * (A - B)ᵀ)
  have h_mul1 := Matrix.frobenius_norm_mul (A - B) Aᵀ
  have h_mul2 := Matrix.frobenius_norm_mul B (A - B)ᵀ
  rw [Matrix.frobenius_norm_transpose A] at h_mul1
  rw [Matrix.frobenius_norm_transpose (A - B)] at h_mul2
  have h_term1 : ‖A - B‖ * ‖A‖ ≤ ‖A - B‖ * M :=
    mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  have h_term2 : ‖B‖ * ‖A - B‖ ≤ M * ‖A - B‖ :=
    mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  have h_comb : ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ ≤ 2 * M * ‖A - B‖ := by
    linarith
  linarith

/-- Pointwise algebraic identity for the difference of two empirical NTK Gram matrices. -/
lemma empiricalNTKMatrix_sub_empiricalNTKMatrix
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) :
    empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂ =
      (outputJacobian f X θ₁ - outputJacobian f X θ₂) * (outputJacobian f X θ₁)ᵀ +
      outputJacobian f X θ₂ * (outputJacobian f X θ₁ - outputJacobian f X θ₂)ᵀ := by
  change outputJacobian f X θ₁ * (outputJacobian f X θ₁)ᵀ -
    outputJacobian f X θ₂ * (outputJacobian f X θ₂)ᵀ = _
  exact matrix_mul_transpose_sub_mul_transpose _ _

/-- The distance between two empirical NTK Gram matrices is bounded by `2 * M` times the
distance between their output Jacobians. -/
theorem empiricalNTKMatrix_sub_le_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) (M : ℝ)
    (hJ₁ : ‖outputJacobian f X θ₁‖ ≤ M) (hJ₂ : ‖outputJacobian f X θ₂‖ ≤ M) :
    ‖empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂‖ ≤
      2 * M * ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ := by
  change ‖outputJacobian f X θ₁ * (outputJacobian f X θ₁)ᵀ -
    outputJacobian f X θ₂ * (outputJacobian f X θ₂)ᵀ‖ ≤ _
  exact norm_mul_transpose_sub_mul_transpose_le _ _ M hJ₁ hJ₂

/-- Lipschitz propagation from output Jacobian to empirical NTK Gram matrix:
if the output Jacobian is bounded by `M` and has local Lipschitz constant `L_J`, then
the empirical NTK Gram matrix has local Lipschitz constant `2 * M * L_J`. -/
theorem empiricalNTKMatrix_sub_le_of_jacobian_lipschitz
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) (M L_J : ℝ)
    (hJ₁ : ‖outputJacobian f X θ₁‖ ≤ M) (hJ₂ : ‖outputJacobian f X θ₂‖ ≤ M)
    (hJ_lip : ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ ≤ L_J * ‖θ₁ - θ₂‖) :
    ‖empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂‖ ≤ (2 * M * L_J) * ‖θ₁ - θ₂‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₁
  have h1 := empiricalNTKMatrix_sub_le_of_jacobian_bound f X θ₁ θ₂ M hJ₁ hJ₂
  have h2 : 2 * M * ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ ≤
      2 * M * (L_J * ‖θ₁ - θ₂‖) := by
    have h2M : 0 ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_left hJ_lip h2M
  have h3 : 2 * M * (L_J * ‖θ₁ - θ₂‖) = (2 * M * L_J) * ‖θ₁ - θ₂‖ := by ring
  rw [h3] at h2
  exact h1.trans h2

/-- Deterministic Lipschitz propagation (Gap 2 deliverable):
On any set `S` containing `θ₀`, if `‖outputJacobian f X θ‖ ≤ M` and
`‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖` for all `θ ∈ S`,
then `‖empiricalNTKMatrix f X θ - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * ‖θ - θ₀‖`. -/
theorem empiricalNTKMatrix_lipschitz_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (S : Set (EuclideanSpace ℝ (Fin P))) (θ₀ : EuclideanSpace ℝ (Fin P)) (hθ₀ : θ₀ ∈ S)
    (M L_J : ℝ)
    (hJ_bdd : ∀ θ ∈ S, ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ ∈ S, ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    {θ : EuclideanSpace ℝ (Fin P)} (hθ : θ ∈ S) :
    ‖empiricalNTKMatrix f X θ - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * ‖θ - θ₀‖ :=
  empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X θ θ₀ M L_J
    (hJ_bdd θ hθ) (hJ_bdd θ₀ hθ₀) (hJ_lip θ hθ)

/-! ### Second-Order Taylor Bound for the Training Outputs

If the output Jacobian is Lipschitz near `θ₀`, the outputs are approximated by their
linearization `f(θ₀) + J(θ₀) (θ - θ₀)` up to a quadratic remainder. This is the deterministic
half of the "lazy training" statement that the *nonlinear* network stays close to its
initialization linearization; it only needs a Lipschitz Jacobian, not twice differentiability. -/

/-- **`C^{1,1}` Taylor bound (first-order remainder under a Lipschitz derivative).** Let `G : E → F`
be Fréchet differentiable with derivative `G' z` at every `z` in the closed ball of radius `r`
around `x₀`, and suppose `‖G' z - G' x₀‖ ≤ L ‖z - x₀‖` there. Then for `‖x - x₀‖ ≤ r`,
`‖G x - G x₀ - G' x₀ (x - x₀)‖ ≤ (L / 2) ‖x - x₀‖²`. Mathlib's Taylor theorems need `n + 1` times
continuous differentiability (`taylor_mean_remainder_bound`); this only needs a Lipschitz derivative
and keeps the sharp constant `1 / 2`. The proof applies
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` on `[0, 1]` to `s ↦ G (x₀ + s (x - x₀)) - ...`
with boundary `L ‖x - x₀‖² s² / 2`. -/
theorem norm_sub_sub_fderiv_le_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : E → F} {G' : E → E →L[ℝ] F} {x₀ x : E} {r L : ℝ}
    (hd : ∀ z, ‖z - x₀‖ ≤ r → HasFDerivAt G (G' z) z)
    (hlip : ∀ z, ‖z - x₀‖ ≤ r → ‖G' z - G' x₀‖ ≤ L * ‖z - x₀‖) (hx : ‖x - x₀‖ ≤ r) :
    ‖G x - G x₀ - G' x₀ (x - x₀)‖ ≤ L / 2 * ‖x - x₀‖ ^ 2 := by
  set Δ := x - x₀ with hΔ
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖x₀ + s • Δ - x₀‖ ≤ r := fun s hs => by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hx
  set g : ℝ → F := fun s => G (x₀ + s • Δ) - G x₀ - s • G' x₀ Δ with hg
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g ((G' (x₀ + s • Δ) - G' x₀) Δ) s := by
    intro s hs
    have hline : HasDerivAt (fun u : ℝ => x₀ + u • Δ) Δ s := by
      simpa using ((hasDerivAt_id s).smul_const Δ).const_add x₀
    have h1 := (hd _ (hseg s hs)).comp_hasDerivAt s hline
    have h2 := (h1.sub_const (G x₀)).sub ((hasDerivAt_id s).smul_const (G' x₀ Δ))
    refine h2.congr_deriv ?_
    simp
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (a := 0) (b := 1) (B := fun s => L * ‖Δ‖ ^ 2 * s ^ 2 / 2)
    (B' := fun s => L * ‖Δ‖ ^ 2 * s)
    (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (by simp [hg])
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul (L * ‖Δ‖ ^ 2)).div_const 2
      convert this using 1
      push_cast
      ring)
    (fun s hs => by
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      calc ‖(G' (x₀ + s • Δ) - G' x₀) Δ‖
          ≤ ‖G' (x₀ + s • Δ) - G' x₀‖ * ‖Δ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖s • Δ‖) * ‖Δ‖ := by
            gcongr
            simpa using hlip _ (hseg s hs')
        _ = L * ‖Δ‖ ^ 2 * s := by
            rw [norm_smul, Real.norm_of_nonneg hs.1]; ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have hθΔ : x₀ + Δ = x := by rw [hΔ]; abel
  simp only [hg, one_smul, hθΔ] at hbound
  linarith

/-- The matrix `M` as a continuous linear map between Euclidean spaces (`v ↦ M v`). -/
noncomputable def matrixCLM {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin a) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 M)

lemma matrixCLM_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : EuclideanSpace ℝ (Fin b)) :
    matrixCLM M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  simp [matrixCLM, Matrix.toLpLin_apply]

lemma matrixCLM_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) :
    matrixCLM M - matrixCLM N = matrixCLM (M - N) := by
  ext v : 1
  simp [matrixCLM_apply, Matrix.sub_mulVec]

lemma norm_matrixCLM_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ‖matrixCLM M‖ ≤ ‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    rw [matrixCLM_apply]; exact mulVec_frobenius_norm_le M v

/-- **Second-order Taylor bound for the training outputs under a Lipschitz Jacobian.** If the output
Jacobian is `L`-Lipschitz at `θ₀` on the closed ball of radius `r` around `θ₀`
(`‖J θ - J θ₀‖ ≤ L ‖θ - θ₀‖`, Frobenius norm) and each output is differentiable there, then for
`‖θ - θ₀‖ ≤ r`
`‖f(θ) - f(θ₀) - J(θ₀) (θ - θ₀)‖ ≤ (L / 2) ‖θ - θ₀‖²`. This is
`norm_sub_sub_fderiv_le_of_lipschitz_fderiv` for `G = trainingOutputs`, with `G' z` the linear map
`v ↦ J(z) v` (its operator norm is at most the Frobenius norm, `mulVec_frobenius_norm_le`). -/
theorem norm_trainingOutputs_sub_linearization_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (θ₀ : EuclideanSpace ℝ (Fin P)) (r L : ℝ)
    (hdiff : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => f (X β) θ') θ)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L * ‖θ - θ₀‖)
    {θ : EuclideanSpace ℝ (Fin P)} (hθ : ‖θ - θ₀‖ ≤ r) :
    ‖trainingOutputs f X θ - trainingOutputs f X θ₀ -
        WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ (θ - θ₀).ofLp)‖ ≤ L / 2 * ‖θ - θ₀‖ ^ 2 := by
  have h := norm_sub_sub_fderiv_le_of_lipschitz_fderiv (G := trainingOutputs f X)
    (G' := fun z => matrixCLM (outputJacobian f X z)) (x₀ := θ₀) (x := θ) (r := r) (L := L)
    (fun z hz => by
      rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
      intro α
      rw [hasFDerivWithinAt_univ]
      have h := (hdiff z hz α).hasGradientAt.hasFDerivAt
      have hcl : PiLp.proj 2 (fun _ : Fin m => ℝ) α ∘SL matrixCLM (outputJacobian f X z) =
          InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
            (gradient (fun θ' => f (X α) θ') z) := by
        ext v
        rw [InnerProductSpace.toDual_apply_apply]
        simp only [ContinuousLinearMap.comp_apply, matrixCLM_apply, PiLp.proj_apply,
          Matrix.mulVec_apply, dotProduct, outputJacobian, tangentFeature, PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
      exact h.congr_fderiv hcl.symm)
    (fun z hz => by
      rw [matrixCLM_sub]; exact (norm_matrixCLM_le _).trans (hJ_lip z hz)) hθ
  simpa [matrixCLM_apply] using h

/-! ### Reusable Analytic Tool: Quadratic Form Perturbation and Rayleigh-Quotient Stability

If two matrices are close in Frobenius norm, their quadratic forms are close, and consequently a
Rayleigh-quotient lower bound established at one matrix propagates - with a correspondingly
weaker constant - to any matrix within that Frobenius distance. This is Gap 5's Step 2: it shows
the spectral-gap hypothesis assumed at initialization `θ₀` continues to hold, with a degraded but
still positive constant, at any `θ` close enough to `θ₀` in parameter space - exactly what the
Gap 5 bootstrap needs to keep re-deriving a uniform-in-time Rayleigh bound along the trajectory.
-/

/-- The quadratic forms of two matrices differ by at most their Frobenius distance times `‖v‖²`:
  `|vᵀ A v - vᵀ B v| ≤ ‖A - B‖ ‖v‖²`. -/
theorem abs_dotProduct_mulVec_sub_le (A B : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    |v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) - v.ofLp ⬝ᵥ (B *ᵥ v.ofLp)| ≤ ‖A - B‖ * ‖v‖ ^ 2 := by
  have heq : v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) - v.ofLp ⬝ᵥ (B *ᵥ v.ofLp) =
      v.ofLp ⬝ᵥ ((A - B) *ᵥ v.ofLp) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [heq]
  rw [← inner_toLp_mulVec_eq_dotProduct]
  calc
    |⟪v, (WithLp.toLp 2 ((A - B) *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))⟫| ≤
        ‖v‖ * ‖(WithLp.toLp 2 ((A - B) *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A - B‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (mulVec_frobenius_norm_le (A - B) v) (norm_nonneg _)
    _ = ‖A - B‖ * ‖v‖ ^ 2 := by ring

/-- A shifted positive semidefinite matrix `K - lambda_min • 1` satisfies the Rayleigh quotient
lower bound `lambda_min * ‖v‖² ≤ vᵀ K v` for all `v`. -/
theorem rayleigh_lower_bound_of_sub_smul_posSemidef
    {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (hK : (K - lambda_min • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) :
    lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K *ᵥ v.ofLp) := by
  have h_nonneg := Matrix.PosSemidef.dotProduct_mulVec_nonneg hK v.ofLp
  rw [star_trivial] at h_nonneg
  have h_mul : (K - lambda_min • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ v.ofLp =
      K *ᵥ v.ofLp - lambda_min • v.ofLp := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h_mul, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h_nonneg
  have h_norm : v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
    rw [dotProduct, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq (v.ofLp i)).symm
  rw [h_norm] at h_nonneg
  linarith

/-- Rayleigh-quotient stability under a matrix distance bound: if `K₀`'s Rayleigh quotient is
bounded below by `lambda_min₀` and `‖K - K₀‖ ≤ ε`, then `K`'s Rayleigh quotient is bounded below
by `lambda_min₀ - ε`. -/
theorem rayleigh_quotient_lower_bound_of_matrix_dist
    (K K₀ : Matrix (Fin m) (Fin m) ℝ) (lambda_min₀ ε : ℝ)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K₀ *ᵥ v.ofLp))
    (hK_dist : ‖K - K₀‖ ≤ ε) (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_min₀ - ε) * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K *ᵥ v.ofLp) := by
  have h1 := h_rr₀ v
  have h2 := (abs_le.mp (abs_dotProduct_mulVec_sub_le K K₀ v)).1
  have h3 : ‖K - K₀‖ * ‖v‖ ^ 2 ≤ ε * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hK_dist (sq_nonneg _)
  nlinarith [h1, h2, h3]

/-- Rayleigh-quotient stability of the empirical NTK Gram matrix under parameter displacement:
if `θ₀`'s empirical NTK matrix has Rayleigh quotient bounded below by `lambda_min₀`, and the
output Jacobian is `M`-bounded at both `θ` and `θ₀` and `L_J`-Lipschitz between them, then `θ`'s
empirical NTK matrix has Rayleigh quotient bounded below by
`lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖`. This is Gap 5's Step 2, connecting Gap 2's Lipschitz
propagation directly to the spectral-gap hypothesis the Gap 5 bootstrap needs at each `θ`. -/
theorem rayleigh_quotient_lower_bound_of_displacement
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₀ θ : EuclideanSpace ℝ (Fin P)) (M L_J lambda_min₀ : ℝ)
    (hJ₀ : ‖outputJacobian f X θ₀‖ ≤ M) (hJ : ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v.ofLp) :=
  rayleigh_quotient_lower_bound_of_matrix_dist (empiricalNTKMatrix f X θ)
    (empiricalNTKMatrix f X θ₀) lambda_min₀ ((2 * M * L_J) * ‖θ - θ₀‖) h_rr₀
    (empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X θ θ₀ M L_J hJ hJ₀ hJ_lip) v

/-! ### Gap 5, Step 1: The Displacement-Integral Bound

Given that a uniform-in-time Rayleigh-quotient lower bound holds on `[0, T]`, gradient flow's
instantaneous speed `‖∂_t θ(t)‖ = ‖∇_θ L(θ(t))‖` decays exponentially (Step 1's gradient-speed
bound, `Kernel.lean`'s `gradient_mseLoss_norm_le`, combined with Step 1's time-varying residual
decay), and integrating this speed bound over `[0, T]` gives an explicit, `T`-independent cap on
how far gradient flow can have moved from `θ₀` by time `T`. -/

/-- Reusable bound: `∫₀ᵀ exp(-c t) dt ≤ 1/c` for `c > 0`, dropping the (nonnegative) `1 - exp(-cT)`
factor from the exact closed form `(1 - exp(-cT))/c`. -/
lemma integral_exp_neg_le (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, Real.exp (-c * t) ≤ c⁻¹ := by
  have hc' : -c ≠ 0 := by linarith
  rw [show (fun t : ℝ => Real.exp (-c * t)) = (fun t => Real.exp ((-c) * t)) from rfl]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hc']
  rw [integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  have h1 : Real.exp (-c * T) - 1 ≤ 0 := by
    have := Real.exp_le_one_iff.mpr (by nlinarith : -c * T ≤ 0)
    linarith
  rw [show (-c)⁻¹ * (Real.exp (-c * T) - 1) = c⁻¹ * (1 - Real.exp (-c * T)) by
    field_simp; ring]
  have h3 : 0 ≤ c⁻¹ := by positivity
  calc
    c⁻¹ * (1 - Real.exp (-c * T)) ≤ c⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ h3
      linarith [Real.exp_nonneg (-c * T)]
    _ = c⁻¹ := by ring

section CoordinateBlocks

variable {κ ι' : Type*} [Fintype κ] [Fintype ι']

/-- The coordinate restriction `v ↦ (v (k o))_{o : κ}` along an enumeration `k : κ → ι'` of some
coordinates, as a continuous linear map between Euclidean spaces. -/
noncomputable def restrictCoords (k : κ → ι') :
    EuclideanSpace ℝ ι' →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun o => v (k o)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma restrictCoords_apply (k : κ → ι') (v : EuclideanSpace ℝ ι') (o : κ) :
    restrictCoords k v o = v (k o) := rfl

lemma norm_sq_restrictCoords (k : κ → ι') (v : EuclideanSpace ℝ ι') :
    ‖restrictCoords k v‖ ^ 2 = ∑ o : κ, v (k o) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; rfl

/-- Cauchy–Schwarz for a block of coordinates of `Jᵀ r`. -/
lemma sum_sq_mulVec_transpose_le (r : Fin m → ℝ) (J : Fin m → κ → ℝ) :
    ∑ o : κ, (∑ α : Fin m, r α * J α o) ^ 2 ≤
      (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, ∑ o : κ, J α o ^ 2 := by
  calc ∑ o : κ, (∑ α : Fin m, r α * J α o) ^ 2
      ≤ ∑ o : κ, (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, J α o ^ 2 :=
        Finset.sum_le_sum fun o _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ α : Fin m, r α ^ 2) * ∑ α : Fin m, ∑ o : κ, J α o ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-- **Speed of a block of coordinates under MSE gradient flow.** -/
theorem norm_restrictCoords_gradient_mseLoss_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) (k : κ → Fin P) :
    ‖restrictCoords k (gradient (mseLoss f X y) θ)‖ ≤
      (m : ℝ)⁻¹ * Real.sqrt (∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) *
        ‖trainingResidual f X y θ‖ := by
  have hcoord : ∀ o : κ, gradient (mseLoss f X y) θ (k o) =
      (m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual f X y θ α * outputJacobian f X θ α (k o) := by
    intro o
    rw [gradient_mseLoss_apply_j f X y θ hdiff (k o), Matrix.mulVec_apply, dotProduct]
    congr 1
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have hsq : ‖restrictCoords k (gradient (mseLoss f X y) θ)‖ ^ 2 ≤
      ((m : ℝ)⁻¹ * Real.sqrt (∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) *
        ‖trainingResidual f X y θ‖) ^ 2 := by
    rw [norm_sq_restrictCoords]
    simp_rw [hcoord, mul_pow, ← Finset.mul_sum]
    have hres : ‖trainingResidual f X y θ‖ ^ 2 = ∑ α : Fin m, trainingResidual f X y θ α ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have hJnn : 0 ≤ ∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.sq_sqrt hJnn, hres]
    calc (m : ℝ)⁻¹ ^ 2 * ∑ o : κ, (∑ α : Fin m, trainingResidual f X y θ α *
            outputJacobian f X θ α (k o)) ^ 2
        ≤ (m : ℝ)⁻¹ ^ 2 * ((∑ α : Fin m, trainingResidual f X y θ α ^ 2) *
            ∑ α : Fin m, ∑ o : κ, outputJacobian f X θ α (k o) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_sq_mulVec_transpose_le _ _) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

end CoordinateBlocks

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Displacement of a linear image of a forward gradient flow.** If the image under `Lin` of the
gradient at time `t` has norm at most `B t` on `[0, T]`, then `Lin (w T - w₀)` has norm at most
`∫₀ᵀ B`. Only the ODE for positive times and continuity on `[0, ∞)` are used. -/
theorem norm_map_sub_le_integral_of_forwardGF {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hflow : ForwardGFTrajectory f w₀ w) (Lin : E →L[ℝ] F) {T : ℝ} (hT : 0 ≤ T) {B : ℝ → ℝ}
    (hB : ∀ t ∈ Set.Icc 0 T, ‖Lin (gradient f (w t))‖ ≤ B t)
    (hBi : IntervalIntegrable B volume 0 T) :
    ‖Lin (w T - w₀)‖ ≤ ∫ t in (0 : ℝ)..T, B t := by
  have hd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => Lin (w s)) (Lin (-gradient f (w t))) t := fun t ht =>
    Lin.hasFDerivAt.comp_hasDerivAt t (hflow.ode t ht)
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun s => Lin (w s)) hT
    (Lin.continuous.comp_continuousOn (hflow.continuousOn.mono Set.Icc_subset_Ici_self))
    (fun t ht => (hd t ht.1).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun t ht => by
      rw [(hd t ht.1).deriv, map_neg, norm_neg]
      exact hB t (Set.mem_Icc_of_Ioo ht)) hBi
  simpa [hflow.init, map_sub] using hmain

end

/-- **The MSE loss does not increase along a local gradient-flow solution.** If `θ` solves
`θ' = -∇L(θ)` on `[0, S]` (one-sided at the endpoints), then `L(θ(t)) ≤ L(θ(0))` there. Unlike
`ConvexOpt.gf_monotone_decrease` this needs neither a global trajectory nor differentiability of `L`
away from the curve. -/
lemma mseLoss_le_of_hasDerivWithinAt_neg_gradient (f : ι → EuclideanSpace ℝ (Fin P) → ℝ)
    (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m)) {θ : ℝ → EuclideanSpace ℝ (Fin P)} {S : ℝ}
    (hdiff : ∀ t ∈ Set.Icc 0 S, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ t))
    (hθ : ∀ t ∈ Set.Icc 0 S,
      HasDerivWithinAt θ (-gradient (mseLoss f X y) (θ t)) (Set.Icc 0 S) t) :
    ∀ t ∈ Set.Icc 0 S, mseLoss f X y (θ t) ≤ mseLoss f X y (θ 0) := by
  have hd : ∀ t ∈ Set.Icc 0 S, HasDerivWithinAt (fun s => mseLoss f X y (θ s))
      (-‖gradient (mseLoss f X y) (θ t)‖ ^ 2) (Set.Icc 0 S) t := by
    intro t ht
    have hg := (hasGradientAt_mseLoss f X y (θ t) (hdiff t ht)).differentiableAt.hasGradientAt
    have h2 := hg.hasFDerivAt.comp_hasDerivWithinAt t (hθ t ht)
    rwa [InnerProductSpace.toDual_apply_apply, inner_neg_right, real_inner_self_eq_norm_sq] at h2
  have hanti : AntitoneOn (fun s => mseLoss f X y (θ s)) (Set.Icc 0 S) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S)
      (fun t ht => (hd t ht).continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).mono interior_subset) (fun t ht => ?_)
    have := neg_nonpos.2 (sq_nonneg ‖gradient (mseLoss f X y) (θ t)‖)
    exact this
  intro t ht
  exact hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- The training residual along a curve is continuous on any set where the curve is continuous and
every output is differentiable at the curve. -/
lemma continuousOn_trainingResidual_comp (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) {θ : ℝ → EuclideanSpace ℝ (Fin P)} {s : Set ℝ}
    (hθ : ContinuousOn θ s)
    (hdiff : ∀ t ∈ s, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ t)) :
    ContinuousOn (fun t => trainingResidual f X y (θ t)) s := by
  intro t ht
  have hcoord : ∀ β : Fin m, ContinuousWithinAt (fun t => f (X β) (θ t) - y β) s t := fun β =>
    ((hdiff t ht β).continuousAt.comp_continuousWithinAt (hθ t ht)).sub continuousWithinAt_const
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).continuousAt.comp_continuousWithinAt
    (continuousWithinAt_pi.2 hcoord)

/-- **Displacement is at most the integral of the speed bound.** If the Rayleigh quotient of the
empirical NTK along the trajectory is bounded below by `lambda_min` (any real, in particular `0`
under positive semidefiniteness) and the output Jacobian is `M`-bounded on `[0, T]`, then
`‖θ(T) - θ₀‖ ≤ ∫₀ᵀ (M / m) ‖r₀‖ exp(-(lambda_min / m) t) dt`. Both the gap and the no-gap
displacement bounds are corollaries. -/
theorem displacement_le_integral_of_rayleigh
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M lambda_min : ℝ)
    (hm : 0 < (m : ℝ))
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (h_rr : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    ‖θ_traj T - θ₀‖ ≤ ∫ t in (0:ℝ)..T,
      (m : ℝ)⁻¹ * M * (‖trainingResidual f X y θ₀‖ *
        Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
  set r₀ : ℝ := ‖trainingResidual f X y θ₀‖ with hr₀_def
  have hr_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        (trainingResidual f X y (θ_traj t)).ofLp))) t :=
    fun t ht => gradient_flow_residual_vector_ode f X y t (hflow.ode t ht.1) (hdiff t)
  have hrc := continuousOn_trainingResidual_comp f X y (s := Set.Icc 0 T)
    (hflow.continuousOn.mono Set.Icc_subset_Ici_self) (fun t _ => hdiff t)
  have hres_decay := residual_norm_exponential_decay_timeVarying_Icc
    (fun t => empiricalNTKMatrix f X (θ_traj t)) lambda_min T hT
    (fun s => trainingResidual f X y (θ_traj s)) h_rr hrc hr_ode hm
  have h0 : trainingResidual f X y (θ_traj 0) = trainingResidual f X y θ₀ := by
    rw [hflow.init]
  have hspeed : ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖gradient (mseLoss f X y) (θ_traj t)‖ ≤
        (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
    intro t ht
    have h1 := gradient_mseLoss_norm_le f X y (θ_traj t) (hdiff t)
    have h2 := hres_decay t ht
    rw [h0] at h2
    calc
      ‖gradient (mseLoss f X y) (θ_traj t)‖ ≤
          (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ * ‖trainingResidual f X y (θ_traj t)‖ := h1
      _ ≤ (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
        have hMnn : 0 ≤ M := (norm_nonneg _).trans (hJ_bdd t ht)
        have hstep1 : ‖trainingResidual f X y (θ_traj t)‖ ≤
            r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t) := h2
        have hstep2 : (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ ≤ (m : ℝ)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hJ_bdd t ht) (by positivity)
        calc
          (m : ℝ)⁻¹ * ‖outputJacobian f X (θ_traj t)‖ * ‖trainingResidual f X y (θ_traj t)‖ ≤
              ((m : ℝ)⁻¹ * M) * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
            apply mul_le_mul hstep2 hstep1 (norm_nonneg _)
            positivity
          _ = (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by ring
  have hBcont : Continuous
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t))) := by
    fun_prop
  have hBi : IntervalIntegrable
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)))
      MeasureTheory.volume 0 T :=
    hBcont.intervalIntegrable 0 T
  simpa using norm_map_sub_le_integral_of_forwardGF hflow
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin P))) hT hspeed hBi

/-- Gap 5 Step 1 deliverable: if the empirical NTK's Rayleigh quotient along the trajectory is
bounded below by `lambda_min` throughout `[0, T]`, and the output Jacobian is `M`-bounded there
too, then gradient flow has moved by at most `(M * ‖r₀‖) / lambda_min` from `θ₀` by time `T` -
a bound with **no explicit dependence on `T`**, since the residual's exponential decay makes the
total distance traveled converge. -/
theorem displacement_integral_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M lambda_min : ℝ) (hm : 0 < (m : ℝ)) (hlam : 0 < lambda_min)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (h_rr : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) :
    ‖θ_traj T - θ₀‖ ≤ (M * ‖trainingResidual f X y θ₀‖) / lambda_min := by
  have hmain := displacement_le_integral_of_rayleigh f X y hflow T hT M lambda_min hm hdiff
    hJ_bdd h_rr
  set r₀ : ℝ := ‖trainingResidual f X y θ₀‖ with hr₀_def
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hJ_bdd 0 ⟨le_refl 0, hT⟩)
  have hr0nn : 0 ≤ r₀ := norm_nonneg _
  have hintbound : ∫ t in (0:ℝ)..T,
      (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) ≤
      (M * r₀) / lambda_min := by
    rw [show (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t))) =
        (fun t : ℝ => ((m : ℝ)⁻¹ * M * r₀) * Real.exp (-(lambda_min / (m : ℝ)) * t)) from
        funext fun t => by ring]
    rw [intervalIntegral.integral_const_mul]
    have hc : 0 < lambda_min / (m : ℝ) := by positivity
    have hbound := integral_exp_neg_le (lambda_min / (m : ℝ)) T hc hT
    have hcoeff_nn : 0 ≤ (m : ℝ)⁻¹ * M * r₀ := by positivity
    calc
      ((m : ℝ)⁻¹ * M * r₀) * ∫ t in (0:ℝ)..T, Real.exp (-(lambda_min / (m : ℝ)) * t) ≤
          ((m : ℝ)⁻¹ * M * r₀) * (lambda_min / (m : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hbound hcoeff_nn
      _ = (M * r₀) / lambda_min := by
        field_simp
  calc
    ‖θ_traj T - θ₀‖ ≤ ∫ t in (0:ℝ)..T,
        (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := hmain
    _ ≤ (M * r₀) / lambda_min := hintbound


/-- **Displacement bound on a finite horizon, with no spectral gap.** Positive semidefiniteness of
the empirical NTK alone makes the residual norm nonincreasing, so if the output Jacobian is
`M`-bounded on `[0, T]` then `‖θ(T) - θ₀‖ ≤ T * M * ‖r₀‖ / m`. The bound grows linearly in `T`, as
it must without a gap. -/
theorem displacement_bound_of_psd
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (T : ℝ) (hT : 0 ≤ T) (M : ℝ) (hm : 0 < (m : ℝ))
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hJ_bdd : ∀ t ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj t)‖ ≤ M) :
    ‖θ_traj T - θ₀‖ ≤ T * M * ‖trainingResidual f X y θ₀‖ / m := by
  have h := displacement_le_integral_of_rayleigh f X y hflow T hT M 0 hm hdiff hJ_bdd
    fun t _ v => by
      simpa using dotProduct_mulVec_nonneg_of_posSemidef
        (empiricalNTKMatrix_posSemidef f X (θ_traj t)) v
  simp only [zero_div, neg_zero, zero_mul, Real.exp_zero, mul_one,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  calc ‖θ_traj T - θ₀‖ ≤ T * ((m : ℝ)⁻¹ * M * ‖trainingResidual f X y θ₀‖) := h
    _ = T * M * ‖trainingResidual f X y θ₀‖ / m := by ring

/-! ### Gap 5, Step 2: The Continuous-Induction Bootstrap

The Rayleigh-quotient lower bound used by `displacement_integral_bound` is only known to hold
while gradient flow stays within a ball around `θ₀` (Rayleigh-quotient stability, above). This
section closes the circularity: `displacement_integral_bound` shows that *while inside* a ball
of radius `r`, the trajectory in fact stays within the strictly smaller radius `C < r` - which,
by continuity, means it can never actually reach the boundary `r` in the first place. This is
formalized as a proof by contradiction using the infimum of the (assumed nonempty) set of "escape
times", ruling out escape entirely and discharging `hlazy` with the tight constant `C`. -/

/-- **Rayleigh lower bound on a ball.** If the Jacobian is `M`-bounded and `L_J`-Lipschitz (relative
to `θ₀`) on the closed ball of radius `r`, the initial Rayleigh quotient is at least `lambda_min₀`,
and `2 * M * L_J * r ≤ lambda_min₀ / 2`, then every `θ` in the ball has Rayleigh quotient at least
`lambda_min₀ / 2`. -/
theorem rayleigh_lower_bound_on_ball
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    {θ₀ : EuclideanSpace ℝ (Fin P)} (M L_J lambda_min₀ r : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (hr_nonneg : 0 ≤ r) (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v.ofLp) := by
  intro θ hθ v
  have hstep := rayleigh_quotient_lower_bound_of_displacement f X θ₀ θ M L_J lambda_min₀
    (hJ_bdd θ₀ (by simpa using hr_nonneg)) (hJ_bdd θ hθ) (hJ_lip θ hθ) h_rr₀ v
  have h2ML_J_nonneg : 0 ≤ 2 * M * L_J := by positivity
  have hCbound : 2 * M * L_J * ‖θ - θ₀‖ ≤ lambda_min₀ / 2 :=
    (mul_le_mul_of_nonneg_left hθ h2ML_J_nonneg).trans h_ball_gap
  have hge : lambda_min₀ - 2 * M * L_J * ‖θ - θ₀‖ ≥ lambda_min₀ / 2 := by linarith
  nlinarith [hstep, mul_le_mul_of_nonneg_right hge (sq_nonneg ‖v‖)]

/-- **Continuous-induction (bootstrap) principle on `[0, T]`.** Let `d` be continuous and
`C < r` (only continuity on `[0, T]` is needed). Suppose that whenever `d ≤ r` holds on all of
`[0, S]` (for `S ∈ [0, T]`), the sharper
bound `d S ≤ C` holds. Then `d ≤ C` on all of `[0, T]`, i.e. `d` can never reach the threshold
`r`. Used for the displacement bootstraps: `d t = ‖θ(t) - θ₀‖` while the Jacobian estimates only
hold inside a ball. -/
theorem le_of_forall_bootstrap {d : ℝ → ℝ} {r C T : ℝ} (hd : ContinuousOn d (Set.Icc 0 T))
    (hCr : C < r)
    (hT : 0 ≤ T) (h0 : d 0 ≤ r)
    (hstep : ∀ S ∈ Set.Icc (0 : ℝ) T, (∀ t ∈ Set.Icc (0 : ℝ) S, d t ≤ r) → d S ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ C := by
  have hzero : d 0 ≤ C := hstep 0 ⟨le_rfl, hT⟩ fun t ht => by
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    exact h0
  have hclosed : IsClosed ({t : ℝ | d t ≤ C} ∩ Set.Icc 0 T) := by
    have := hd.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := C))
    rwa [Set.inter_comm] at this
  have h := IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
    (s := {t : ℝ | d t ≤ C}) (a := 0) (b := T) hclosed hzero (fun t ht hsub => ?_)
  · exact fun t htT => h htT
  have hdt : d t < r := (hsub ⟨ht.1, le_rfl⟩).trans_lt hCr
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hd t ⟨ht.1, ht.2.le⟩) (r - d t)
    (by linarith)
  have hδ' : 0 < min δ (T - t) := lt_min hδ (by linarith [ht.2])
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show t < t + min δ (T - t) by linarith)) ?_
  intro u hu
  have huT : u ≤ T := by linarith [hu.2, min_le_right δ (T - t)]
  refine hstep u ⟨by linarith [ht.1, hu.1], huT⟩ fun t' ht' => ?_
  by_cases hle : t' ≤ t
  · exact (hsub ⟨ht'.1, hle⟩).trans hCr.le
  · have hlt : t < t' := not_le.1 hle
    have hdist : dist t' t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [ht'.2, hu.2, min_le_left δ (T - t)]
    have hlt' := hball ⟨by linarith [ht'.1], by linarith [ht'.2, hu.2, huT]⟩ hdist
    rw [Real.dist_eq] at hlt'
    linarith [(abs_lt.1 hlt').2]

/-- **Gap 5 deliverable.** Given a base spectral-gap hypothesis `lambda_min₀` at `θ₀`, a Jacobian
bound `M` and Lipschitz constant `L_J` that hold on the closed ball `‖θ - θ₀‖ ≤ r` (not globally -
matching how `empiricalNTKMatrix_lipschitz_of_jacobian_bound`, Gap 2, is already stated over an
arbitrary set `S`; concentration bounds like Gap 3/4's are inherently local to a neighborhood of
`θ₀`, not uniform over the whole parameter space), and a radius `r` strictly larger than the
target displacement bound `C` chosen so that `r` itself keeps the Rayleigh quotient above
`lambda_min₀/2` (`h_ball_gap`) and `C` dominates the resulting displacement bound (`hC_ge`),
gradient flow never moves more than `C` from `θ₀`, for any `t ≥ 0`. This discharges
`lazy_training_kernel_freeze_bound`'s `hlazy` hypothesis with a **width-independent** `C` - see
`docs/NTK_lazy_training_gap_closure_plan.md` §3.1 for why the `1/√n` decay belongs on `L_J`,
not here. -/
theorem lazy_training_displacement_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (M L_J lambda_min₀ r C : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r)
    (hCr : C < r)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual f X y θ₀‖ / (lambda_min₀ / 2) ≤ C)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ T : ℝ, 0 ≤ T → ‖θ_traj T - θ₀‖ ≤ C := by
  set lambda_min : ℝ := lambda_min₀ / 2 with hlm_def
  have hlambda_pos : 0 < lambda_min := by positivity
  have h_rr_ball := rayleigh_lower_bound_on_ball f X M L_J lambda_min₀ r hM hL_J hr_nonneg
    h_ball_gap h_rr₀ hJ_bdd hJ_lip
  -- Core claim: if the trajectory has stayed in the closed ball `[0, S]` for some `S`, its
  -- displacement at `S` is in fact bounded by the tighter constant `C`.
  have hcore : ∀ S : ℝ, 0 ≤ S → (∀ t ∈ Set.Icc (0:ℝ) S, ‖θ_traj t - θ₀‖ ≤ r) →
      ‖θ_traj S - θ₀‖ ≤ C := by
    intro S hS hballS
    have hJ_bdd' : ∀ t ∈ Set.Icc (0:ℝ) S, ‖outputJacobian f X (θ_traj t)‖ ≤ M :=
      fun t ht => hJ_bdd (θ_traj t) (hballS t ht)
    have h_rr' : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ v : EuclideanSpace ℝ (Fin m),
        lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp) :=
      fun t ht v => h_rr_ball (θ_traj t) (hballS t ht) v
    have hfinal := displacement_integral_bound f X y hflow S hS M lambda_min hm hlambda_pos
      hdiff hJ_bdd' h_rr'
    rw [hlm_def] at hfinal
    exact hfinal.trans hC_ge
  intro T hT
  exact le_of_forall_bootstrap (d := fun t => ‖θ_traj t - θ₀‖)
    ((hflow.continuousOn.sub continuousOn_const).norm.mono Set.Icc_subset_Ici_self) hCr hT
    (by simpa [hflow.init] using hr_nonneg) (fun S hS hb => hcore S hS.1 hb) T ⟨hT, le_rfl⟩

/-! ### Finite-Horizon Bootstrap Without a Spectral Gap

Positive semidefiniteness alone gives `‖r(t)‖ ≤ ‖r₀‖`, hence a displacement bound growing
linearly in the horizon (`displacement_bound_of_psd`). Closing the same continuous-induction
bootstrap as in the gap case then bounds the displacement, and thereby the kernel drift, on
`[0, T]` with no lower bound on the spectrum of the kernel. -/

/-- **Finite-horizon displacement bound without a spectral gap.** If the output Jacobian is
`M`-bounded on the closed ball of radius `r` around `θ₀` and `T * M * ‖r₀‖ / m ≤ C < r`, then a
gradient flow from `θ₀` stays within `C` of `θ₀` on `[0, T]`. -/
theorem finite_horizon_displacement_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (T M r C : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hm : 0 < (m : ℝ)) (hr : 0 ≤ r) (hCr : C < r)
    (hC_ge : T * M * ‖trainingResidual f X y θ₀‖ / m ≤ C)
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖θ_traj t - θ₀‖ ≤ C :=
  le_of_forall_bootstrap (d := fun t => ‖θ_traj t - θ₀‖)
    ((hflow.continuousOn.sub continuousOn_const).norm.mono Set.Icc_subset_Ici_self) hCr hT
    (by simpa [hflow.init] using hr) fun S hS hb =>
      (displacement_bound_of_psd f X y hflow S hS.1 M hm hdiff
        fun t ht => hJ_bdd _ (hb t ht)).trans
        (le_trans (by gcongr; exact hS.2) hC_ge)

/-- **Finite-horizon kernel freeze without a spectral gap.** Under the hypotheses of
`finite_horizon_displacement_bound` and `L_J`-Lipschitzness of the output Jacobian on the ball,
`‖K(θ(t)) - K(θ₀)‖ ≤ (2 * M * L_J) * C` for every `t ∈ [0, T]`. -/
theorem finite_horizon_kernel_freeze_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (T M L_J r C : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ)) (hr : 0 ≤ r)
    (hCr : C < r) (hC_ge : T * M * ‖trainingResidual f X y θ₀‖ / m ≤ C)
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C := by
  intro t ht
  have hdisp := finite_horizon_displacement_bound f X y hflow hdiff T M r C hT hM hm hr hCr hC_ge
    hJ_bdd t ht
  have hball : ‖θ_traj t - θ₀‖ ≤ r := hdisp.trans hCr.le
  exact (empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X (θ_traj t) θ₀ M L_J
    (hJ_bdd _ hball) (hJ_bdd θ₀ (by simpa using hr)) (hJ_lip _ hball)).trans
    (mul_le_mul_of_nonneg_left hdisp (by positivity))

/-- A nonnegative quantity bounded by `L₀ * exp (-c t)` with `c > 0` tends to `0`. Used to pass from
exponential loss decay to convergence of the training loss. -/
lemma tendsto_zero_of_le_mul_exp_neg {L : ℝ → ℝ} {L₀ c : ℝ} (hc : 0 < c)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ L t) (hL : ∀ t, 0 ≤ t → L t ≤ L₀ * Real.exp (-c * t)) :
    Tendsto L atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => L₀ * Real.exp (-c * t)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))).const_mul L₀
    simpa [Function.comp_def] using h
  exact squeeze_zero' (eventually_atTop.2 ⟨0, hnn⟩) (eventually_atTop.2 ⟨0, hL⟩) hexp

/-! ### Asymptotic Properties in the Infinite-Width Limit -/

/-- Reusable Limit: Reciprocal square root sequence vanishes as `n → ∞`. -/
lemma tendsto_const_div_sqrt_nat_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_div_atTop hg c

/-- Property 2 (Kernel Constancy / Lazy Training Freeze Bound):
Under parameter displacement `‖θ(t) - θ₀‖ ≤ C / √n` and `L_K`-Lipschitz empirical NTK,
the empirical kernel stays within `O(n^{-1/2})` of initialization for all `t ≥ 0`:
  `‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ L_K * C / √n`. -/
theorem lazy_training_kernel_freeze_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (θ₀ : EuclideanSpace ℝ (Fin P))
    (C L_K : ℝ) (hL_K : 0 ≤ L_K) (n : ℕ)
    (hlazy : ∀ t ≥ 0, ‖θ_traj t - θ₀‖ ≤ C / Real.sqrt (n : ℝ))
    (hLip : ∀ t ≥ 0, ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      L_K * ‖θ_traj t - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      L_K * C / Real.sqrt (n : ℝ) := by
  have h1 := hLip t ht
  have h2 := hlazy t ht
  have h_mul := mul_le_mul_of_nonneg_left h2 hL_K
  rw [← mul_div_assoc] at h_mul
  exact h1.trans h_mul

/-- Property 2 (Kernel Freeze Bound instantiated with Jacobian Bounds):
When `θ_traj` satisfies lazy displacement `‖θ(t) - θ₀‖ ≤ C` and the output Jacobian
is bounded by `M` and `L_J`-Lipschitz along the trajectory, the empirical NTK matrix satisfies
`‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C`.
The width decay `1/√n` belongs on `L_J = Θ(1/√n)` (from the network parameterization factor
`n^{-1/2}` in `outputJacobian`), not on parameter displacement `hlazy`. -/
theorem empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P)) (θ₀ : EuclideanSpace ℝ (Fin P))
    (C M L_J : ℝ) (hL_J : 0 ≤ L_J)
    (hlazy : ∀ t ≥ 0, ‖θ_traj t - θ₀‖ ≤ C)
    (hJ_bdd : ∀ t ≥ 0, ‖outputJacobian f X (θ_traj t)‖ ≤ M)
    (hJ_bdd₀ : ‖outputJacobian f X θ₀‖ ≤ M)
    (hJ_lip : ∀ t ≥ 0, ‖outputJacobian f X (θ_traj t) - outputJacobian f X θ₀‖ ≤
      L_J * ‖θ_traj t - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      (2 * M * L_J) * C := by
  have hLip : ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤
      (2 * M * L_J) * ‖θ_traj t - θ₀‖ :=
    empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X (θ_traj t) θ₀ M L_J
      (hJ_bdd t ht) hJ_bdd₀ (hJ_lip t ht)
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ_bdd₀
  have h2ML_nonneg : 0 ≤ 2 * M * L_J := by
    have : 0 ≤ 2 * M := by linarith
    exact mul_nonneg this hL_J
  have h_disp := hlazy t ht
  have h_bound := mul_le_mul_of_nonneg_left h_disp h2ML_nonneg
  exact hLip.trans h_bound

/-- **Global consequences of the ball hypotheses (positive-gap bootstrap).** Under the hypotheses of
Gap 5's bootstrap, for every `t ≥ 0` the gradient flow (i) stays within `C` of `θ₀`, (ii) keeps the
Rayleigh quotient of the empirical NTK at least `lambda_min₀ / 2`, (iii) moves the empirical NTK by
at most `(2 * M * L_J) * C`, and satisfies exponential decay (iv) of the residual norm and (v) of
the MSE loss, both at the rates given by `lambda_min₀ / 2`. -/
theorem lazy_training_global_bounds_of_ball_hypotheses
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (M L_J lambda_min₀ r C : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r)
    (hCr : C < r)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual f X y θ₀‖ / (lambda_min₀ / 2) ≤ C)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖) :
    ∀ t : ℝ, 0 ≤ t →
      ‖θ_traj t - θ₀‖ ≤ C ∧
      (∀ v : EuclideanSpace ℝ (Fin m), (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ v.ofLp)) ∧
      ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C ∧
      ‖trainingResidual f X y (θ_traj t)‖ ≤
        ‖trainingResidual f X y θ₀‖ * Real.exp (-((lambda_min₀ / 2) / (m : ℝ)) * t) ∧
      mseLoss f X y (θ_traj t) ≤
        mseLoss f X y θ₀ * Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t) := by
  have hdisp := lazy_training_displacement_bound f X y hflow hdiff M L_J lambda_min₀ r C
    hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀ hJ_bdd hJ_lip
  have hJ_bdd_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s)‖ ≤ M :=
    fun s hs => hJ_bdd (θ_traj s) ((hdisp s hs).trans hCr.le)
  have hJ_lip_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤
      L_J * ‖θ_traj s - θ₀‖ :=
    fun s hs => hJ_lip (θ_traj s) ((hdisp s hs).trans hCr.le)
  have hray := rayleigh_lower_bound_on_ball f X M L_J lambda_min₀ r hM hL_J hr_nonneg h_ball_gap
    h_rr₀ hJ_bdd hJ_lip
  have hr_ode : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        (trainingResidual f X y (θ_traj t)).ofLp))) t :=
    fun t ht => gradient_flow_residual_vector_ode f X y t (hflow.ode t ht) (hdiff t)
  have hrc := continuousOn_trainingResidual_comp f X y (s := Set.Ici 0) hflow.continuousOn
    (fun t _ => hdiff t)
  have h0 : trainingResidual f X y (θ_traj 0) = trainingResidual f X y θ₀ := by rw [hflow.init]
  intro t ht
  have hrr : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X (θ_traj s)) *ᵥ v.ofLp) :=
    fun s hs v => hray (θ_traj s) ((hdisp s hs.1).trans hCr.le) v
  refine ⟨hdisp t ht, fun v => hray (θ_traj t) ((hdisp t ht).trans hCr.le) v,
    empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound f X θ_traj θ₀ C M L_J hL_J hdisp
      hJ_bdd_all (hJ_bdd θ₀ (by simpa using hr_nonneg)) hJ_lip_all t ht, ?_, ?_⟩
  · have h := residual_norm_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) (lambda_min₀ / 2) t ht
      (fun s => trainingResidual f X y (θ_traj s)) hrr (hrc.mono Set.Icc_subset_Ici_self)
      (fun s hs => hr_ode s hs.1) hm t ⟨ht, le_rfl⟩
    rwa [h0] at h
  · have h := residual_norm_sq_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) (lambda_min₀ / 2) t ht
      (fun s => trainingResidual f X y (θ_traj s)) hrr (hrc.mono Set.Icc_subset_Ici_self)
      (fun s hs => hr_ode s hs.1) hm t ⟨ht, le_rfl⟩
    rw [h0] at h
    unfold mseLoss
    calc (2 * (m : ℝ))⁻¹ * ‖trainingResidual f X y (θ_traj t)‖ ^ 2
        ≤ (2 * (m : ℝ))⁻¹ * (‖trainingResidual f X y θ₀‖ ^ 2 *
            Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring

/-- **Phase 6: end-to-end kernel-freeze bound from ball-restricted Jacobian hypotheses.**
Wires Gap 5's bootstrap (`lazy_training_displacement_bound`) directly into
`empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound`: given a Jacobian bound `M` and
Lipschitz constant `L_J` on the ball `‖θ - θ₀‖ ≤ r` (exactly what a concentration argument like
Gap 3/4 supplies - never a bound uniform over the whole parameter space), plus a base
spectral-gap hypothesis `lambda_min₀` at `θ₀` and the radius/target-bound relations `hCr`,
`h_ball_gap`, `hC_ge` from Gap 5, the empirical NTK matrix never drifts from its value at `θ₀`
by more than `(2 * M * L_J) * C`. No free `hlazy`/`hLip` hypotheses remain - both are derived,
not assumed. -/
theorem lazy_training_kernel_freeze_bound_of_ball_hypotheses
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (M L_J lambda_min₀ r C : ℝ) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J) (hm : 0 < (m : ℝ))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r)
    (hCr : C < r)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual f X y θ₀‖ / (lambda_min₀ / 2) ≤ C)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C :=
  (lazy_training_global_bounds_of_ball_hypotheses f X y hflow hdiff M L_J lambda_min₀ r C hM hL_J
    hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀ hJ_bdd hJ_lip t ht).2.2.1

/-- Property 2 (Asymptotic Freeze of Empirical NTK Bound in Infinite-Width Limit):
As the network width `n → ∞`, the kernel displacement bound `L_K * C / √n` converges to `0`. -/
theorem tendsto_lazy_training_kernel_freeze (L_K C : ℝ) :
    Tendsto (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_sqrt_nat_atTop (L_K * C)

/-- Property 2 (Asymptotic Freeze of Empirical NTK Matrix in Infinite-Width Limit):
Under lazy training displacement `‖θ(t) - θ₀‖ ≤ C / √n` and Lipschitz continuity of the
empirical NTK Gram matrix `empiricalNTKMatrix`, the difference
`‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖` converges
to `0` as network width `n → ∞`. -/
theorem tendsto_lazy_training_kernel_freeze_matrix
    {P : ℕ → ℕ}
    (f : (n : ℕ) → ι → EuclideanSpace ℝ (Fin (P n)) → ℝ) (X : Fin m → ι)
    (θ_traj : (n : ℕ) → ℝ → EuclideanSpace ℝ (Fin (P n)))
    (θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin (P n)))
    (C L_K : ℝ) (hL_K : 0 ≤ L_K)
    (hlazy : ∀ n (t : ℝ), 0 ≤ t → ‖θ_traj n t - θ₀ n‖ ≤ C / Real.sqrt (n : ℝ))
    (hLip : ∀ n (t : ℝ), 0 ≤ t →
      ‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖ ≤
        L_K * ‖θ_traj n t - θ₀ n‖)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      ‖empiricalNTKMatrix (f n) X (θ_traj n t) - empiricalNTKMatrix (f n) X (θ₀ n)‖)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hh : Tendsto (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_lazy_training_kernel_freeze L_K C
  have hgf : (fun _ : ℕ => (0 : ℝ)) ≤
      (fun n : ℕ => ‖empiricalNTKMatrix (f n) X (θ_traj n t) -
        empiricalNTKMatrix (f n) X (θ₀ n)‖) :=
    fun _ => norm_nonneg _
  have hfh : (fun n : ℕ => ‖empiricalNTKMatrix (f n) X (θ_traj n t) -
      empiricalNTKMatrix (f n) X (θ₀ n)‖) ≤
      (fun n : ℕ => L_K * C / Real.sqrt (n : ℝ)) := by
    intro n
    exact lazy_training_kernel_freeze_bound (f n) X (θ_traj n) (θ₀ n) C L_K hL_K n
      (hlazy n) (hLip n) t ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh hgf hfh

/-- Property 1 (Deterministic NTK Initialization):
By `ntk_convergence` from `Kernel.lean`, the empirical kernel `empiricalNTKFromRows`
built from `n` Gaussian hidden rows converges almost surely to the deterministic
limiting kernel `limitingNTK` as width `n → ∞`:
  `k_n(x, x') → k_∞(x, x')` a.s. -/
theorem deterministic_initialization_empiricalNTK_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      Filter.Tendsto (fun n => empiricalNTKFromRows σ' rows n x x')
        Filter.atTop (𝓝 (limitingNTK σ' x x')) :=
  ntk_convergence σ' hσ'_meas hσ'_bounded x x'

/-- Property 1 (Deterministic NTK Gram Matrix Initialization Limit):
For any finite dataset `X : Fin m → Fin d → ℝ`, the empirical NTK Gram matrix
`fun α β => empiricalNTKFromRows σ' rows n (X α) (X β)` converges entrywise almost surely
to the deterministic limiting NTK Gram matrix `fun α β => limitingNTK σ' (X α) (X β)`
as width `n → ∞`. -/
theorem deterministic_initialization_empiricalNTKMatrix_tendsto_ae
    (σ' : ℝ → ℝ) (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C) (X : Fin m → Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      ∀ α β : Fin m,
        Filter.Tendsto (fun n => empiricalNTKFromRows σ' rows n (X α) (X β))
          Filter.atTop (𝓝 (limitingNTK σ' (X α) (X β))) := by
  rw [eventually_all]
  intro α
  rw [eventually_all]
  intro β
  exact ntk_convergence σ' hσ'_meas hσ'_bounded (X α) (X β)

/-- Reusable Limit: Reciprocal natural number sequence scaled by `C / ε²` vanishes as `n → ∞`. -/
lemma tendsto_chebyshev_bound_atTop (C ε : ℝ) :
    Tendsto (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) atTop (𝓝 0) := by
  have h_eq : (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) = (fun n : ℕ => (C / ε ^ 2) / (n : ℝ)) := by
    ext n
    rw [div_mul_eq_div_div]
  rw [h_eq]
  have hg : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_div_atTop hg (C / ε ^ 2)

/-- Property 1 (Empirical NTK Entrywise Chebyshev Concentration Bound):
For any tolerance `ε > 0`, the probability under the initialization measure
`Measure.infinitePi (fun _ => gaussianRowMeasure d)` that the empirical NTK
`empiricalNTKFromRows σ' rows n x x'` deviates from its expectation by `≥ ε`
is bounded by `variance (empiricalNTKFromRows σ' · n x x') μ / ε²`.
When the estimator's variance decays as `≤ C / n`, this probability is bounded
by `C / (ε² * n)`. -/
theorem deterministic_initialization_chebyshev_bound
    (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) (n : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hL2 : MemLp (fun rows => empiricalNTKFromRows σ' rows n x x') 2
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d))
    (hvar : ProbabilityTheory.variance (fun rows => empiricalNTKFromRows σ' rows n x x')
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d) ≤ C / (n : ℝ)) :
    let μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)
    let k_n := fun rows => empiricalNTKFromRows σ' rows n x x'
    μ {rows | ε ≤ |k_n rows - ∫ r, k_n r ∂μ|} ≤
      ENNReal.ofReal (C / (ε ^ 2 * (n : ℝ))) := by
  intro μ k_n
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hL2 hε
  have h_bound : ProbabilityTheory.variance k_n μ / ε ^ 2 ≤ C / (ε ^ 2 * (n : ℝ)) := by
    have h_pos : 0 < ε ^ 2 := pow_pos hε 2
    have h1 : ProbabilityTheory.variance k_n μ / ε ^ 2 =
        (ε ^ 2)⁻¹ * ProbabilityTheory.variance k_n μ := by ring
    have h2 : C / (ε ^ 2 * (n : ℝ)) = (ε ^ 2)⁻¹ * (C / (n : ℝ)) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hvar (inv_pos.mpr h_pos).le
  exact hcheb.trans (ENNReal.ofReal_le_ofReal h_bound)

/-- Property 1 (Asymptotic Concentration of Empirical NTK Deviation in Probability):
As network width `n → ∞`, the Chebyshev upper bound `ENNReal.ofReal (C / (ε² * n))`
on the probability that `empiricalNTKFromRows` deviates by `≥ ε` converges to `0`. -/
theorem tendsto_empiricalNTK_chebyshev_bound (C ε : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (C / (ε ^ 2 * (n : ℝ)))) atTop (𝓝 0) := by
  have h_real : Tendsto (fun n : ℕ => C / (ε ^ 2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_chebyshev_bound_atTop C ε
  have h := ENNReal.tendsto_ofReal h_real
  rw [ENNReal.ofReal_zero] at h
  exact h

/-! ### Stability of Linear ODEs under Coefficient Perturbation

Generic, network-independent stability estimate used to compare the actual residual dynamics
`r' = -(1 / m) K(t) r` with the frozen dynamics `s' = -(1 / m) K_∞ s`. -/

section LinearODECoefficientPerturbation

/-- One-point estimate behind coefficient-perturbation stability: if `A` is PSD then the error
`e = r - s` between solutions of `r' = -A r` and `s' = -B s` satisfies
`⟪e, e'⟫ ≤ ‖e‖ ‖A - B‖ ‖s‖`. -/
private lemma inner_sub_le_of_psd_coefficient (A B : Matrix (Fin m) (Fin m) ℝ)
    (r s : EuclideanSpace ℝ (Fin m))
    (hA : ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)) :
    ⟪r - s, (WithLp.toLp 2 (-(A *ᵥ r.ofLp)) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 (-(B *ᵥ s.ofLp))⟫ ≤ ‖r - s‖ * (‖A - B‖ * ‖s‖) := by
  have hvec : (WithLp.toLp 2 (-(A *ᵥ r.ofLp)) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (-(B *ᵥ s.ofLp)) =
      -(WithLp.toLp 2 (A *ᵥ (r - s).ofLp) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) := by
    ext i
    simp [Matrix.mulVec_sub, Matrix.sub_mulVec]
    ring
  rw [hvec, inner_sub_right, inner_neg_right, inner_toLp_mulVec_eq_dotProduct]
  have h1 := hA (r - s)
  have h2 : -⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫ ≤
      ‖r - s‖ * (‖A - B‖ * ‖s‖) := by
    calc -⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫
        ≤ |⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫| := neg_le_abs _
      _ ≤ ‖r - s‖ * ‖(WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖r - s‖ * (‖A - B‖ * ‖s‖) :=
          mul_le_mul_of_nonneg_left (mulVec_frobenius_norm_le (A - B) s) (norm_nonneg _)
  linarith

/-- **Stability of linear ODEs under coefficient perturbation (PSD case).** Let `r' = -A(t) r` and
`s' = -B(t) s` on `[0, T]` with `A(t)` positive semidefinite, and suppose
`‖A(t) - B(t)‖ ‖s(t)‖ ≤ a` there. Then `‖r(t) - s(t)‖ ≤ ‖r(0) - s(0)‖ + a t` for `t ∈ [0, T]`.
The equation for `r` is only needed on `(0, T)`, with `r` continuous on `[0, T]`, so forward-time
trajectories qualify.
The PSD hypothesis on `A` removes any exponential Grönwall factor: the dissipative part
`-⟪e, A e⟫` of the error equation is nonpositive and only the forcing `(A - B) s` remains.
Independent of neural networks, initialization and width. -/
theorem norm_sub_le_of_linear_ode_perturbation
    (A B : ℝ → Matrix (Fin m) (Fin m) ℝ) (r s : ℝ → EuclideanSpace ℝ (Fin m)) {T a : ℝ}
    (hT : 0 ≤ T) (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T, HasDerivAt r (WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp))) t)
    (hs : ∀ t ∈ Set.Icc 0 T, HasDerivAt s (WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t)
    (hA : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (A t *ᵥ v.ofLp))
    (hab : ∀ t ∈ Set.Icc 0 T, ‖A t - B t‖ * ‖s t‖ ≤ a) :
    ∀ t ∈ Set.Icc 0 T, ‖r t - s t‖ ≤ ‖r 0 - s 0‖ + a * t := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have ha : 0 ≤ a := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hab 0 h0)
  have he : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun τ => r τ - s τ)
      ((WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp)) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t := fun t ht =>
    (hr t ht).sub (hs t (Set.Ioo_subset_Icc_self ht))
  have hsc : ContinuousOn s (Set.Icc 0 T) := fun t ht => (hs t ht).continuousAt.continuousWithinAt
  -- Regularized comparison: `√(‖e‖² + η²) - a t` is nonincreasing on `[0, T]`.
  have key : ∀ η > 0, ∀ t ∈ Set.Icc 0 T,
      Real.sqrt (‖r t - s t‖ ^ 2 + η ^ 2) ≤ Real.sqrt (‖r 0 - s 0‖ ^ 2 + η ^ 2) + a * t := by
    intro η hη t ht
    have hpos : ∀ τ, 0 < ‖r τ - s τ‖ ^ 2 + η ^ 2 := fun τ => by positivity
    have hu : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt
        (fun σ => Real.sqrt (‖r σ - s σ‖ ^ 2 + η ^ 2) - a * σ)
        ((2 * ⟪r τ - s τ, (WithLp.toLp 2 (-(A τ *ᵥ (r τ).ofLp)) : EuclideanSpace ℝ (Fin m)) -
            WithLp.toLp 2 (-(B τ *ᵥ (s τ).ofLp))⟫) /
          (2 * Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2)) - a * 1) τ := by
      intro τ hτ
      have h1 := ((he τ hτ).norm_sq.add_const (η ^ 2)).sqrt
        (hpos τ).ne'
      exact h1.sub ((hasDerivAt_id τ).const_mul a)
    have hanti : AntitoneOn (fun σ => Real.sqrt (‖r σ - s σ‖ ^ 2 + η ^ 2) - a * σ)
        (Set.Icc 0 T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
        ((((hrc.sub hsc).norm.pow 2).add continuousOn_const).sqrt.sub
          (continuousOn_const.mul continuousOn_id))
        (fun τ hτ => (hu τ (by rwa [interior_Icc] at hτ)).differentiableAt.differentiableWithinAt)
        (fun τ hτ => ?_)
      have hτ'' : τ ∈ Set.Ioo 0 T := by rwa [interior_Icc] at hτ
      have hτ' := Set.Ioo_subset_Icc_self hτ''
      rw [(hu τ hτ'').deriv]
      have hS : 0 < Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) := Real.sqrt_pos.2 (hpos τ)
      have hle : ‖r τ - s τ‖ ≤ Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) := by
        calc ‖r τ - s τ‖ = Real.sqrt (‖r τ - s τ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg η])
      have hin := inner_sub_le_of_psd_coefficient (A τ) (B τ) (r τ) (s τ) (hA τ hτ')
      have hin' : ⟪r τ - s τ, (WithLp.toLp 2 (-(A τ *ᵥ (r τ).ofLp)) : EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (-(B τ *ᵥ (s τ).ofLp))⟫ ≤
          Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) * a := by
        refine hin.trans ?_
        calc ‖r τ - s τ‖ * (‖A τ - B τ‖ * ‖s τ‖) ≤ ‖r τ - s τ‖ * a :=
            mul_le_mul_of_nonneg_left (hab τ hτ') (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right hle ha
      rw [mul_one, sub_nonpos, mul_div_mul_left _ _ two_ne_zero, div_le_iff₀ hS]
      linarith [hin']
    have := hanti h0 ht ht.1
    simp only [mul_zero, sub_zero] at this
    linarith
  intro t ht
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : ‖r t - s t‖ ≤ Real.sqrt (‖r t - s t‖ ^ 2 + η ^ 2) := by
    calc ‖r t - s t‖ = Real.sqrt (‖r t - s t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg η])
  have h2 : Real.sqrt (‖r 0 - s 0‖ ^ 2 + η ^ 2) ≤ ‖r 0 - s 0‖ + η := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg (r 0 - s 0)]
  linarith [key η hη t ht]

/-- **Residual vs. frozen-kernel residual.** Specialization of
`norm_sub_le_of_linear_ode_perturbation` to `A t = (1 / m) K t` and `B t = (1 / m) K_inf`, i.e. to
the NTK residual dynamics: if the kernel `K t` is positive semidefinite along `[0, T]` and
`‖K t - K_inf‖ ‖s t‖ ≤ b`, then `‖r t - s t‖ ≤ ‖r 0 - s 0‖ + (1 / m) b t`. -/
theorem residual_sub_frozen_residual_le
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r s : ℝ → EuclideanSpace ℝ (Fin m)) {T b : ℝ} (hT : 0 ≤ T)
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hs : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt s (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (s t).ofLp))) t)
    (hK : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖K t - K_inf‖ * ‖s t‖ ≤ b) :
    ∀ t ∈ Set.Icc 0 T, ‖r t - s t‖ ≤ ‖r 0 - s 0‖ + (m : ℝ)⁻¹ * b * t := by
  have hcoeff : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m)),
      (-(m : ℝ)⁻¹ • (M *ᵥ v.ofLp) : Fin m → ℝ) = -(((m : ℝ)⁻¹ • M) *ᵥ v.ofLp) := by
    intro M v
    rw [Matrix.smul_mulVec, neg_smul]
  have h := norm_sub_le_of_linear_ode_perturbation (fun t => (m : ℝ)⁻¹ • K t)
    (fun _ => (m : ℝ)⁻¹ • K_inf) r s (a := (m : ℝ)⁻¹ * b) hT hrc
    (fun t ht => by simpa only [hcoeff] using hr t ht)
    (fun t ht => by simpa only [hcoeff] using hs t ht)
    (fun t ht v => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)) (hK t ht v))
    (fun t ht => by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)),
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb t ht) (inv_nonneg.2 (Nat.cast_nonneg m)))
  exact h

/-- **Actual residual vs. the frozen matrix-exponential residual.** If `r' = -(1 / m) K(t) r` on
`[0, T]` with `K(t)` and `K_inf` positive semidefinite and `‖K(t) - K_inf‖ ≤ ε_K` there, then
`‖r(t) - exp(-(t / m) K_inf) r(0)‖ ≤ (1 / m) ε_K ‖r(0)‖ t`. The frozen residual starts at the same
initial condition and its norm never exceeds `‖r(0)‖` (positive semidefiniteness of `K_inf`), which
is what makes the coefficient error `‖K - K_inf‖ ‖s‖` controlled by `ε_K ‖r(0)‖`. -/
theorem residual_sub_matrix_exp_le
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) {T ε_K : ℝ} (hT : 0 ≤ T) (hm : 0 < (m : ℝ))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hK : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hK_inf : ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖K t - K_inf‖ ≤ ε_K) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖r t - (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
        EuclideanSpace ℝ (Fin m))‖ ≤ (m : ℝ)⁻¹ * (ε_K * ‖r 0‖) * t := by
  have hε_K : 0 ≤ ε_K := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hs0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
      EuclideanSpace ℝ (Fin m)) = r 0 := by simp
  have h := residual_sub_frozen_residual_le K K_inf r
    (fun t => (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
      EuclideanSpace ℝ (Fin m))) (b := ε_K * ‖r 0‖) hT hrc hr
    (fun t _ => matrix_exp_residual_trajectory_hasDerivAt K_inf (r 0) t) hK
    (fun t ht => mul_le_mul (hb t ht) (by
      simpa using matrix_exp_residual_decay K_inf (r 0) 0
        (fun v => by simpa using hK_inf v) hm t ht.1) (norm_nonneg _) hε_K)
  intro t ht
  have := h t ht
  simpa [hs0] using this

end LinearODECoefficientPerturbation

/-! ### Global Flow of a Locally Lipschitz Field with A Priori Bounds

Generic construction, independent of neural networks, of the two-sided flow of an autonomous field
`V` that is Lipschitz on balls and admits a priori bounds on solutions. It specializes Mathlib's
Picard-Lindelöf theorem to a truncation of `V`, closes the truncation with the continuous-induction
bootstrap `le_of_forall_bootstrap`, and glues the finite windows by uniqueness. -/

section GlobalFlowConstruction

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The radial cutoff `1` on the ball of radius `A` and `0` outside the ball of radius `2A`, as a
`1/A`-Lipschitz function. -/
lemma abs_cutoff_sub_le {A : ℝ} (hA : 0 < A) (x y : E) :
    |max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))| ≤ A⁻¹ * ‖x - y‖ := by
  have h1 : |(2 - ‖x‖ / A) - (2 - ‖y‖ / A)| ≤ A⁻¹ * ‖x - y‖ := by
    have : (2 - ‖x‖ / A) - (2 - ‖y‖ / A) = -(A⁻¹ * (‖x‖ - ‖y‖)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hA)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (inv_pos.2 hA).le
  have hclamp : LipschitzWith 1 (fun u : ℝ => max 0 (min 1 u)) :=
    (LipschitzWith.id.const_min 1).const_max 0
  have h := hclamp.dist_le_mul (2 - ‖x‖ / A) (2 - ‖y‖ / A)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h.trans h1

omit [NormedSpace ℝ E] in
lemma cutoff_eq_zero {A : ℝ} (hA : 0 < A) {x : E} (hx : 2 * A ≤ ‖x‖) :
    max 0 (min 1 (2 - ‖x‖ / A)) = 0 := by
  have h2 : 2 ≤ ‖x‖ / A := by rw [le_div_iff₀ hA]; linarith
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [NormedSpace ℝ E] in
lemma cutoff_eq_one {A : ℝ} (hA : 0 < A) {x : E} (hx : ‖x‖ ≤ A) :
    max 0 (min 1 (2 - ‖x‖ / A)) = 1 := by
  have h1 : ‖x‖ / A ≤ 1 := by rw [div_le_iff₀ hA]; linarith
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

/-- **Cutoff of a locally Lipschitz vector field.** If `V` is bounded by `M` and `K`-Lipschitz on
the ball of radius `2A`, then `x ↦ χ(x) • V x`, with the radial cutoff `χ` (`1` on the ball of
radius `A`,
`0` outside the ball of radius `2A`), is `(K + M / A)`-Lipschitz on all of `E`. -/
lemma norm_cutoff_smul_sub_le {V : E → E} {A K M : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hbdd : ∀ x, ‖x‖ ≤ 2 * A → ‖V x‖ ≤ M)
    (hlip : ∀ x y, ‖x‖ ≤ 2 * A → ‖y‖ ≤ 2 * A → ‖V x - V y‖ ≤ K * ‖x - y‖) (x y : E) :
    ‖max 0 (min 1 (2 - ‖x‖ / A)) • V x - max 0 (min 1 (2 - ‖y‖ / A)) • V y‖ ≤
      (K + A⁻¹ * M) * ‖x - y‖ := by
  have hχ0 : ∀ z : E, 0 ≤ max 0 (min 1 (2 - ‖z‖ / A)) := fun z => le_max_left _ _
  have hχ1 : ∀ z : E, max 0 (min 1 (2 - ‖z‖ / A)) ≤ 1 :=
    fun z => max_le zero_le_one (min_le_left _ _)
  have hχlip := abs_cutoff_sub_le hA x y
  have hAM : 0 ≤ A⁻¹ * M := by positivity
  by_cases hx : ‖x‖ ≤ 2 * A <;> by_cases hy : ‖y‖ ≤ 2 * A
  · -- both inside the ball of radius `2A`
    have h1 : max 0 (min 1 (2 - ‖x‖ / A)) • V x - max 0 (min 1 (2 - ‖y‖ / A)) • V y =
        (max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))) • V x +
          max 0 (min 1 (2 - ‖y‖ / A)) • (V x - V y) := by
      rw [sub_smul, smul_sub]; abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hχ0 y)]
    have h2 : |max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))| * ‖V x‖ ≤
        A⁻¹ * ‖x - y‖ * M := mul_le_mul hχlip (hbdd x hx) (norm_nonneg _) (by positivity)
    have h3 : max 0 (min 1 (2 - ‖y‖ / A)) * ‖V x - V y‖ ≤ K * ‖x - y‖ :=
      (mul_le_mul_of_nonneg_right (hχ1 y) (norm_nonneg _)).trans
        (by rw [one_mul]; exact hlip x y hx hy)
    nlinarith [h2, h3]
  · -- `y` outside: its cutoff vanishes
    have hy0 := cutoff_eq_zero hA (not_le.1 hy).le
    rw [hy0, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
    have hd : max 0 (min 1 (2 - ‖x‖ / A)) ≤ A⁻¹ * ‖x - y‖ := by
      have := hχlip
      rw [hy0, sub_zero, abs_of_nonneg (hχ0 x)] at this
      exact this
    calc max 0 (min 1 (2 - ‖x‖ / A)) * ‖V x‖ ≤ (A⁻¹ * ‖x - y‖) * M :=
          mul_le_mul hd (hbdd x hx) (norm_nonneg _) (by positivity)
      _ ≤ (K + A⁻¹ * M) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  · have hx0 := cutoff_eq_zero hA (not_le.1 hx).le
    rw [hx0, zero_smul, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hχ0 y)]
    have hd : max 0 (min 1 (2 - ‖y‖ / A)) ≤ A⁻¹ * ‖x - y‖ := by
      have := hχlip
      rw [hx0, zero_sub, abs_neg, abs_of_nonneg (hχ0 y)] at this
      exact this
    calc max 0 (min 1 (2 - ‖y‖ / A)) * ‖V y‖ ≤ (A⁻¹ * ‖x - y‖) * M :=
          mul_le_mul hd (hbdd y hy) (norm_nonneg _) (by positivity)
      _ ≤ (K + A⁻¹ * M) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  · rw [cutoff_eq_zero hA (not_le.1 hx).le, cutoff_eq_zero hA (not_le.1 hy).le]
    simp only [zero_smul, sub_self, norm_zero]
    positivity

variable [CompleteSpace E]

/-- **Local-to-uniform flow of a globally Lipschitz bounded field.** A bounded, globally Lipschitz
autonomous field has a flow on `[-T, T]`, jointly continuous in the initial point (in any ball) and
time. This specializes Mathlib's Picard-Lindelöf theorem with `x₀ = 0` and `a = r + M T`, so the
ball hypothesis is automatic. -/
lemma exists_flow_of_lipschitzWith_of_bound (Vg : E → E) {K M : NNReal} (hVlip : LipschitzWith K Vg)
    (hVb : ∀ x, ‖Vg x‖ ≤ M) (T r : NNReal) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall (0 : E) r, α (x, 0) = x ∧
        ∀ t ∈ Icc (-(T : ℝ)) T, HasDerivWithinAt (fun s => α (x, s)) (Vg (α (x, t)))
          (Icc (-(T : ℝ)) T) t) ∧
      ContinuousOn α (closedBall (0 : E) r ×ˢ Icc (-(T : ℝ)) T) := by
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨by simp, T.2⟩
  have hPL : IsPicardLindelof (fun _ : ℝ => Vg) (⟨0, h0⟩ : Icc (-(T : ℝ)) T) (0 : E)
      (r + M * T) r M K :=
    { lipschitzOnWith := fun _ _ => hVlip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ _ _ => hVb _
      mul_max_le := by
        simp only [NNReal.coe_add, NNReal.coe_mul, add_sub_cancel_left, zero_sub, sub_zero, neg_neg,
          max_self]
        exact le_rfl }
  exact hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn


/-- **Finite-window flow with an a priori bound.** Suppose `V` is Lipschitz on balls and every
solution on `[0, S]` (`S ≤ T`) that starts in the ball of radius `r` stays in a ball of some radius
`ρ`. Then `V` has a forward flow on `[0, T]`, jointly continuous in the initial point (in the
ball of radius `r`) and time. Proof: truncate `V` outside a large ball, apply
`exists_flow_of_lipschitzWith_of_bound`, and use the continuous-induction bootstrap
`le_of_forall_bootstrap` to show the truncated flow never leaves the region where it agrees with
`V`. Only forward time is used, so nothing is required of the solution for negative times. -/
theorem exists_flow_window (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    (T r : NNReal)
    (hprior : ∃ ρ : ℝ, ∀ (θ : ℝ → E) (S : ℝ), 0 ≤ S → S ≤ T → ‖θ 0‖ ≤ r →
      (∀ t ∈ Icc 0 S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t) → ‖θ S‖ ≤ ρ) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall (0 : E) r, α (x, 0) = x ∧
        ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => α (x, s)) (V (α (x, t)))
          (Icc 0 (T : ℝ)) t) ∧
      ContinuousOn α (closedBall (0 : E) r ×ˢ Icc 0 (T : ℝ)) := by
  obtain ⟨ρ, hρ⟩ := hprior
  set A : ℝ := max ρ r + 1 with hA_def
  have hA : 0 < A := by
    have h0 : (0 : ℝ) ≤ r := r.2
    have := le_max_right ρ (r : ℝ)
    linarith
  obtain ⟨K, hK, hKlip⟩ := hV_lip (2 * A)
  set M : ℝ := ‖V 0‖ + K * (2 * A) with hM_def
  have hM : 0 ≤ M := by positivity
  have hVbdd : ∀ x : E, ‖x‖ ≤ 2 * A → ‖V x‖ ≤ M := fun x hx => by
    have h := hKlip x 0 hx
      (by simp only [norm_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity)
    rw [sub_zero] at h
    have h2 := norm_sub_norm_le (V x) (V 0)
    rw [hM_def]; nlinarith [norm_nonneg x]
  set Vg : E → E := fun x => max 0 (min 1 (2 - ‖x‖ / A)) • V x with hVg
  have hχ0 : ∀ z : E, 0 ≤ max 0 (min 1 (2 - ‖z‖ / A)) := fun z => le_max_left _ _
  have hχ1 : ∀ z : E, max 0 (min 1 (2 - ‖z‖ / A)) ≤ 1 :=
    fun z => max_le zero_le_one (min_le_left _ _)
  have hVg_lip : LipschitzWith ⟨K + A⁻¹ * M, by positivity⟩ Vg :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact norm_cutoff_smul_sub_le hA hK hM hVbdd hKlip x y
  have hVg_bdd : ∀ x, ‖Vg x‖ ≤ (⟨M, hM⟩ : NNReal) := fun x => by
    by_cases hx : ‖x‖ ≤ 2 * A
    · rw [hVg]
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
      calc _ ≤ 1 * ‖V x‖ := mul_le_mul_of_nonneg_right (hχ1 x) (norm_nonneg _)
        _ ≤ M := by rw [one_mul]; exact hVbdd x hx
    · rw [hVg]
      dsimp only
      rw [cutoff_eq_zero hA (not_le.1 hx).le, zero_smul, norm_zero]
      exact hM
  obtain ⟨α, hα, hαc⟩ := exists_flow_of_lipschitzWith_of_bound Vg hVg_lip hVg_bdd T r
  have hsub : Icc (0 : ℝ) T ⊆ Icc (-(T : ℝ)) T := Icc_subset_Icc (by linarith [T.coe_nonneg]) le_rfl
  refine ⟨α, fun x hx => ?_, hαc.mono (prod_mono subset_rfl hsub)⟩
  obtain ⟨h0, hsol⟩ := hα x hx
  refine ⟨h0, ?_⟩
  have hsolF : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => α (x, s)) (Vg (α (x, t))) (Icc 0 (T : ℝ)) t :=
    fun t ht => (hsol t (hsub ht)).mono hsub
  set θ : ℝ → E := fun s => α (x, s) with hθ
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hθcont : ContinuousOn θ (Icc (0 : ℝ) T) := fun t ht => (hsolF t ht).continuousWithinAt
  have hθ0 : θ 0 = x := h0
  have hρ_lt : ρ < A := by rw [hA_def]; linarith [le_max_left ρ (r : ℝ)]
  have hr_le : (r : ℝ) ≤ A - 1 := by
    have := le_max_right ρ (r : ℝ); rw [hA_def]; linarith
  -- forward bootstrap: `‖θ t‖ ≤ A - 1` for `t ∈ [0, T]`
  have hfwd : ∀ t ∈ Icc (0 : ℝ) T, ‖θ t‖ ≤ A - 1 := by
    refine le_of_forall_bootstrap (d := fun t => ‖θ t‖) (r := A) (C := A - 1)
      hθcont.norm (by linarith) T.coe_nonneg (by rw [hθ0]; linarith) ?_
    intro S hS hb
    have hsolS : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t := by
      intro t ht
      have h1 := (hsolF t ⟨ht.1, ht.2.trans hS.2⟩).mono
        (show Icc (0 : ℝ) S ⊆ Icc 0 (T : ℝ) from Icc_subset_Icc le_rfl hS.2)
      convert h1 using 2
      simp only [hVg]
      rw [cutoff_eq_one hA (hb t ht), one_smul]
    have := hρ θ S hS.1 hS.2 (by rw [hθ0]; exact hxr) hsolS
    rw [hA_def]
    linarith [le_max_left ρ (r : ℝ)]
  intro t ht
  have h1 := hsolF t ht
  convert h1 using 2
  simp only [hVg]
  rw [cutoff_eq_one hA (by linarith [hfwd t ht]), one_smul]

omit [CompleteSpace E] in
/-- **Uniqueness on a forward window.** Two solutions of `x' = V x` on `[0, T]` (`T > 0`),
continuous on `[0, T]` and differentiable on `(0, T)`, with the same value at `0` coincide there,
when `V` is Lipschitz on balls. Continuity makes both solutions bounded, so Mathlib's
`ODE_solution_unique_of_mem_Icc` applies on a large ball. This is a thin adapter (it supplies the
ball and constant) used only by `exists_forward_flow` and `forwardFlow_unique`, hence private. -/
private theorem forwardFlow_unique_window (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {f g : ℝ → E}
    (hfc : ContinuousOn f (Icc 0 T)) (hf : ∀ t ∈ Ioo 0 T, HasDerivAt f (V (f t)) t)
    (hgc : ContinuousOn g (Icc 0 T)) (hg : ∀ t ∈ Ioo 0 T, HasDerivAt g (V (g t)) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  -- a field that is Lipschitz on balls is continuous
  have hVc : Continuous V := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨K, hK, hKlip⟩ := hV_lip (‖x‖ + 1)
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min 1 (ε / (K + 1)), by positivity, fun y hy => ?_⟩
    have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y x < ε / (K + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    rw [dist_eq_norm] at hy1 hy2 ⊢
    have hyn : ‖y‖ ≤ ‖x‖ + 1 := by linarith [norm_sub_norm_le y x]
    have := hKlip y x hyn (by linarith [norm_nonneg x])
    rw [lt_div_iff₀ (by positivity)] at hy2
    nlinarith [norm_nonneg (y - x)]
  -- solutions have a right derivative at the initial time as well (the derivative has a limit)
  have hright : ∀ {h : ℝ → E}, ContinuousOn h (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, HasDerivAt h (V (h t)) t) → ∀ t ∈ Ico 0 T,
        HasDerivWithinAt h (V (h t)) (Ici t) t := by
    intro h hc hd t ht
    rcases ht.1.eq_or_lt with rfl | hpos
    · have hcw : ContinuousWithinAt h (Ioi 0) 0 :=
        (hc 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self)
      have hlim : Filter.Tendsto (fun x => V (h x)) (nhdsWithin 0 (Ioi 0)) (nhds (V (h 0))) :=
        (hVc.continuousAt.tendsto).comp hcw.tendsto
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 T)
        (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
        ((hc 0 ⟨le_rfl, hT.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hT) ?_
      exact hlim.congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT hT)
        fun x hx => (hd x hx).deriv.symm)
    · exact (hd t ⟨hpos, ht.2⟩).hasDerivWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK, hKlip⟩ := hV_lip (max Cf Cg)
  have hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K.toNNReal ((fun _ : ℝ => V) t)
      ((fun _ : ℝ => closedBall (0 : E) (max Cf Cg)) t) := fun _ _ =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simpa [dist_eq_norm, Real.coe_toNNReal K hK] using
        hKlip x y (by simpa using hx) (by simpa using hy)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
    (s := fun _ => closedBall (0 : E) (max Cf Cg)) hv hfc (hright hfc hf)
    (fun t ht => by simpa using (hCf t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)) hgc
    (hright hgc hg)
    (fun t ht => by simpa using (hCg t (Ico_subset_Icc_self ht)).trans (le_max_right _ _)) h0

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A locally Lipschitz map on a proper normed space is Lipschitz on every closed ball centered at
`0`, in the elementary form used by `exists_forward_flow` and `forwardFlow_unique`. -/
lemma lipschitz_on_ball_of_locallyLipschitz [ProperSpace E] {V : E → E} (hV : LocallyLipschitz V)
    (A : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := (hV.locallyLipschitzOn (s := closedBall (0 : E) A)
    ).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 A)
  refine ⟨K, K.2, fun x z hx hz => ?_⟩
  have := hK.dist_le_mul x (by simpa using hx) z (by simpa using hz)
  simpa [dist_eq_norm] using this

omit [CompleteSpace E] in
/-- **Forward uniqueness of solutions.** If `V` is Lipschitz on balls, two solutions of `x' = V x`
that are continuous on `[0, ∞)` and differentiable for `t > 0`, with the same value at `0`, agree on
`[0, ∞)`. -/
theorem forwardFlow_unique (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    {f g : ℝ → E} (hfc : ContinuousOn f (Ici 0)) (hf : ∀ t, 0 < t → HasDerivAt f (V (f t)) t)
    (hgc : ContinuousOn g (Ici 0)) (hg : ∀ t, 0 < t → HasDerivAt g (V (g t)) t)
    (h0 : f 0 = g 0) : EqOn f g (Ici 0) := fun t ht =>
  forwardFlow_unique_window V hV_lip (T := t + 1) (by linarith [show (0 : ℝ) ≤ t from ht])
    (hfc.mono Icc_subset_Ici_self) (fun s hs => hf s hs.1)
    (hgc.mono Icc_subset_Ici_self) (fun s hs => hg s hs.1) h0 ⟨ht, by linarith⟩

/-- **Forward flow from local Lipschitz continuity and a priori bounds.** Suppose `V` is Lipschitz
on balls and solutions on `[0, S]` starting in a ball stay in a ball whose radius depends only on
the horizon and the starting radius. Then there is a flow `Φ : E → ℝ → E` solving `x' = V x` for all
positive times, with `Φ x 0 = x` and `(x, t) ↦ Φ x t` continuous (for negative times `Φ x t = x` by
construction, which carries no meaning). Solutions are unique (`forwardFlow_unique`), so `Φ` is
*the* forward flow. -/
theorem exists_forward_flow (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    (hprior : ∀ T r : ℝ, ∃ ρ : ℝ, ∀ (θ : ℝ → E) (S : ℝ), 0 ≤ S → S ≤ T →
      ‖θ 0‖ ≤ r → (∀ t ∈ Icc 0 S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t) → ‖θ S‖ ≤ ρ) :
    ∃ Φ : E → ℝ → E, (∀ x, Φ x 0 = x) ∧ (∀ x t, 0 < t → HasDerivAt (Φ x) (V (Φ x t)) t) ∧
      Continuous (fun p : E × ℝ => Φ p.1 p.2) := by
  choose α hα using fun k : ℕ => exists_flow_window V hV_lip ((k + 1 : ℕ) : NNReal)
    ((k + 1 : ℕ) : NNReal) (hprior _ _)
  -- the radius/window `k + 1` in real form
  have hcast : ∀ k : ℕ, (((k + 1 : ℕ) : NNReal) : ℝ) = (k : ℝ) + 1 := fun k => by push_cast; ring
  have hsol : ∀ k : ℕ, ∀ x : E, ‖x‖ ≤ (k : ℝ) + 1 → α k (x, 0) = x ∧
      ∀ t ∈ Icc 0 ((k : ℝ) + 1), HasDerivWithinAt (fun s => α k (x, s))
        (V (α k (x, t))) (Icc 0 ((k : ℝ) + 1)) t := fun k x hx => by
    have := (hα k).1 x (by rw [mem_closedBall, dist_zero_right, hcast]; exact hx)
    simpa [hcast] using this
  have hcont : ∀ k : ℕ, ContinuousOn (α k)
      (closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1)) := fun k => by
    simpa [hcast] using (hα k).2
  -- consistency between different windows
  have hcons : ∀ k k' : ℕ, ∀ x : E, ‖x‖ ≤ (k : ℝ) + 1 → ‖x‖ ≤ (k' : ℝ) + 1 → ∀ t : ℝ,
      0 ≤ t → t ≤ (k : ℝ) + 1 → t ≤ (k' : ℝ) + 1 → α k (x, t) = α k' (x, t) := by
    intro k k' x hx hx' t ht0 ht ht'
    set m : ℕ := min k k' with hm
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast min_le_left k k'
    have hmk' : (m : ℝ) ≤ k' := by exact_mod_cast min_le_right k k'
    have hsub : ∀ j : ℕ, (m : ℝ) ≤ j → Icc 0 ((m : ℝ) + 1) ⊆ Icc 0 ((j : ℝ) + 1) :=
      fun j hj u hu => ⟨hu.1, by linarith [hu.2]⟩
    have hwin : ∀ j : ℕ, (m : ℝ) ≤ j → ‖x‖ ≤ (j : ℝ) + 1 →
        ContinuousOn (fun s => α j (x, s)) (Icc 0 ((m : ℝ) + 1)) ∧
        ∀ s ∈ Ioo 0 ((m : ℝ) + 1), HasDerivAt (fun s => α j (x, s)) (V (α j (x, s))) s :=
      fun j hj hxj =>
        ⟨fun s hs => (((hsol j x hxj).2 s (hsub j hj hs)).mono (hsub j hj)).continuousWithinAt,
          fun s hs => (((hsol j x hxj).2 s (hsub j hj (Ioo_subset_Icc_self hs))).mono
            (hsub j hj)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)⟩
    have hfun := forwardFlow_unique_window V hV_lip (T := (m : ℝ) + 1) (by positivity)
      (hwin k hmk hx).1 (hwin k hmk hx).2 (hwin k' hmk' hx').1 (hwin k' hmk' hx').2
      (by rw [(hsol k x hx).1, (hsol k' x hx').1])
    refine hfun ⟨ht0, ?_⟩
    rcases le_total k k' with h | h
    · rw [hm, min_eq_left h]; exact ht
    · rw [hm, min_eq_right h]; exact ht'
  set Φ : E → ℝ → E := fun x t => α ⌈max ‖x‖ t⌉₊ (x, t) with hΦ_def
  have hΦ : ∀ (x : E) (t : ℝ) (k : ℕ), ‖x‖ ≤ (k : ℝ) + 1 → 0 ≤ t → t ≤ (k : ℝ) + 1 →
      Φ x t = α k (x, t) := by
    intro x t k hx ht0 ht
    have hk₀ : max ‖x‖ t ≤ (⌈max ‖x‖ t⌉₊ : ℝ) := Nat.le_ceil _
    exact hcons _ k x ((le_max_left _ _).trans hk₀ |>.trans (by linarith)) hx t ht0
      ((le_max_right _ _).trans hk₀ |>.trans (by linarith)) ht
  have hmain : (∀ x, Φ x 0 = x) ∧ (∀ x t, 0 < t → HasDerivAt (Φ x) (V (Φ x t)) t) ∧
      ContinuousOn (fun p : E × ℝ => Φ p.1 p.2) (univ ×ˢ Ici 0) := by
    refine ⟨fun x => ?_, fun x t ht => ?_, fun p hp => ?_⟩
    · have hk : ‖x‖ ≤ (⌈max ‖x‖ 0⌉₊ : ℝ) + 1 :=
        ((le_max_left _ _).trans (Nat.le_ceil _)).trans (by linarith)
      rw [hΦ x 0 ⌈‖x‖⌉₊ ((Nat.le_ceil _).trans (by linarith)) le_rfl (by positivity),
        (hsol _ x ((Nat.le_ceil _).trans (by linarith))).1]
    · set k : ℕ := ⌈max ‖x‖ (t + 1)⌉₊ with hk_def
      have hk₀ : max ‖x‖ (t + 1) ≤ (k : ℝ) := Nat.le_ceil _
      have hxk : ‖x‖ ≤ (k : ℝ) + 1 := (le_max_left _ _).trans hk₀ |>.trans (by linarith)
      have ht1 : t + 1 ≤ (k : ℝ) := (le_max_right _ _).trans hk₀
      have hmem : t ∈ Icc 0 ((k : ℝ) + 1) := ⟨ht.le, by linarith⟩
      have hnhds : Icc 0 ((k : ℝ) + 1) ∈ nhds t := Icc_mem_nhds ht (by linarith)
      have hd := ((hsol k x hxk).2 t hmem).hasDerivAt hnhds
      have hev : (fun s => α k (x, s)) =ᶠ[nhds t] Φ x := by
        have hnb : Ioo (t / 2) (t + 1) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hnb] with s hs
        exact (hΦ x s k hxk (by linarith [hs.1]) (by linarith [hs.2])).symm
      rw [hΦ x t k hxk ht.le (by linarith)]
      exact (hd.congr_of_eventuallyEq hev.symm)
    · obtain ⟨x₀, t₀⟩ := p
      have ht₀ : 0 ≤ t₀ := hp.2
      set k : ℕ := ⌈max (‖x₀‖ + 1) (t₀ + 1)⌉₊ with hk_def
      have hk₀ : max (‖x₀‖ + 1) (t₀ + 1) ≤ (k : ℝ) := Nat.le_ceil _
      have hx₀k : ‖x₀‖ + 1 ≤ (k : ℝ) := (le_max_left _ _).trans hk₀
      have ht₀k : t₀ + 1 ≤ (k : ℝ) := (le_max_right _ _).trans hk₀
      have hnb : ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1) ∈ nhds (x₀, t₀) :=
        prod_mem_nhds (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith))
          (Iio_mem_nhds (by linarith))
      have hUsub : ∀ q ∈ ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1), 0 ≤ q.2 →
          ‖q.1‖ ≤ (k : ℝ) + 1 ∧ q.2 ≤ (k : ℝ) + 1 := fun q hq _ => by
        refine ⟨?_, ?_⟩
        · have := mem_ball_zero_iff.1 hq.1
          linarith
        · linarith [mem_Iio.1 hq.2]
      have hmem : (x₀, t₀) ∈ closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1) :=
        ⟨by rw [mem_closedBall, dist_zero_right]; linarith, ht₀, by linarith⟩
      have hat : ContinuousWithinAt (α k) (closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1))
          (x₀, t₀) := (hcont k) (x₀, t₀) hmem
      have hmemW : closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1) ∈
          nhdsWithin (x₀, t₀) (univ ×ˢ Ici 0) := by
        rw [mem_nhdsWithin]
        refine ⟨ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1), isOpen_ball.prod isOpen_Iio,
          ⟨by rw [mem_ball, dist_zero_right]; linarith, by simp only [mem_Iio]; linarith⟩, ?_⟩
        · rintro q ⟨hq, -, hq0⟩
          obtain ⟨h1, h2⟩ := hUsub q hq hq0
          exact ⟨by rw [mem_closedBall, dist_zero_right]; exact h1, hq0, h2⟩
      refine (hat.mono_of_mem_nhdsWithin hmemW).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hmemW, self_mem_nhdsWithin] with q hq _
        exact hΦ q.1 q.2 k (by simpa [mem_closedBall, dist_zero_right] using hq.1) hq.2.1
          hq.2.2
      · exact hΦ x₀ t₀ k (by linarith) ht₀ (by linarith)
  obtain ⟨h0, hd, hc⟩ := hmain
  -- extend by the value at `0` for negative times, so that `Φ` is continuous everywhere
  refine ⟨fun x t => Φ x (max t 0), fun x => by simpa using h0 x, fun x t ht => ?_,
    hc.comp_continuous (continuous_fst.prodMk (continuous_snd.max continuous_const))
      fun p => ⟨trivial, show (0 : ℝ) ≤ max p.2 0 from le_max_right _ _⟩⟩
  have e : Φ x (max t 0) = Φ x t := by rw [max_eq_left ht.le]
  change HasDerivAt (fun s => Φ x (max s 0)) (V (Φ x (max t 0))) t
  rw [e]
  exact (hd x t ht).congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [max_eq_left (le_of_lt hs)])

/-- A finite sum of locally Lipschitz functions is locally Lipschitz. -/
lemma locallyLipschitz_finset_sum {α ι β : Type*} [PseudoEMetricSpace α] [SeminormedAddCommGroup β]
    (s : Finset ι) {f : ι → α → β} (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : β)).locallyLipschitz
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The product of two locally Lipschitz real functions is locally Lipschitz (multiplication on
`ℝ × ℝ` is `C¹`, hence locally Lipschitz). Mathlib's `LocallyLipschitz.mul` is the product in a
seminormed commutative *group*, so it does not apply to multiplication in `ℝ`. -/
lemma locallyLipschitz_mul_real {α : Type*} [PseudoEMetricSpace α] {f g : α → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (fun x => f x * g x) :=
  (contDiff_mul.locallyLipschitz (𝕂 := ℝ) (E' := ℝ × ℝ) (F' := ℝ)).comp (hf.prodMk hg)

/-- The Euclidean norm is at most the `ℓ¹` norm of the coordinates. -/
lemma norm_euclidean_le_sum_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (v : EuclideanSpace 𝕜 ι) : ‖v‖ ≤ ∑ k, ‖v k‖ := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun k _ => norm_nonneg _,
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun k => ‖v k‖)
      fun k _ => norm_nonneg (v k)⟩

/-- A map into `EuclideanSpace ℝ ι` (`ι` finite) is locally Lipschitz if every coordinate is
locally Lipschitz. Mathlib has no `Pi`/`PiLp` version of this. -/
lemma locallyLipschitz_euclidean_of_coord {α ι : Type*} [PseudoMetricSpace α] [Fintype ι]
    {g : α → EuclideanSpace ℝ ι} (h : ∀ k, LocallyLipschitz (fun x => g x k)) :
    LocallyLipschitz g := by
  intro x
  choose K t ht hK using fun k => h k x
  refine ⟨⟨∑ k, (K k : ℝ), Finset.sum_nonneg fun k _ => (K k).2⟩, ⋂ k, t k,
    Filter.iInter_mem.2 ht, LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  rw [dist_eq_norm]
  refine (norm_euclidean_le_sum_norm _).trans ?_
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  calc ∑ k, |g y k - g z k| ≤ ∑ k, (K k : ℝ) * dist y z := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := (hK k).dist_le_mul y (Set.mem_iInter.1 hy k) z (Set.mem_iInter.1 hz k)
        simpa [Real.dist_eq] using this
    _ = _ := by rw [← Finset.sum_mul]; rfl

end GlobalFlowConstruction

/-! ### Fixed-Feature (Affine) Dynamics and Minimum Norm

For a fixed matrix `J : Matrix (Fin m) (Fin P) ℝ` (the frozen output Jacobian at initialization) the
affine model `f₀ + J (θ - θ₀)` has residual `r₀ + J w`, `w = θ - θ₀`, and its gradient flow is
`w' = -(1/m) Jᵀ (r₀ + J w)`. Everything below is stated for an arbitrary `J`, independent of
networks; `Jᵀ (J Jᵀ)⁻¹` is the Moore-Penrose pseudo-inverse of a full-row-rank `J`. -/

/-- Solution of the affine (frozen-feature) gradient flow `w' = -(1/m) Jᵀ (r₀ + J w)`, `w 0 = 0`,
when the Gram matrix `J Jᵀ` is invertible:
`w(t) = -Jᵀ (J Jᵀ)⁻¹ (r₀ - exp(-(t/m) J Jᵀ) r₀)`. -/
theorem hasDerivAt_affineFlowSolution (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
        WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
        WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))).ofLp)))) t := by
  have h := ((matrix_exp_residual_trajectory_hasDerivAt (J * Jᵀ) r₀ t).const_sub r₀)
  have h2 := (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹))).hasFDerivAt.comp_hasDerivAt t h
  refine h2.congr_deriv ?_
  set res : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp) with hres
  have hGinv : (J * Jᵀ) * (J * Jᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  have hGinv' : (J * Jᵀ)⁻¹ * (J * Jᵀ) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  simp only [matrixCLM_apply]
  have hJw : ∀ v : Fin m → ℝ, J *ᵥ (-(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ v) = -v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, hGinv, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  congr 1
  rw [hJw]
  have hJT : ∀ v : Fin m → ℝ, -(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ (-(-(m : ℝ)⁻¹ • ((J * Jᵀ) *ᵥ v))) =
      -(m : ℝ)⁻¹ • (Jᵀ *ᵥ v) := fun v => by
    rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, hGinv', Matrix.mul_one]
  simpa [hres] using hJT (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)

/-- `matrixCLM Mᵀ` is the adjoint of `matrixCLM M`. -/
lemma inner_matrixCLM_transpose {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : EuclideanSpace ℝ (Fin a)) (v : EuclideanSpace ℝ (Fin b)) :
    ⟪matrixCLM Mᵀ u, v⟫ = ⟪u, matrixCLM M v⟫ := by
  simp only [matrixCLM_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    RCLike.inner_apply, conj_trivial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


/-- **Minimum-norm characterization of the affine-flow limit.** Let `J` have invertible Gram matrix
`J Jᵀ` and put `wInf = -Jᵀ (J Jᵀ)⁻¹ r₀`. Then `J wInf = -r₀`, and every `w'` with `J w' = -r₀`
satisfies `‖w'‖² = ‖wInf‖² + ‖w' - wInf‖²`; hence `wInf` is the unique minimum-norm solution of the
interpolation constraint `f₀ + J w = y` (`r₀ = f₀ - y`). The increment `wInf` lies in the range of
`Jᵀ` (`(ker J)ᗮ`), so it is orthogonal to `ker J`. This is proved directly by Pythagoras from the
adjoint identity `inner_matrixCLM_transpose`, which is all `LinearMap.orthogonal_ker` would
supply. -/
theorem affine_minNorm_pythagoras (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp) :
    J *ᵥ (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀).ofLp = -r₀.ofLp ∧
      ‖w'‖ ^ 2 = ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 +
        ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 := by
  have hGinv : (J * Jᵀ) * (J * Jᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
  set wInf := matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ with hwInf
  have hJw : J *ᵥ wInf.ofLp = -r₀.ofLp := by
    rw [hwInf, matrixCLM_apply]
    change J *ᵥ (-(Jᵀ * (J * Jᵀ)⁻¹) *ᵥ r₀.ofLp) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, hGinv, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  refine ⟨hJw, ?_⟩
  set k := w' - wInf with hk
  have hJk : J *ᵥ k.ofLp = 0 := by
    change J *ᵥ (w'.ofLp - wInf.ofLp) = 0
    rw [Matrix.mulVec_sub, hw', hJw, sub_self]
  have hrange : wInf = matrixCLM Jᵀ (matrixCLM (-(J * Jᵀ)⁻¹) r₀) := by
    rw [hwInf]
    ext i : 1
    simp [matrixCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_neg]
  have horth : ⟪wInf, k⟫ = 0 := by
    rw [hrange, inner_matrixCLM_transpose]
    have : matrixCLM J k = 0 := by rw [matrixCLM_apply]; simp [hJk]
    rw [this, inner_zero_right]
  have hw'eq : w' = wInf + k := by rw [hk]; abel
  conv_lhs => rw [hw'eq]
  rw [norm_add_sq_real, horth]
  ring

/-- The affine-flow limit `wInf` has the least norm among all solutions of `J w = -r₀`. -/
theorem norm_affine_limit_le (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp) :
    ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ≤ ‖w'‖ := by
  have h := (affine_minNorm_pythagoras J hG r₀ hw').2
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖])
    (norm_nonneg _) |>.2

/-- Uniqueness of the minimum-norm interpolant. -/
theorem eq_affine_limit_of_norm_le (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w' : EuclideanSpace ℝ (Fin P)}
    (hw' : J *ᵥ w'.ofLp = -r₀.ofLp)
    (hle : ‖w'‖ ≤ ‖matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖) :
    w' = matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ := by
  have h := (affine_minNorm_pythagoras J hG r₀ hw').2
  have h0 : ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖w' - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀‖, norm_nonneg w',
      norm_nonneg (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀)]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0))


/-- **The minimum-norm interpolant predicts by kernel regression.** For the affine limit
`w∞ = -Jᵀ (J Jᵀ)⁻¹ r₀` and any feature vector `g`, `⟪g, w∞⟫ = -(J g) ⬝ᵥ ((J Jᵀ)⁻¹ r₀)`. With
`J = J(θ₀)`, `g = ∇f(x; θ₀)`, `r₀ = f₀(X) - y` this is `(J g)ᵀ (J Jᵀ)⁻¹ (y - f₀(X)) =
k₀(x, X)ᵀ K₀⁻¹ (y - f₀(X))`: the frozen-feature minimum-norm predictor is the kernel-regression
formula with the empirical kernels `K₀`, `k₀`. The limiting formula replaces them by `K_∞`,
`k_∞`. -/
theorem inner_affine_limit (J : Matrix (Fin m) (Fin P) ℝ) (r₀ : EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin P)) :
    ⟪g, matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀⟫ = -((J *ᵥ g.ofLp) ⬝ᵥ ((J * Jᵀ)⁻¹ *ᵥ r₀.ofLp)) := by
  have hrange : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ =
      matrixCLM Jᵀ (matrixCLM (-(J * Jᵀ)⁻¹) r₀) := by
    ext i : 1
    simp [matrixCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_neg]
  rw [hrange, real_inner_comm, inner_matrixCLM_transpose]
  simp [matrixCLM_apply, PiLp.inner_apply, dotProduct, Matrix.neg_mulVec]

/-- **Closed form of the affine (frozen-feature) gradient flow.** Let `J` have invertible Gram
matrix.
Any forward-time solution of `w' = -(1/m) Jᵀ (r₀ + J w)`, `w(0) = 0` -- the gradient flow of the
affine model `f₀ + J w` under the mean-squared loss with residual `r₀ + J w` -- equals
`w(t) = -Jᵀ (J Jᵀ)⁻¹ (r₀ - exp(-(t/m) J Jᵀ) r₀)` for `t ≥ 0`. In particular `w(t)` lies in the range
of `Jᵀ`. Uniqueness is `forwardFlow_unique` (the field is affine, hence Lipschitz). -/
theorem affineFlow_eq_solution (J : Matrix (Fin m) (Fin P) ℝ) (hG : IsUnit (J * Jᵀ))
    (r₀ : EuclideanSpace ℝ (Fin m)) {w : ℝ → EuclideanSpace ℝ (Fin P)} (hw0 : w 0 = 0)
    (hwc : ContinuousOn w (Set.Ici 0))
    (hw : ∀ t : ℝ, 0 < t → HasDerivAt w
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ (w t).ofLp)))) t) {t : ℝ} (ht : 0 ≤ t) :
    w t = matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)) := by
  set V : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin P) := fun x =>
    WithLp.toLp 2 (-(m : ℝ)⁻¹ • (Jᵀ *ᵥ (r₀.ofLp + J *ᵥ x.ofLp))) with hV
  have hVsub : ∀ x y, V x - V y = matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J)) (x - y) := fun x y => by
    ext i : 1
    simp [hV, matrixCLM_apply, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.neg_mulVec, Matrix.smul_mulVec]
  have hLip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : EuclideanSpace ℝ (Fin P), ‖x‖ ≤ A → ‖y‖ ≤ A →
      ‖V x - V y‖ ≤ K * ‖x - y‖ := fun A =>
    ⟨‖matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J))‖, norm_nonneg _, fun x y _ _ => by
      rw [hVsub]; exact (matrixCLM (-(m : ℝ)⁻¹ • (Jᵀ * J))).le_opNorm _⟩
  have hsolc : ContinuousOn (fun s : ℝ => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))) (Set.Ici 0) :=
    fun s _ => (hasDerivAt_affineFlowSolution J hG r₀ s).continuousAt.continuousWithinAt
  have h0 : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(0 / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp)) = 0 := by
    have := matrix_exp_residual_trajectory_zero (J * Jᵀ) r₀
    rw [show -(0 / (m : ℝ)) = -(0 * (m : ℝ)⁻¹) by ring, this, sub_self, map_zero]
  exact forwardFlow_unique V hLip hwc (fun s hs => hw s hs) hsolc
    (fun s _ => hasDerivAt_affineFlowSolution J hG r₀ s) (by rw [hw0, h0]) ht


/-- **The affine flow converges to the minimum-norm interpolant.** If the Gram matrix `J Jᵀ` is
positive definite, the closed-form affine flow `w(t)` converges to `w∞ = -Jᵀ (J Jᵀ)⁻¹ r₀`, with
exponential rate `λ_min(J Jᵀ) / m`; the limit interpolates (`J w∞ = -r₀`) and has least norm
(`norm_affine_limit_le`). -/
theorem tendsto_affineFlowSolution (hm : 0 < m) (J : Matrix (Fin m) (Fin P) ℝ)
    (hG : (J * Jᵀ).PosDef) (r₀ : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun t : ℝ => matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ -
      WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp))) atTop
      (𝓝 (matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀)) := by
  obtain ⟨c, hc, hcgap⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hG
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef _ c hcgap
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_zero_of_le_mul_exp_neg (L₀ := ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖r₀‖)
    (c := c / m) (by positivity) (fun t _ => norm_nonneg _) fun t ht => ?_
  set res : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (NormedSpace.exp (-(t / (m : ℝ)) • (J * Jᵀ)) *ᵥ r₀.ofLp) with hres
  have hdiff : matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) (r₀ - res) - matrixCLM (-(Jᵀ * (J * Jᵀ)⁻¹)) r₀ =
      matrixCLM (Jᵀ * (J * Jᵀ)⁻¹) res := by
    rw [← map_sub, sub_sub_cancel_left, map_neg]
    ext i : 1
    simp [matrixCLM_apply, Matrix.neg_mulVec]
  rw [hdiff]
  calc ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹) res‖ ≤ ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖res‖ :=
        (matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)).le_opNorm _
    _ ≤ ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * (‖r₀‖ * Real.exp (-(c / (m : ℝ)) * t)) := by
        gcongr
        exact matrix_exp_residual_decay (J * Jᵀ) r₀ c hrr hmR t ht
    _ = ‖matrixCLM (Jᵀ * (J * Jᵀ)⁻¹)‖ * ‖r₀‖ * Real.exp (-(c / (m : ℝ)) * t) := by ring

/-! ### Test-Point Prediction Along a Gradient Flow

For a test input `x`, the linearized output change `⟪∇_θ f(x; θ₀), θ(t) - θ₀⟫` is compared with the
frozen-kernel prediction `-a ⬝ᵥ (r₀ - exp(-(t/m) K_∞) r₀)`, where `K_∞ a = k_∞` (`a = K_∞⁻¹ k_∞`
when `K_∞` is invertible). The comparison is a mean-value estimate whose pointwise derivative bound
involves only three drifts: Jacobian, cross-kernel `J(θ₀) ∇_θ f(x; θ₀)`, and residual versus the
matrix exponential (`residual_sub_matrix_exp_le`). -/

/-- Derivative along the flow of the test-feature projection of the displacement. -/
lemma hasDerivAt_inner_tangentFeature_displacement
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (g θ₀ : EuclideanSpace ℝ (Fin P)) {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)} {t : ℝ}
    (hflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj t)) t)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => ⟪g, θ_traj s - θ₀⟫)
      (-(m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual f X y (θ_traj t) α *
        ⟪g, tangentFeature f (X α) (θ_traj t)⟫) t := by
  have h := (hasDerivAt_const t g).inner ℝ (hflow.sub_const θ₀)
  refine h.congr_deriv ?_
  rw [gradient_mseLoss f X y _ hdiff]
  simp [inner_neg_right, inner_smul_right, inner_sum, Finset.mul_sum]

/-- Derivative of the frozen-kernel prediction curve `s ↦ -a ⬝ᵥ (r₀ - exp(-(s/m) K_inf) r₀)`, where
`K_inf` is symmetric and `K_inf a = k_inf`: it equals `-(1/m) k_inf ⬝ᵥ exp(-(s/m) K_inf) r₀`. -/
lemma hasDerivAt_frozenPrediction (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK : K_inf.IsHermitian)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) (r₀ : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    HasDerivAt (fun u : ℝ => -(a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)))
      (-(m : ℝ)⁻¹ * (k_inf ⬝ᵥ (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) s := by
  have hρ := matrix_exp_residual_trajectory_hasDerivAt K_inf r₀ s
  have h := ((hasDerivAt_const s (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m))).inner ℝ hρ).sub_const
    (a ⬝ᵥ r₀.ofLp)
  have hfun : (fun u : ℝ => -(a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) = fun u : ℝ =>
      ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)),
        (WithLp.toLp 2 (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))⟫ - a ⬝ᵥ r₀.ofLp := by
    funext u
    have hin : ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)),
        (WithLp.toLp 2 (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))⟫ =
        a ⬝ᵥ (NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) := by
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    rw [hin, dotProduct_sub]
    ring
  rw [hfun]
  refine h.congr_deriv ?_
  have hKt : K_infᵀ = K_inf := hK
  set v : Fin m → ℝ := NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp with hv
  have hin : ∀ u : Fin m → ℝ, ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), WithLp.toLp 2 u⟫ =
      a ⬝ᵥ u := fun u => by simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hin, inner_zero_left, add_zero, dotProduct_smul, Matrix.dotProduct_mulVec, smul_eq_mul]
  have : a ᵥ* K_inf = k_inf := by
    rw [← hKa, ← Matrix.vecMul_transpose, hKt]
  rw [this]

/-- Cauchy-Schwarz for the dot product of two vectors of `Fin m → ℝ`. -/
lemma abs_dotProduct_le_norm_mul_norm (u v : Fin m → ℝ) :
    |u ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m))‖ *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m)) (WithLp.toLp 2 v)
  simpa [PiLp.inner_apply, dotProduct, mul_comm] using this

/-- **Pointwise derivative of the test-point prediction error.** Along a gradient flow, the error
curve `e(s) = ⟪g, θ(s) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(s/m) K_inf) r₀)` (with `K_inf` symmetric and
`K_inf a = k_inf`) is differentiable at `c` with `|e'(c)| ≤ (1/m) (‖r(c)‖ (‖g‖ ‖J(θ(c)) - J(θ₀)‖ +
ε_k) + ‖k_inf‖ ‖r(c) - exp(-(c/m) K_inf) r₀‖)`, where `ε_k` bounds `‖J(θ₀) g - k_inf‖`. The three
terms are the Jacobian drift, the cross-kernel error and the residual-versus-frozen-exponential
error; the estimate uses no smallness beyond them. -/
lemma hasDerivAt_predictionError_abs_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (g : EuclideanSpace ℝ (Fin P)) (K_inf : Matrix (Fin m) (Fin m) ℝ) (hKsymm : K_inf.IsHermitian)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) (r₀ : EuclideanSpace ℝ (Fin m)) {c : ℝ}
    (hcflow : HasDerivAt θ_traj (-gradient (mseLoss f X y) (θ_traj c)) c)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj c)) {ε_k : ℝ}
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k) :
    ∃ e' : ℝ, HasDerivAt (fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) e' c ∧
      |e'| ≤ (m : ℝ)⁻¹ * (‖trainingResidual f X y (θ_traj c)‖ *
          (‖g‖ * ‖outputJacobian f X (θ_traj c) - outputJacobian f X θ₀‖ + ε_k) +
        ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
          ‖trainingResidual f X y (θ_traj c) -
            WithLp.toLp 2 (NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖) := by
  have hd1 := hasDerivAt_inner_tangentFeature_displacement f X y g θ₀ hcflow hdiff
  have hd2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ c).neg
  have hd2' : HasDerivAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
      NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))
      ((m : ℝ)⁻¹ * (k_inf ⬝ᵥ (NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp))) c := by
    convert hd2 using 1
    · funext u
      simp
    · ring
  refine ⟨_, hd1.add hd2', ?_⟩
  set rc : EuclideanSpace ℝ (Fin m) := trainingResidual f X y (θ_traj c) with hrc
  have hsum : ∑ α : Fin m, rc α * ⟪g, tangentFeature f (X α) (θ_traj c)⟫ =
      rc.ofLp ⬝ᵥ (outputJacobian f X (θ_traj c) *ᵥ g.ofLp) := by
    simp only [dotProduct, Matrix.mulVec, outputJacobian, Matrix.of_apply, tangentFeature,
      PiLp.inner_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
  rw [hsum]
  set Jc := outputJacobian f X (θ_traj c) with hJc
  set J₀ := outputJacobian f X θ₀ with hJ₀
  set ρv : Fin m → ℝ := NormedSpace.exp (-(c / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp with hρv
  have hdec : rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv =
      rc.ofLp ⬝ᵥ ((Jc - J₀) *ᵥ g.ofLp) + rc.ofLp ⬝ᵥ (J₀ *ᵥ g.ofLp - k_inf) +
        k_inf ⬝ᵥ (rc.ofLp - ρv) := by
    simp only [Matrix.sub_mulVec, dotProduct_sub, dotProduct_comm k_inf rc.ofLp]
    ring
  have hrcv : (WithLp.toLp 2 rc.ofLp : EuclideanSpace ℝ (Fin m)) = rc := rfl
  have b1 : |rc.ofLp ⬝ᵥ ((Jc - J₀) *ᵥ g.ofLp)| ≤ ‖rc‖ * (‖g‖ * ‖Jc - J₀‖) := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
    rw [hrcv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (mulVec_frobenius_norm_le (Jc - J₀) g).trans (le_of_eq (mul_comm _ _))
  have b2 : |rc.ofLp ⬝ᵥ (J₀ *ᵥ g.ofLp - k_inf)| ≤ ‖rc‖ * ε_k := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
    rw [hrcv]
    refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hk) (norm_nonneg _)
    congr 1
  have b3 : |k_inf ⬝ᵥ (rc.ofLp - ρv)| ≤ ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
      ‖rc - WithLp.toLp 2 ρv‖ := by
    refine (abs_dotProduct_le_norm_mul_norm _ _).trans (le_of_eq ?_)
    congr 2
  have hkey : |rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv| ≤
      ‖rc‖ * (‖g‖ * ‖Jc - J₀‖ + ε_k) + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
        ‖rc - WithLp.toLp 2 ρv‖ := by
    rw [hdec]
    refine (abs_add_three _ _ _).trans ?_
    nlinarith [b1, b2, b3]
  have hexp : -(m : ℝ)⁻¹ * (rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp)) + (m : ℝ)⁻¹ * (k_inf ⬝ᵥ ρv) =
      -(m : ℝ)⁻¹ * (rc.ofLp ⬝ᵥ (Jc *ᵥ g.ofLp) - k_inf ⬝ᵥ ρv) := by ring
  rw [hexp, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hm)]
  exact mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hm.le)

/-- **Deterministic test-point prediction error along a gradient flow.** Let `θ(t)` be a forward
gradient flow of the MSE loss of `f` on `X`, `g = ∇_θ f(x; θ₀)` the tangent feature at a test input
`x`, `r₀` the initial residual, and `K_inf`, `k_inf` a symmetric positive semidefinite kernel matrix
and cross-kernel vector with `K_inf a = k_inf`. If on `[0, T]` the Jacobian stays within `ε_J` of
`J(θ₀)`, the empirical kernel within `ε_K` of `K_inf`, and `J(θ₀) g` within `ε_k` of `k_inf`, then
for
`t ∈ [0, T]`
`|⟪g, θ(t) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(t/m) K_inf) r₀)| ≤ t m⁻¹ (‖g‖ ε_J ‖r₀‖ + ε_k ‖r₀‖ +
‖k_inf‖ m⁻¹ ε_K ‖r₀‖ T)`.
With `a = K_inf⁻¹ k_inf` this says the linearized output change `⟪g, θ(t) - θ₀⟫` equals the
kernel-regression prediction `k_inf K_inf⁻¹ (I - exp(-(t/m) K_inf)) (y - f₀)` up to the stated
error.
The proof is a mean-value estimate on the error curve, whose derivative is bounded pointwise by the
three drifts (Jacobian, cross-kernel, residual-vs-exponential); no integral formula is used. -/
theorem abs_inner_displacement_add_frozenPrediction_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (g : EuclideanSpace ℝ (Fin P)) {T : ℝ} (hT : 0 ≤ T)
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK_inf : K_inf.PosSemidef)
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) {ε_J ε_K ε_k : ℝ}
    (hJ : ∀ s ∈ Set.Icc 0 T, ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤ ε_J)
    (hK : ∀ s ∈ Set.Icc 0 T, ‖empiricalNTKMatrix f X (θ_traj s) - K_inf‖ ≤ ε_K)
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      |⟪g, θ_traj t - θ₀⟫ + a ⬝ᵥ ((trainingResidual f X y θ₀).ofLp -
          NormedSpace.exp (-(t / (m : ℝ)) • K_inf) *ᵥ (trainingResidual f X y θ₀).ofLp)| ≤
        t * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖trainingResidual f X y θ₀‖ +
          ε_k * ‖trainingResidual f X y θ₀‖ + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
            ((m : ℝ)⁻¹ * (ε_K * ‖trainingResidual f X y θ₀‖) * T))) := by
  set r₀ := trainingResidual f X y θ₀ with hr₀
  set r : ℝ → EuclideanSpace ℝ (Fin m) := fun s => trainingResidual f X y (θ_traj s) with hr
  have hKsymm : K_inf.IsHermitian := hK_inf.isHermitian
  have hrc : ContinuousOn r (Set.Icc 0 T) :=
    (continuousOn_trainingResidual_comp f X y (s := Set.Icc 0 T)
      (hflow.continuousOn.mono Set.Icc_subset_Ici_self) fun t _ => hdiff t)
  have hr_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ •
      ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (r t).ofLp))) t := fun t ht =>
    gradient_flow_residual_vector_ode f X y t (hflow.ode t ht.1) (hdiff t)
  have hK_psd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v : EuclideanSpace ℝ (Fin m),
      0 ≤ v.ofLp ⬝ᵥ (empiricalNTKMatrix f X (θ_traj s) *ᵥ v.ofLp) := fun s _ v => by
    simpa using dotProduct_mulVec_nonneg_of_posSemidef
      (empiricalNTKMatrix_posSemidef f X (θ_traj s)) v
  have hr0 : r 0 = r₀ := by simp [hr, hr₀, hflow.init]
  have hrnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖r s‖ ≤ ‖r₀‖ := fun s hs => by
    have h := residual_norm_exponential_decay_timeVarying_Icc
      (fun s => empiricalNTKMatrix f X (θ_traj s)) 0 T hT r
      (fun s hs v => by simpa using hK_psd s hs v) hrc hr_ode hm s hs
    simpa [hr0] using h
  have hres := residual_sub_matrix_exp_le (fun s => empiricalNTKMatrix f X (θ_traj s)) K_inf r hT hm
    hrc hr_ode hK_psd (fun v => by simpa using dotProduct_mulVec_nonneg_of_posSemidef hK_inf v) hK
  set ρ : ℝ → EuclideanSpace ℝ (Fin m) := fun s =>
    WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with hρ
  set C : ℝ := (m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
    ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T)) with hC
  -- the error curve
  set e : ℝ → ℝ := fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
    NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with he
  have he0 : e 0 = 0 := by
    simp [he, hflow.init]
  have hecont : ContinuousOn e (Set.Icc 0 T) := by
    intro s hs
    have h1 : ContinuousWithinAt (fun s => ⟪g, θ_traj s - θ₀⟫) (Set.Icc 0 T) s :=
      ((continuous_const.inner (continuous_id.sub continuous_const)).comp_continuousOn
        (hflow.continuousOn.mono Set.Icc_subset_Ici_self)) s hs
    have h2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ s).continuousAt
    have h2' : ContinuousAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) s := by
      convert h2.neg using 1
      funext u
      simp
    exact h1.add h2'.continuousWithinAt
  have hεK : 0 ≤ ε_K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  have hεJ : 0 ≤ ε_J := (norm_nonneg _).trans (hJ 0 ⟨le_rfl, hT⟩)
  have hεk : 0 ≤ ε_k := (norm_nonneg _).trans hk
  -- pointwise derivative bound
  have hbound : ∀ c ∈ Set.Ioo (0 : ℝ) T, ∃ e' : ℝ, HasDerivAt e e' c ∧ |e'| ≤ C := by
    intro c hc
    have hcI : c ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hc
    obtain ⟨e', hde, hbe⟩ := hasDerivAt_predictionError_abs_le f X y hm g K_inf hKsymm a k_inf hKa
      r₀ (hflow.ode c hc.1) (hdiff c) hk
    refine ⟨e', hde, hbe.trans ?_⟩
    have hres' := hres c hcI
    rw [hr0] at hres'
    have hrc_norm : ‖r c‖ ≤ ‖r₀‖ := hrnorm c hcI
    have hJc := hJ c hcI
    have hres'' : ‖r c - ρ c‖ ≤ (m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T :=
      hres'.trans (mul_le_mul_of_nonneg_left hc.2.le (by positivity))
    rw [hC]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
    have hg0 := norm_nonneg g
    have hkn := norm_nonneg (WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))
    calc ‖r c‖ * (‖g‖ * ‖outputJacobian f X (θ_traj c) - outputJacobian f X θ₀‖ + ε_k) +
          ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ * ‖r c - ρ c‖
        ≤ ‖r₀‖ * (‖g‖ * ε_J + ε_k) + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
          ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * T) := by
          gcongr
      _ = _ := by ring
  intro t ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have := he0
    simp only [he] at this ⊢
    simpa using this
  · choose! e' he' hb using hbound
    obtain ⟨c, hc, hcs⟩ :=
      exists_hasDerivAt_eq_slope e e' hpos (hecont.mono (Set.Icc_subset_Icc_right ht.2))
      (fun x hx => he' x ⟨hx.1, hx.2.trans_le ht.2⟩)
    have hct : |e' c| ≤ C := hb c ⟨hc.1, hc.2.trans_le ht.2⟩
    have : e t = e' c * t := by
      rw [he0, sub_zero, sub_zero] at hcs
      field_simp at hcs
      linarith
    change |e t| ≤ t * C
    rw [this, abs_mul, abs_of_pos hpos, mul_comm]
    exact mul_le_mul_of_nonneg_left hct hpos.le

/-- **Exponentially decaying derivative gives a small tail.** If `e` is continuous on `[S, ∞)` and
differentiable on `(S, ∞)` with `|e'(s)| ≤ B exp(-ν s)`, `ν > 0`, then for every `t ≥ S`,
`|e t - e S| ≤ (B / ν) exp(-ν S)`. -/
lemma abs_sub_le_of_abs_deriv_le_exp {e : ℝ → ℝ} {S B ν : ℝ} (hν : 0 < ν)
    (hec : ContinuousOn e (Set.Ici S))
    (hd : ∀ s, S < s → ∃ e' : ℝ, HasDerivAt e e' s ∧ |e'| ≤ B * Real.exp (-ν * s))
    {t : ℝ} (ht : S ≤ t) : |e t - e S| ≤ B / ν * Real.exp (-ν * S) := by
  have hexp : ∀ s, HasDerivAt (fun s => B / ν * Real.exp (-ν * s)) (-(B * Real.exp (-ν * s))) s :=
    fun s => by
      have := ((hasDerivAt_id s).const_mul (-ν)).exp.const_mul (B / ν)
      refine this.congr_deriv ?_
      simp only [id_eq]
      field_simp
  have hcexp : Continuous fun s => B / ν * Real.exp (-ν * s) := by fun_prop
  have hdiff : DifferentiableOn ℝ e (interior (Set.Ici S)) := fun s hs => by
    rw [interior_Ici] at hs
    obtain ⟨e', he', -⟩ := hd s hs
    exact he'.differentiableAt.differentiableWithinAt
  -- antitone: e + (B/ν) exp(-ν ·)
  have hanti : AntitoneOn (fun s => e s + B / ν * Real.exp (-ν * s)) (Set.Ici S) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici S) (hec.add hcexp.continuousOn)
      (hdiff.add (fun s _ => (hexp s).differentiableAt.differentiableWithinAt)) fun s hs => ?_
    rw [interior_Ici] at hs
    obtain ⟨e', he', hb⟩ := hd s hs
    have h : HasDerivAt (fun s => e s + B / ν * Real.exp (-ν * s))
        (e' + -(B * Real.exp (-ν * s))) s := he'.add (hexp s)
    rw [h.deriv]
    linarith [(abs_le.1 hb).2]
  have hmono : MonotoneOn (fun s => e s - B / ν * Real.exp (-ν * s)) (Set.Ici S) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici S) (hec.sub hcexp.continuousOn)
      (hdiff.sub (fun s _ => (hexp s).differentiableAt.differentiableWithinAt)) fun s hs => ?_
    rw [interior_Ici] at hs
    obtain ⟨e', he', hb⟩ := hd s hs
    have h : HasDerivAt (fun s => e s - B / ν * Real.exp (-ν * s))
        (e' - -(B * Real.exp (-ν * s))) s := he'.sub (hexp s)
    rw [h.deriv]
    linarith [(abs_le.1 hb).1]
  have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have h2 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hpos : 0 ≤ B / ν * Real.exp (-ν * t) := by
    have : 0 ≤ B := by
      obtain ⟨e', -, hb⟩ := hd (S + 1) (by linarith)
      exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans hb)
    positivity
  rw [abs_le]
  simp only at h1 h2
  constructor <;> nlinarith

/-- **Uniform-in-time prediction error under exponential residual decay.** Suppose, in addition to
the hypotheses of `abs_inner_displacement_add_frozenPrediction_le` on a window `[0, S]`, that the
Jacobian drift is bounded by `ε_J` for *all* times, the residual decays like
`‖r(s)‖ ≤ ‖r₀‖ exp(-ν s)`, and `K_inf` has a spectral gap `lam` with `ν ≤ lam / m`. Then for every
`t ≥ 0`, the prediction error `|⟪g, θ(t) - θ₀⟫ + a ⬝ᵥ (r₀ - exp(-(t/m) K_inf) r₀)|` is at most the
finite-window bound `S m⁻¹ (‖g‖ ε_J ‖r₀‖ + ε_k ‖r₀‖ + ‖k_inf‖ m⁻¹ ε_K ‖r₀‖ S)` plus the tail
`(m⁻¹ ‖r₀‖ (‖g‖ ε_J + ε_k + 2 ‖k_inf‖) / ν) exp(-ν S)`. On `[0, S]` this is the finite-time
theorem; beyond `S` the error curve has derivative bounded by a multiple of `exp(-ν s)` (residual
and frozen residual both decay), so it moves by at most the tail
(`abs_sub_le_of_abs_deriv_le_exp`). -/
theorem abs_inner_displacement_add_frozenPrediction_le_of_exp_decay
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    (hm : 0 < (m : ℝ)) {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : ForwardGFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (g : EuclideanSpace ℝ (Fin P)) {S : ℝ} (hS : 0 ≤ S)
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (hK_inf : K_inf.PosSemidef) {lam : ℝ}
    (hlam : ∀ v : EuclideanSpace ℝ (Fin m), lam * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (a k_inf : Fin m → ℝ) (hKa : K_inf *ᵥ a = k_inf) {ε_J ε_K ε_k ν : ℝ} (hν : 0 < ν)
    (hνlam : ν ≤ lam / m)
    (hJ : ∀ s : ℝ, 0 ≤ s → ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤ ε_J)
    (hK : ∀ s ∈ Set.Icc 0 S, ‖empiricalNTKMatrix f X (θ_traj s) - K_inf‖ ≤ ε_K)
    (hk : ‖(WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ g.ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 k_inf‖ ≤ ε_k)
    (hr : ∀ s : ℝ, 0 ≤ s → ‖trainingResidual f X y (θ_traj s)‖ ≤
      ‖trainingResidual f X y θ₀‖ * Real.exp (-ν * s)) :
    ∀ t : ℝ, 0 ≤ t →
      |⟪g, θ_traj t - θ₀⟫ + a ⬝ᵥ ((trainingResidual f X y θ₀).ofLp -
          NormedSpace.exp (-(t / (m : ℝ)) • K_inf) *ᵥ (trainingResidual f X y θ₀).ofLp)| ≤
        S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖trainingResidual f X y θ₀‖ +
          ε_k * ‖trainingResidual f X y θ₀‖ + ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ *
            ((m : ℝ)⁻¹ * (ε_K * ‖trainingResidual f X y θ₀‖) * S))) +
        ((m : ℝ)⁻¹ * ‖trainingResidual f X y θ₀‖ * (‖g‖ * ε_J + ε_k +
          2 * ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖)) / ν * Real.exp (-ν * S) := by
  set r₀ := trainingResidual f X y θ₀ with hr₀
  set kn : ℝ := ‖(WithLp.toLp 2 k_inf : EuclideanSpace ℝ (Fin m))‖ with hkn
  have hKsymm : K_inf.IsHermitian := hK_inf.isHermitian
  have hfin := abs_inner_displacement_add_frozenPrediction_le f X y hm hflow hdiff g hS K_inf hK_inf
    a k_inf hKa (fun s hs => hJ s hs.1) hK hk
  set e : ℝ → ℝ := fun s => ⟪g, θ_traj s - θ₀⟫ + a ⬝ᵥ (r₀.ofLp -
    NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) with he
  have hεJ : 0 ≤ ε_J := (norm_nonneg _).trans (hJ 0 le_rfl)
  have hεk : 0 ≤ ε_k := (norm_nonneg _).trans hk
  have hεK : 0 ≤ ε_K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hS⟩)
  have hr0n := norm_nonneg r₀
  have hkn0 : 0 ≤ kn := norm_nonneg _
  have hg0 := norm_nonneg g
  set Bc : ℝ := (m : ℝ)⁻¹ * ‖r₀‖ * (‖g‖ * ε_J + ε_k + 2 * kn) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have hecont : ContinuousOn e (Set.Ici 0) := by
    intro s hs
    have h1 : ContinuousWithinAt (fun s => ⟪g, θ_traj s - θ₀⟫) (Set.Ici 0) s :=
      ((continuous_const.inner (continuous_id.sub continuous_const)).comp_continuousOn
        hflow.continuousOn) s hs
    have h2 := (hasDerivAt_frozenPrediction K_inf hKsymm a k_inf hKa r₀ s).continuousAt
    have h2' : ContinuousAt (fun u : ℝ => a ⬝ᵥ (r₀.ofLp -
        NormedSpace.exp (-(u / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)) s := by
      convert h2.neg using 1
      funext u
      simp
    exact h1.add h2'.continuousWithinAt
  have hSfin : |e S| ≤ S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
      kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) := hfin S ⟨hS, le_rfl⟩
  have htail : ∀ t, S ≤ t → |e t - e S| ≤ Bc / ν * Real.exp (-ν * S) := fun t ht =>
    abs_sub_le_of_abs_deriv_le_exp hν (hecont.mono (Set.Ici_subset_Ici.2 hS)) (fun s hs => by
      have hs0 : 0 ≤ s := hS.trans hs.le
      obtain ⟨e', hde, hbe⟩ := hasDerivAt_predictionError_abs_le f X y hm g K_inf hKsymm a k_inf
        hKa r₀ (hflow.ode s (hS.trans_lt hs)) (hdiff s) hk
      refine ⟨e', hde, hbe.trans ?_⟩
      have hrs := hr s hs0
      have hρs : ‖(WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp) :
          EuclideanSpace ℝ (Fin m))‖ ≤ ‖r₀‖ * Real.exp (-ν * s) :=
        (matrix_exp_residual_decay K_inf r₀ lam hlam hm s hs0).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hνlam)])) hr0n)
      have hdiffn : ‖trainingResidual f X y (θ_traj s) -
          WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖ ≤
          2 * (‖r₀‖ * Real.exp (-ν * s)) :=
        (norm_sub_le _ _).trans (by linarith)
      have hJs := hJ s hs0
      have hexp0 := Real.exp_pos (-ν * s)
      calc (m : ℝ)⁻¹ * (‖trainingResidual f X y (θ_traj s)‖ *
            (‖g‖ * ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ + ε_k) +
          kn * ‖trainingResidual f X y (θ_traj s) -
            WithLp.toLp 2 (NormedSpace.exp (-(s / (m : ℝ)) • K_inf) *ᵥ r₀.ofLp)‖)
          ≤ (m : ℝ)⁻¹ * (‖r₀‖ * Real.exp (-ν * s) * (‖g‖ * ε_J + ε_k) +
            kn * (2 * (‖r₀‖ * Real.exp (-ν * s)))) := by
            gcongr
        _ = Bc * Real.exp (-ν * s) := by rw [hBc]; ring) ht
  intro t ht
  by_cases hts : t ≤ S
  · refine (hfin t ⟨ht, hts⟩).trans ?_
    have hbr : 0 ≤ (m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S)) := by positivity
    have : t * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) ≤ S * ((m : ℝ)⁻¹ * (‖g‖ * ε_J * ‖r₀‖ + ε_k * ‖r₀‖ +
        kn * ((m : ℝ)⁻¹ * (ε_K * ‖r₀‖) * S))) := mul_le_mul_of_nonneg_right hts hbr
    have htl : 0 ≤ Bc / ν * Real.exp (-ν * S) := by positivity
    linarith
  · have hSt : S ≤ t := (not_le.1 hts).le
    have h1 := htail t hSt
    have h2 : |e t| ≤ |e S| + |e t - e S| := by
      have := abs_add_le (e S) (e t - e S)
      simpa using this
    exact h2.trans (add_le_add hSfin h1)

end NTK

end
