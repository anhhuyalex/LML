/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Dynamics
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Convergence
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.LinearDynamics
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.KernelStability
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Bootstrap
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.InfiniteWidth
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.ODEStability
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.AffineDynamics
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.TestPrediction

/-!
# The Infinite-Width NTK Regime and Linearized Dynamics

This file formalizes the infinite-width Neural Tangent Kernel (NTK) regime and its exact
linearized training dynamics, corresponding to Jacot et al. (2018) and Lee et al. (2019).

## Structure

The development is a chain of modules in `GradientFlow/`, each importing the previous one; this
file re-exports all of them.  The generic ODE tools (Grönwall, `le_of_forall_bootstrap`,
`exists_global_flow`) are in `NTK.Foundations.ODE`.

* `Dynamics` : residual ODE, general losses, risk dissipation, kinetic energy.
* `Convergence` : exponential convergence of the training loss.
* `LinearDynamics` : closed-form dynamics via the matrix exponential, eigenmodes.
* `KernelStability` : Lipschitz propagation for the empirical NTK, Taylor bound, Rayleigh stability.
* `Bootstrap` : displacement-integral bound and the continuous-induction bootstrap.
* `InfiniteWidth` : asymptotic properties in the infinite-width limit.
* `ODEStability` : stability of linear ODEs under coefficient perturbation.
* `AffineDynamics` : fixed-feature (affine) dynamics and minimum norm.
* `TestPrediction` : test-point prediction along a gradient flow.

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
    `shallowEmpiricalNTK σ' (fun j : Fin n => rows j.val) x x' → shallowLimitingNTK σ' x x'`
    almost surely and in probability.
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
  and its instance for the training outputs under an `L`-Lipschitz output Jacobian (test-input
linearization error).
* `NTK.minNorm_pythagoras`, `NTK.matrixCLM_transpose_eq_adjoint` : minimum-norm Pythagoras for any
  bounded linear map between real Hilbert spaces, and the adjoint identity for `matrixCLM`.
* `NTK.matrixCLM`, `NTK.inner_matrixCLM_transpose`, `NTK.hasDerivAt_affineFlowSolution`,
  `NTK.affineFlow_eq_solution`, `NTK.affine_minNorm_pythagoras`, `NTK.norm_affine_limit_le`,
  `NTK.eq_affine_limit_of_norm_le`, `NTK.tendsto_affineFlowSolution`, `NTK.inner_affine_limit` :
  For an arbitrary matrix `J` with invertible Gram matrix `J Jᵀ`, the closed form of
  the affine gradient flow, its convergence to the minimum-norm interpolant `-Jᵀ (J Jᵀ)⁻¹ r₀`,
  the Pythagoras identity proving minimality, and the kernel-regression form of its prediction.
* `NTK.hasDerivAt_predictionError_abs_le`, `NTK.abs_inner_displacement_add_frozenPrediction_le`,
  `NTK.abs_sub_le_of_abs_deriv_le_exp`,
  `NTK.abs_inner_displacement_add_frozenPrediction_le_of_exp_decay` : Deterministic
  test-point prediction error along a gradient flow, on a finite window and uniformly in time under
  exponential residual decay.
* `NTK.norm_sq_gradient_generalizedRisk`, `NTK.norm_sq_gradient_mseLoss`,
  `NTK.norm_deriv_sq_eq_quadratic_form_of_forwardGF`, `NTK.mseLoss_sub_eq_integral_quadratic_form` :
  Kinetic energy: `‖∇L‖² = (1/m²) rᵀ K r`, `‖θ'‖² = (1/m²) rᵀ K r` along the forward flow,
  and `L(θ 0) - L(θ T) = ∫₀ᵀ (1/m²) rᵀ K r = ∫₀ᵀ ‖θ'‖²` (generic part in
  `ConvexOpt.ForwardGFTrajectory`).
* `NTK.hasDerivAt_coord_of_forwardGF` : Coordinate form `∂_t θ_k = -(1/m) [Jᵀ r]_k` of the
  training flow (the `a_i` and `W_{ij}` equations are in `NTK.Training.TwoLayer.Packing`).
* `NTK.matrix_exp_smul_mulVec_of_eigenvector`, `NTK.inner_matrix_exp_mulVec_of_eigenvector`,
  `NTK.inner_eigenvectorBasis_matrix_exp_mulVec`, `NTK.matrix_exp_mulVec_eq_sum_eigenmodes`,
  `NTK.norm_sq_matrix_exp_mulVec_eq_sum`, `NTK.abs_inner_eigenvector_residual_sub_mode_le` :
  Eigenmodes `⟪v_k, r(t)⟫ = exp(-λ_k t / m) ⟪v_k, r(0)⟫` of the frozen-kernel residual
  (Mathlib's `Matrix.IsHermitian.eigenvectorBasis`), Parseval energy, and the lazy-training
  comparison for the actual residual.
* `NTK.tendsto_zero_of_le_mul_exp_neg` : exponential bound implies convergence to zero.
* `NTK.exists_forward_flow`, `NTK.forwardFlow_unique`, `NTK.lipschitz_on_ball_of_locallyLipschitz` :
  Generic forward-time flow of a field that is Lipschitz on balls and has a priori
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
* `NTK.norm_sub_le_of_linear_ode_perturbation` : **Generic** stability of `r' = -A(t) r`
  against `s' = -B(t) s` for PSD `A`: `‖r - s‖ ≤ ‖r(0) - s(0)‖ + a t` if `‖A - B‖ ‖s‖ ≤ a`.
* `NTK.residual_sub_frozen_residual_le` : Specialization to the NTK residual dynamics with
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
* `NTK.empiricalNTKMatrix_lipschitz_of_jacobian_bound` : Deterministic
  Lipschitz propagation on any set `S` around `θ₀`.
* `NTK.empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound` : Kernel freeze bound
  `‖K(θ(t)) - K(θ₀)‖ ≤ (2 * M * L_J) * C` instantiated with Jacobian bounds
  (the `1/√n` decay lives in `L_J`, not in the displacement bound `C` - see
  `NTK.Shallow.DatasetNTK`'s `gradient_mseLoss_norm_le` and this file's Rayleigh-quotient stability
  theorems below).
* `NTK.abs_dotProduct_mulVec_sub_le` : Quadratic forms of nearby matrices are close:
  `|vᵀ A v - vᵀ B v| ≤ ‖A - B‖ ‖v‖²`.
* `NTK.rayleigh_lower_bound_of_sub_smul_posSemidef` : Shifted positive semidefiniteness implies
  a Rayleigh-quotient lower bound: `(K - λ • 1).PosSemidef ⟹ λ ‖v‖² ≤ vᵀ K v`.
* `NTK.rayleigh_quotient_lower_bound_of_matrix_dist` : Rayleigh-quotient stability under a
  matrix distance bound `‖K - K₀‖ ≤ ε`.
* `NTK.rayleigh_quotient_lower_bound_of_displacement` : a spectral gap `lambda_min₀` of the kernel
  at `θ₀` gives a gap `lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖` at any `θ`, when the Jacobian has
  Frobenius norm at most `M` at `θ₀` and `θ` and changes by at most `L_J * ‖θ - θ₀‖` between them.
  This is the input the lazy-training bootstrap needs at every `θ` near `θ₀`.
* `NTK.restrictCoords`, `NTK.norm_restrictCoords_gradient_mseLoss_le`,
  `NTK.norm_map_sub_le_integral_of_forwardGF` : displacement of a *block of coordinates* (or any
  continuous linear image) of a gradient flow is at most the integral of the speed of that block;
  the block speed under MSE flow is `(1/m) ‖J_block‖ ‖r‖`.
* `NTK.integral_exp_neg_le` : Reusable bound `∫₀ᵀ exp(-c t) dt ≤ 1/c` for `c > 0`.
* `NTK.displacement_integral_bound` : A `T`-independent displacement
  cap `(M * ‖r₀‖) / lambda_min` given a uniform-in-time Rayleigh bound on `[0, T]`.
* `NTK.lazy_training_displacement_bound` : The continuous-induction
  bootstrap discharging `hlazy` with a width-independent constant `C`.
* `NTK.lazy_training_kernel_freeze_bound` : Step 2 kernel freeze bound under lazy training.
* `NTK.tendsto_lazy_training_kernel_freeze` : Asymptotic freeze limit as `n → ∞`.
* `NTK.tendsto_lazy_training_kernel_freeze_matrix` : Empirical NTK matrix freeze as `n → ∞`.
* `NTK.deterministic_initialization_empiricalNTKMatrix_tendsto_ae` : Property 1 a.s. Gram matrix
  limit (entrywise `NTK.ntk_convergence`).
* `NTK.deterministic_initialization_chebyshev_bound` : Property 1 entrywise Chebyshev bound.
* `NTK.tendsto_shallowEmpiricalNTK_chebyshev_bound` : Property 1 Chebyshev tail decay in ENNReal.

-/
