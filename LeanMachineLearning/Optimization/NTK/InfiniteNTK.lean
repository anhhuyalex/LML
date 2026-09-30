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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (-⟪tangentFeature f (X α) (θ_traj t),
        gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj t)⟫) t := by
  have h := hasDerivAt_trainingOutputs_coord f X θ_traj
    (fun s => -gradient (generalizedEmpiricalRisk ℓ f X y) (θ_traj s)) t α hdiff (hflow.ode t)
  rw [inner_neg_right] at h
  exact h

/-- Step 3 (Insertion of Generalized Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1/m) ∑_β r^β(t) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - (1/m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ r^β(t)`. -/
theorem gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner
    (ℓ : ℝ → ℝ → ℝ) (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad ℓ f X y hflow t α (hf α)
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
        (generalizedResidual ℓ f X y (θ_traj t)) β) t := by
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner ℓ f X y hflow t α hf hℓ
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj) (t : ℝ)
    (hf : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (hℓ : ∀ β : Fin m, HasDerivAt (fun f' => ℓ f' (y β))
      (generalizedResidual ℓ f X y (θ_traj t) β) (f (X β) (θ_traj t))) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
          (generalizedResidual ℓ f X y (θ_traj t)).ofLp))) t := by
  rw [hasDerivAt_euclideanSpace]
  intro α
  have h_coord := gradient_flow_generalizedOutput_coord_ode ℓ f X y hflow t α hf hℓ
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (-⟪tangentFeature f (X α) (θ_traj t), gradient (mseLoss f X y) (θ_traj t)⟫) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow ⊢
  exact gradient_flow_generalizedOutput_coord_deriv_eq_inner_grad _ f X y hflow t α hdiff

/-- Step 3 (Insertion of Loss Gradient):
Substitute `∇_θ L(θ(t)) = (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f(x^β; θ(t))` into the rate of change:
  `∂_t f^α(t) = - ⟨∇_θ f^α(θ(t)), (1 / m) ∑_β (f^β(t) - y^β) ∇_θ f^β(θ(t))⟩`
              `= - (1 / m) ∑_β ⟨∇_θ f^α(θ(t)), ∇_θ f^β(θ(t))⟩ (f^β(t) - y^β)`. -/
theorem gradient_flow_output_coord_deriv_eq_sum_inner
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m,
        ⟪tangentFeature f (X α) (θ_traj t), tangentFeature f (X β) (θ_traj t)⟫ *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_deriv_eq_sum_inner _ f X y hflow t α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 4 (Assembly with Empirical NTK):
Recognizing the empirical NTK matrix entries `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`:
  `∂_t f^α(t) = - (1 / m) ∑_β K_t^{α β} (f^β(t) - y^β) = - (1 / m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_output_coord_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ *
        ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β *
          (trainingResidual f X y (θ_traj t)) β) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_coord_ode _ f X y hflow t α hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 5 (Matrix-Vector Formulation for Output Vector):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_output_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  rw [← generalizedEmpiricalRisk_squaredLoss_eq_mseLoss] at hflow
  have hℓ := fun β => hasDerivAt_squaredLoss_generalizedResidual f X y (θ_traj t) β
  have h := gradient_flow_generalizedOutput_vector_ode _ f X y hflow t hdiff hℓ
  rwa [generalizedResidual_squaredLoss_eq_trainingResidual] at h

/-- Step 5 (Matrix-Vector Formulation with Explicit `f(t) - y`):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t (f(t) - y)`. -/
theorem gradient_flow_output_vector_ode_sub_y
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        ((trainingOutputs f X (θ_traj t)) - y).ofLp))) t :=
  gradient_flow_output_vector_ode f X y hflow t hdiff

/-- Step 5 (Matrix-Vector Formulation for Residual Vector):
Function-space residual ODE under gradient flow:
  `∂_t r(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_residual_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ •
        ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  have h_out := gradient_flow_output_vector_ode f X y hflow t hdiff
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ)
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
    exact gradient_flow_generalizedOutput_coord_ode ℓ f X y hflow t α hf hℓ
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ)
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
  refine ⟨risk_dissipation_identity ℓ f X y hflow t hf hℓ, ?_⟩
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
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (generalizedEmpiricalRisk ℓ f X y) θ₀ θ_traj)
    (t : ℝ)
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
  refine ⟨risk_dissipation_identity ℓ f X y hflow t hf hℓ, ?_⟩
  have h1 := h_rr (generalizedResidual ℓ f X y (θ_traj t))
  have h_sq_nonneg : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 h_sq_nonneg
  have h3 : ((m : ℝ) ^ 2)⁻¹ * (lambda_min * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2) =
      (lambda_min / (m : ℝ) ^ 2) * ‖generalizedResidual ℓ f X y (θ_traj t)‖ ^ 2 := by ring
  rw [h3] at h2
  linarith

/-! ### Reusable Analytic Tool: Grönwall Differential Inequality -/

/-- Interval-Restricted Grönwall Decay Lemma:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` for all `t ∈ [0, T]`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ∈ [0, T]`.
This localized variant enables continuous induction bootstrap arguments where the differential
inequality only holds while the state remains inside a bootstrap region. -/
lemma gronwall_exponential_decay_Icc {E E' : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Set.Icc 0 T, E' t ≤ -c * E t) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    E t ≤ E 0 * Real.exp (-c * t) := by
  let g : ℝ → ℝ := fun s => E s * Real.exp (c * s)
  have hg_deriv : ∀ s, HasDerivAt g ((E' s + c * E s) * Real.exp (c * s)) s := by
    intro s
    have h1 := hE s
    have h2 : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
      have hc : HasDerivAt (fun u => c * u) (c * 1) s := (hasDerivAt_id s).const_mul c
      rw [mul_one] at hc
      exact hc.exp
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_diff : Differentiable ℝ g := fun s => (hg_deriv s).differentiableAt
  have hg_cont : ContinuousOn g (Set.Icc 0 T) := hg_diff.continuous.continuousOn
  have hg_within : ∀ s ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt g ((E' s + c * E s) * Real.exp (c * s)) (interior (Set.Icc 0 T)) s :=
    fun s _ => (hg_deriv s).hasDerivWithinAt
  have hg_nonpos : ∀ s ∈ interior (Set.Icc 0 T), (E' s + c * E s) * Real.exp (c * s) ≤ 0 := by
    intro s hs
    have hs_icc : s ∈ Set.Icc 0 T := interior_subset hs
    have hle : E' s + c * E s ≤ 0 := by linarith [hbound s hs_icc]
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
  gronwall_exponential_decay_Icc ht hE (fun s _ => hbound s) t ⟨ht, le_rfl⟩

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
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)` for any `t ∈ [0, T]`. -/
theorem residual_norm_sq_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hE : ∀ s, HasDerivAt (fun u => ‖r u‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp))) s :=
    fun s => deriv_norm_sq_timeVarying_ode K r s (hr s)
  have hbound : ∀ s ∈ Set.Icc 0 T, -(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K s *ᵥ (r s).ofLp)) ≤
      -(2 * lambda_min / (m : ℝ)) * ‖r s‖ ^ 2 := by
    intro s hs
    have h := deriv_norm_sq_le_of_rayleighRitz_timeVarying K lambda_min r s (h_rr s hs) (hr s) hm
    exact h.2
  exact gronwall_exponential_decay_Icc hT hE hbound t ht

/-- Exponential Decay of Residual Norm on a Closed Interval `[0, T]`:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)` for any `t ∈ [0, T]`. -/
theorem residual_norm_exponential_decay_timeVarying_Icc
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (lambda_min T : ℝ) (hT : 0 ≤ T)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h_rr : ∀ s ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K s *ᵥ v.ofLp))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have h_sq :=
    residual_norm_sq_exponential_decay_timeVarying_Icc K lambda_min T hT r h_rr hr hm t ht
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
    (fun s _ => h_rr s) hr hm t ⟨ht, le_rfl⟩

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
    (fun s _ => h_rr s) hr hm t ⟨ht, le_rfl⟩

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

/-- **Displacement is at most the integral of the speed bound.** If the Rayleigh quotient of the
empirical NTK along the trajectory is bounded below by `lambda_min` (any real, in particular `0`
under positive semidefiniteness) and the output Jacobian is `M`-bounded on `[0, T]`, then
`‖θ(T) - θ₀‖ ≤ ∫₀ᵀ (M / m) ‖r₀‖ exp(-(lambda_min / m) t) dt`. Both the gap and the no-gap
displacement bounds are corollaries. -/
theorem displacement_le_integral_of_rayleigh
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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
  have hr_ode : ∀ t : ℝ, HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (-(m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ
        (trainingResidual f X y (θ_traj t)).ofLp))) t :=
    fun t => gradient_flow_residual_vector_ode f X y hflow t (hdiff t)
  have hres_decay := residual_norm_exponential_decay_timeVarying_Icc
    (fun t => empiricalNTKMatrix f X (θ_traj t)) lambda_min T hT
    (fun s => trainingResidual f X y (θ_traj s)) h_rr hr_ode hm
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
  have hderiv_bound : ∀ t ∈ Set.Ioo (0:ℝ) T, ‖deriv θ_traj t‖ ≤
      (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)) := by
    intro t ht
    have hderiv_eq : deriv θ_traj t = -gradient (mseLoss f X y) (θ_traj t) :=
      (hflow.ode t).deriv
    rw [hderiv_eq, norm_neg]
    exact hspeed t (Set.mem_Icc_of_Ioo ht)
  have hcont : ContinuousOn θ_traj (Set.Icc 0 T) := hflow.cont_diff.continuous.continuousOn
  have hdiffOn : DifferentiableOn ℝ θ_traj (Set.Ioo 0 T) :=
    fun t _ => (hflow.ode t).differentiableAt.differentiableWithinAt
  have hBcont : Continuous
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t))) := by
    fun_prop
  have hBi : IntervalIntegrable
      (fun t : ℝ => (m : ℝ)⁻¹ * M * (r₀ * Real.exp (-(lambda_min / (m : ℝ)) * t)))
      MeasureTheory.volume 0 T :=
    hBcont.intervalIntegrable 0 T
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le hT hcont hdiffOn
    (Filter.Eventually.of_forall hderiv_bound) hBi
  rw [hflow.init] at hmain
  exact hmain

/-- Gap 5 Step 1 deliverable: if the empirical NTK's Rayleigh quotient along the trajectory is
bounded below by `lambda_min` throughout `[0, T]`, and the output Jacobian is `M`-bounded there
too, then gradient flow has moved by at most `(M * ‖r₀‖) / lambda_min` from `θ₀` by time `T` -
a bound with **no explicit dependence on `T`**, since the residual's exponential decay makes the
total distance traveled converge. -/
theorem displacement_integral_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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

/-- **Continuous-induction (bootstrap) principle on `[0, T]`.** Let `d` be continuous and
`C < r`. Suppose that whenever `d ≤ r` holds on all of `[0, S]` (for `S ∈ [0, T]`), the sharper
bound `d S ≤ C` holds. Then `d ≤ C` on all of `[0, T]`, i.e. `d` can never reach the threshold
`r`. Used for the displacement bootstraps: `d t = ‖θ(t) - θ₀‖` while the Jacobian estimates only
hold inside a ball. -/
theorem le_of_forall_bootstrap {d : ℝ → ℝ} (hd : Continuous d) {r C T : ℝ} (hCr : C < r)
    (hT : 0 ≤ T) (h0 : d 0 ≤ r)
    (hstep : ∀ S ∈ Set.Icc (0 : ℝ) T, (∀ t ∈ Set.Icc (0 : ℝ) S, d t ≤ r) → d S ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ C := by
  have hzero : d 0 ≤ C := hstep 0 ⟨le_rfl, hT⟩ fun t ht => by
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    exact h0
  have h := IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
    (s := {t : ℝ | d t ≤ C}) (a := 0) (b := T)
    ((isClosed_le hd continuous_const).inter isClosed_Icc) hzero (fun t ht hsub => ?_)
  · exact fun t htT => h htT
  have hdt : d t < r := (hsub ⟨ht.1, le_rfl⟩).trans_lt hCr
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff.1 (hd.continuousAt.eventually_lt continuousAt_const hdt)
  have hδ' : 0 < min δ (T - t) := lt_min hδ (by linarith [ht.2])
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show t < t + min δ (T - t) by linarith)) ?_
  intro u hu
  have huT : u ≤ T := by linarith [hu.2, min_le_right δ (T - t)]
  refine hstep u ⟨by linarith [ht.1, hu.1], huT⟩ fun t' ht' => ?_
  by_cases hle : t' ≤ t
  · exact (hsub ⟨ht'.1, hle⟩).trans hCr.le
  · have hlt : t < t' := not_le.1 hle
    have : dist t' t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [ht'.2, hu.2, min_le_left δ (T - t)]
    exact (hball this).le

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
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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
  -- Rayleigh-quotient stability, packaged: staying within radius `r` of `θ₀` keeps the Rayleigh
  -- quotient `≥ lambda_min`.
  have h_rr_ball : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ∀ v : EuclideanSpace ℝ (Fin m),
        lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v.ofLp) := by
    intro θ hθ v
    have hstep := rayleigh_quotient_lower_bound_of_displacement f X θ₀ θ M L_J lambda_min₀
      (hJ_bdd θ₀ (by simpa using hr_nonneg)) (hJ_bdd θ hθ) (hJ_lip θ hθ) h_rr₀ v
    have h2ML_J_nonneg : 0 ≤ 2 * M * L_J := by positivity
    have hCbound : 2 * M * L_J * ‖θ - θ₀‖ ≤ lambda_min₀ / 2 :=
      (mul_le_mul_of_nonneg_left hθ h2ML_J_nonneg).trans h_ball_gap
    have hge : lambda_min₀ - 2 * M * L_J * ‖θ - θ₀‖ ≥ lambda_min := by rw [hlm_def]; linarith
    nlinarith [hstep, mul_le_mul_of_nonneg_right hge (sq_nonneg ‖v‖)]
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
    (hflow.cont_diff.continuous.sub continuous_const).norm hCr hT
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
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t))
    (T M r C : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hm : 0 < (m : ℝ)) (hr : 0 ≤ r) (hCr : C < r)
    (hC_ge : T * M * ‖trainingResidual f X y θ₀‖ / m ≤ C)
    (hJ_bdd : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ‖outputJacobian f X θ‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖θ_traj t - θ₀‖ ≤ C :=
  le_of_forall_bootstrap (d := fun t => ‖θ_traj t - θ₀‖)
    (hflow.cont_diff.continuous.sub continuous_const).norm hCr hT
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
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
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
    ‖empiricalNTKMatrix f X (θ_traj t) - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * C := by
  have hdisp := lazy_training_displacement_bound f X y hflow hdiff M L_J lambda_min₀ r C
    hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀ hJ_bdd hJ_lip
  have hJ_bdd_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s)‖ ≤ M :=
    fun s hs => hJ_bdd (θ_traj s) ((hdisp s hs).trans hCr.le)
  have hJ_lip_all : ∀ s ≥ 0, ‖outputJacobian f X (θ_traj s) - outputJacobian f X θ₀‖ ≤
      L_J * ‖θ_traj s - θ₀‖ :=
    fun s hs => hJ_lip (θ_traj s) ((hdisp s hs).trans hCr.le)
  exact empiricalNTKMatrix_trajectory_freeze_of_jacobian_bound f X θ_traj θ₀ C M L_J hL_J
    hdisp hJ_bdd_all (hJ_bdd θ₀ (by simpa using hr_nonneg)) hJ_lip_all t ht

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
The PSD hypothesis on `A` removes any exponential Grönwall factor: the dissipative part
`-⟪e, A e⟫` of the error equation is nonpositive and only the forcing `(A - B) s` remains.
Independent of neural networks, initialization and width. -/
theorem norm_sub_le_of_linear_ode_perturbation
    (A B : ℝ → Matrix (Fin m) (Fin m) ℝ) (r s : ℝ → EuclideanSpace ℝ (Fin m)) {T a : ℝ}
    (hT : 0 ≤ T)
    (hr : ∀ t ∈ Set.Icc 0 T, HasDerivAt r (WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp))) t)
    (hs : ∀ t ∈ Set.Icc 0 T, HasDerivAt s (WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t)
    (hA : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (A t *ᵥ v.ofLp))
    (hab : ∀ t ∈ Set.Icc 0 T, ‖A t - B t‖ * ‖s t‖ ≤ a) :
    ∀ t ∈ Set.Icc 0 T, ‖r t - s t‖ ≤ ‖r 0 - s 0‖ + a * t := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have ha : 0 ≤ a := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hab 0 h0)
  have he : ∀ t ∈ Set.Icc 0 T, HasDerivAt (fun τ => r τ - s τ)
      ((WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp)) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t := fun t ht => (hr t ht).sub (hs t ht)
  -- Regularized comparison: `√(‖e‖² + η²) - a t` is nonincreasing on `[0, T]`.
  have key : ∀ η > 0, ∀ t ∈ Set.Icc 0 T,
      Real.sqrt (‖r t - s t‖ ^ 2 + η ^ 2) ≤ Real.sqrt (‖r 0 - s 0‖ ^ 2 + η ^ 2) + a * t := by
    intro η hη t ht
    have hpos : ∀ τ, 0 < ‖r τ - s τ‖ ^ 2 + η ^ 2 := fun τ => by positivity
    have hu : ∀ τ ∈ Set.Icc 0 T, HasDerivAt
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
        (fun τ hτ => (hu τ hτ).continuousAt.continuousWithinAt)
        (fun τ hτ => (hu τ (interior_subset hτ)).differentiableAt.differentiableWithinAt)
        (fun τ hτ => ?_)
      have hτ' := interior_subset hτ
      rw [(hu τ hτ').deriv]
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
    (hr : ∀ t ∈ Set.Icc 0 T,
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
    (fun _ => (m : ℝ)⁻¹ • K_inf) r s (a := (m : ℝ)⁻¹ * b) hT
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
    (hr : ∀ t ∈ Set.Icc 0 T,
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
      EuclideanSpace ℝ (Fin m))) (b := ε_K * ‖r 0‖) hT hr
    (fun t _ => matrix_exp_residual_trajectory_hasDerivAt K_inf (r 0) t) hK
    (fun t ht => mul_le_mul (hb t ht) (by
      simpa using matrix_exp_residual_decay K_inf (r 0) 0
        (fun v => by simpa using hK_inf v) hm t ht.1) (norm_nonneg _) hε_K)
  intro t ht
  have := h t ht
  simpa [hs0] using this

end LinearODECoefficientPerturbation

end NTK

end
