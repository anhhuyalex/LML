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
* `NTK.gronwall_exponential_decay` : Reusable Grönwall differential inequality for linear decay.
* `NTK.deriv_norm_sq_linear_ode` : Step 1 derivative `(d/dt) ‖r(t)‖² = - (2/m) r(t)ᵀ K_∞ r(t)`.
* `NTK.deriv_norm_sq_le_of_rayleighRitz` : Step 2 bound `(d/dt) ‖r(t)‖² ≤ - (2 λ / m) ‖r(t)‖²`.
* `NTK.residual_norm_sq_exponential_decay` : Step 3 squared residual norm decay.
* `NTK.residual_norm_exponential_decay` : Step 3 residual norm decay.
* `NTK.mse_loss_exponential_decay` : Step 4 empirical MSE loss decay.
* `NTK.matrix_exp_residual_trajectory_zero` : Initial condition `r(0) = r₀`.
* `NTK.matrix_exp_output_trajectory_zero` : Initial condition `f(0) = f₀`.
* `NTK.matrix_exp_residual_eq_output_sub_y` : Residual relation `f(t) - y = r(t)`.
* `NTK.matrix_exp_residual_trajectory_hasDerivAt` : Residual ODE satisfaction
  via matrix exponential.
* `NTK.matrix_exp_output_trajectory_hasDerivAt` : Output ODE satisfaction via matrix exponential.
* `NTK.matrix_exp_residual_decay` : Exponential decay for explicit matrix exponential trajectory.
* `NTK.matrix_exp_loss_decay` : Exponential loss decay for explicit matrix exponential trajectory.
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
      ring
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

/-- Reusable Grönwall Decay Lemma:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` for all `t`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ≥ 0`.
This lemma provides the analytic engine for establishing exponential convergence of
gradient flow training dynamics without ad-hoc definitions. -/
lemma gronwall_exponential_decay {E E' : ℝ → ℝ} {c : ℝ}
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t, E' t ≤ -c * E t) (t : ℝ) (ht : 0 ≤ t) :
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
  have hg_nonpos : (fun s => (E' s + c * E s) * Real.exp (c * s)) ≤ 0 := by
    intro s
    dsimp
    have hle : E' s + c * E s ≤ 0 := by linarith [hbound s]
    have hexp : 0 ≤ Real.exp (c * s) := (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg hle hexp
  have h_anti := antitone_of_hasDerivAt_nonpos hg_deriv hg_nonpos
  have h_le := h_anti ht
  dsimp [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (-c * t)).le
  have h_exp_cancel : E t * Real.exp (c * t) * Real.exp (-c * t) = E t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, mul_one]
  rw [h_exp_cancel] at h_mul
  exact h_mul

/-! ### Step-by-Step Proof of Exponential Convergence of Training Loss -/

/-- Step 1 (Time Derivative of Squared Residual Norm):
Along any trajectory satisfying `∂_t r(t) = - (1 / m) K_inf r(t)`, the rate of change of
`‖r(t)‖²` is given by:
  `(d / dt) ‖r(t)‖² = 2 r(t)ᵀ ∂_t r(t) = - (2 / m) r(t)ᵀ K_inf r(t)`. -/
theorem deriv_norm_sq_linear_ode
    (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hr : HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp))) t := by
  have h_inner : HasDerivAt (fun s => ⟪r s, r s⟫)
      (⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ +
       ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp)), r t⟫) t :=
    HasDerivAt.inner ℝ hr hr
  have h_symm : ⟪WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp)), r t⟫ =
      ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ := real_inner_comm _ _
  rw [h_symm, ← two_mul] at h_inner
  have h_dot : ⟪r t, WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))⟫ =
      -(m : ℝ)⁻¹ * ((r t).ofLp ⬝ᵥ (K_inf *ᵥ (r t).ofLp)) := by
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

/-- Step 2 (Rayleigh-Ritz Lower Bound Substitution):
Using the Rayleigh-Ritz condition `vᵀ K_inf v ≥ lambda_min ‖v‖²`, the rate of change is bounded:
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
        -(2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by
  constructor
  · exact deriv_norm_sq_linear_ode K_inf r t hr
  · have h1 := h_rr (r t)
    have hpos : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : (2 / (m : ℝ)) * (lambda_min * ‖r t‖ ^ 2) =
        (2 * lambda_min / (m : ℝ)) * ‖r t‖ ^ 2 := by ring
    rw [h3] at h2
    linarith

/-- Step 3 (Grönwall Integration for Squared Residual Norm):
Integrating the differential inequality yields:
  `‖r(t)‖² ≤ ‖r(0)‖² * exp(- (2 lambda_min / m) t)`. -/
theorem residual_norm_sq_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have hE : ∀ s, HasDerivAt (fun u => ‖r u‖ ^ 2)
      (-(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K_inf *ᵥ (r s).ofLp))) s :=
    fun s => deriv_norm_sq_linear_ode K_inf r s (hr s)
  have hbound : ∀ s, -(2 / (m : ℝ)) * ((r s).ofLp ⬝ᵥ (K_inf *ᵥ (r s).ofLp)) ≤
      -(2 * lambda_min / (m : ℝ)) * ‖r s‖ ^ 2 := by
    intro s
    have h := deriv_norm_sq_le_of_rayleighRitz K_inf lambda_min h_rr r s (hr s) hm
    exact h.2
  exact gronwall_exponential_decay hE hbound t ht

/-- Step 3 (Exponential Decay of Residual Norm):
Taking the square root gives:
  `‖r(t)‖ ≤ ‖r(0)‖ * exp(- (lambda_min / m) t)`. -/
theorem residual_norm_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    ‖r t‖ ≤ ‖r 0‖ * Real.exp (-(lambda_min / (m : ℝ)) * t) := by
  have h_sq := residual_norm_sq_exponential_decay K_inf lambda_min h_rr r hr hm t ht
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

/-- Step 4 (Exponential Loss Decay):
Multiplying by `1 / (2m)` yields the exponential loss convergence bound:
  `(1 / (2m)) ‖r(t)‖² ≤ ((1 / (2m)) ‖r(0)‖²) * exp(- (2 lambda_min / m) t)`. -/
theorem mse_loss_exponential_decay
    (K_inf : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (h_rr : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (hr : ∀ t, HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (r t).ofLp))) t)
    (hm : 0 < (m : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (2 * (m : ℝ))⁻¹ * ‖r t‖ ^ 2 ≤
      ((2 * (m : ℝ))⁻¹ * ‖r 0‖ ^ 2) * Real.exp (-(2 * lambda_min / (m : ℝ)) * t) := by
  have h := residual_norm_sq_exponential_decay K_inf lambda_min h_rr r hr hm t ht
  have hpos : 0 ≤ (2 * (m : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h_mul := mul_le_mul_of_nonneg_left h hpos
  rw [← mul_assoc] at h_mul
  exact h_mul

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

end NTK

end
