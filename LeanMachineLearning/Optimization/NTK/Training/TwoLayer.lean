/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.Packing
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JacobianBounds
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.NeuronSum
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.Concentration
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JointInit
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.KernelFreeze
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.KernelDrift
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.InitializationEvents
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.FiniteHorizon
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.CrossKernel
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.PredictionLimits
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.GlobalGap
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.FlowConstruction

/-!
# Two-Layer NTK Parameter Packing, Concentration, and the End-to-End Kernel-Freeze Bound

This module implements Gaps 1, 3, 4, and 6 of the NTK lazy training program
(see `docs/NTK_lazy_training_gap_closure_plan.md`).

Gap 1 bridges the curried `(W, a)` representation used by `evalSingle`/`evalVector`
in `NTK.Initialization` to the flat parameter vector
`θ : EuclideanSpace ℝ (Fin (n * d + n))` expected by `tangentFeature`,
`outputJacobian`, and `empiricalNTKMatrix` in `NTK.Shallow.Kernel`. Gap 3 concentrates the output
Jacobian's Frobenius norm at initialization; Gap 4 gives a local Lipschitz bound on the
Jacobian. Gap 6 (`lazy_training_kernel_freeze_bound_of_gaussian_init`) wires all of this,
plus Gap 5's bootstrap in `Training.GradientFlow`, into a single fully probabilistic corollary with
no free `hlazy`/`hLip` hypotheses.

## Structure

The development is a chain of modules, each importing the previous one; this file re-exports all
of them.  Folder `TwoLayer/`:

* `Packing` : `packParams`, `netFromParams`, gradients, coordinate equations, Jacobian norm
  concentration (Gap 3).
* `JacobianBounds` : Lipschitz bound on the output Jacobian (Gap 4) and the Taylor bound.
* `NeuronSum` : neuron-sum formula for the empirical NTK, scaled dataset, sequence-prefix bridge.
* `Concentration` : finite-width concentration of the empirical NTK, spectral-gap failure.
* `JointInit` : measurability and the joint weak limit of the initial residual and kernel.
* `KernelFreeze` : the end-to-end kernel-freeze bound (Gap 6).
* `KernelDrift` : `O(n⁻¹ᐟ²)` kernel drift from average neuron moments (Phase 11.2).
* `InitializationEvents` : `SmoothActivation`, bootstrap constants, good events (Phases 6.3, 8, 9).
* `FiniteHorizon` : finite-horizon specification, Jacobian and linearization-error freezing.
* `CrossKernel` : the train-test cross-kernel (Phase 14).
* `PredictionLimits` : test-prediction and weak limits of the trained residual and outputs.
* `GlobalGap` : the global positive-gap theorem.
* `FlowConstruction` : construction of the forward gradient-flow family.

## Main Definitions
- `packParams W a`: Pack weights `W` and readout `a` into a flat parameter vector `θ`.
- `unpackW θ`: Extract weight matrix `W : Fin n → Fin d → ℝ`.
- `unpackA θ`: Extract readout vector `a : Fin n → ℝ`.
- `netFromParams φ n d x θ`: Single-output network evaluation from flat parameter `θ`.
- `gradW φ n d x θ`: Gradient block for `W`, evaluated at `(x, θ)`.
- `gradA φ n d x θ`: Gradient block for `a`, evaluated at `(x, θ)`.
- `gradParams φ n d x θ`: Packed gradient vector of `netFromParams`.

## Main Theorems
- `unpackW_packParams`, `unpackA_packParams`: Left inverse equations.
- `packParams_unpack`: Right inverse equation (`packParams (unpackW θ) (unpackA θ) = θ`).
- `inner_packParams`: Inner product `⟪packParams W a, v⟫` in terms of components.
- `inner_packParams_packParams`: Inner product `⟪packParams W₁ a₁, packParams W₂ a₂⟫`.
- `hasFDerivAt_netFromParams`: Fréchet derivative of `netFromParams` with respect to `θ`.
- `hasGradientAt_netFromParams`: Gradient of `netFromParams`.
- `tangentFeature_netFromParams`: Closed form for `tangentFeature (netFromParams φ n d) x θ`.
- `unpackW_tangentFeature`, `unpackA_tangentFeature`: Component-wise tangent feature equations.
- `outputJacobian_netFromParams_apply_W`, `outputJacobian_netFromParams_apply_a`:
  Row evaluations of the output Jacobian delegating to `gradW` / `gradA`.
- `forwardGF_readout_hasDerivAt`, `forwardGF_inputWeight_hasDerivAt`:
  Phase 15 coordinate equations `∂_t a_i`, `∂_t W_{ij}` of the forward gradient flow.
- `empiricalNTKMatrix_netFromParams_apply`:
  Two-block decomposition of the empirical NTK matrix.
- `empiricalNTKMatrix_netFromParams_eq_neuron_sum`:
  Explicit empirical-NTK neuron-sum formula.
- `netFromParams_scaled_input`, `netFromParams_scaled_input_div`:
  Evaluation on scaled inputs `x / √d`.
- `gradW_scaled_input`, `gradA_scaled_input`:
  Gradients on scaled inputs factoring out `1 / √d` and `1 / √n`.
- `empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum`:
  Full empirical NTK on the scaled dataset `X / √d`.
- `outputJacobian_netFromParams_frobenius_norm_concentration` : **Gap 3 deliverable** - the
  output Jacobian's Frobenius norm is `O(1)` (width-independent) with probability `≥ 1 - δ`.
- `outputJacobian_netFromParams_frobenius_sub_le` : **Gap 4 deliverable** - the output Jacobian
  is `O(1/√n)`-Lipschitz, given a bound `R` on the readout weights.
- `norm_trainingOutputs_netFromParams_sub_linearization_le` : **Phase 12.2** - second-order Taylor
  bound `(K / (2 √n)) ‖θ - θ₀‖²` for the packed network (hidden and readout weights trained).
- `lazy_training_kernel_freeze_bound_of_gaussian_init` : **Gap 6, the plan's final
  deliverable** - the fully probabilistic end-to-end kernel-freeze bound.
- `chebyshev_entrywise_empiricalNTKMatrix` : finite-width entrywise Chebyshev concentration
  under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `chebyshev_matrix_empiricalNTKMatrix` : finite-width matrix Frobenius norm Chebyshev
  concentration under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `tendsto_initMeasure_empiricalNTKMatrix_ge_eps` : finite-width convergence in probability of
  the empirical NTK matrix in Frobenius norm under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le` : Rayleigh lower bound
  transfer from `limitingFullNTKMatrix` under Frobenius distance `λ_min / 2`.
- `chebyshev_matrix_empiricalNTKMatrix_spectral_gap_failure` : finite-width initial spectral-gap
  failure concentration bound under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `tendsto_initMeasure_initial_spectral_gap_failure` : spectral-gap failure measure tends to zero
  as width `n → ∞`.
- `measurable_empiricalNTKMatrix_netFromParams_packParams` : measurability of the empirical NTK
  matrix on packed parameters under `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)`.
- `tendstoInDistribution_initial_trainingResidual` : canonical initial training residual weak limit
  `r_n(0) ⟹ G - y` on the scaled dataset `(1 / √d) * X`.
- `tendstoInDistribution_joint_initial_residual_empiricalNTK` : joint weak convergence of initial
  training residual and empirical NTK matrix `(r_n(0), K_n(0)) ⟹ (G - y, K_∞)`.
- `exists_initial_residual_radius` : a single deterministic radius `R`, uniform in the width `n`,
  bounding the tail probability of the initial training residual norm by any `ε > 0`.
- `exists_measurableSet_initial_jacobian_and_readout_bounds` and
  `freeze_bound_of_initial_jacobian_and_readout_bounds` : the probabilistic and deterministic
  halves of `lazy_training_kernel_freeze_bound_of_gaussian_init`, split so that later theorems can
  reuse the measurable good event.
- `SmoothActivation` : bundled activation hypotheses (differentiable, bounded derivative,
  Lipschitz derivative; no bound on the value of `φ`) shared by the paper-facing theorems below.
- `tendsto_measure_kernel_drift_finite_horizon`,
  `tendstoInDistribution_trainingResidual_matrix_exp`,
  `tendstoInDistribution_trainingOutputs_matrix_exp` : **Phase 8** - finite-horizon kernel
  stationarity in probability and fixed-time weak limits of the trained residual and predictions
  (`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`), with no spectral gap.
- `exists_finite_horizon_kernel_freeze_event` : the no-gap counterpart on `[0, T]` with failure
  probability `≤ 2δ + ε`; positive semidefiniteness alone bounds the residual and the
  displacement radius `C = T M R / m` grows linearly in `T`.
- `exists_forwardGradientFlow`, `exists_forwardGradientFlow_family`, `forwardGradientFlow_unique`,
  `gradientFlow_finite_horizon_training_limit`,
  `gradientFlow_global_positive_gap_lazy_training_limit` : **Phases 10 and 11.1** - forward-time
  existence, uniqueness and continuous dependence of the gradient flow for every `SmoothActivation`
  (Picard-Lindelöf on a truncated field, an a priori bound from loss monotonicity, the linear growth
  of the Jacobian and Grönwall), a measurable trajectory family for every width, and the Phase 8 and
  Phase 9 theorems with the trajectory hypotheses discharged.
- `exists_measurableSet_global_lazy_training_event`, `global_positive_gap_lazy_training_limit` :
  **Phase 9** - under a positive limiting gap, uniform Rayleigh gap `λ_∞ / 4`, kernel drift
  `O(√(log n / n))`, exponential residual and loss decay and `mseLoss → 0`, with probability
  `≥ 1 - η`.
- `neuron_displacement_le`, `kernel_drift_le_of_neuron_moments`, `exists_neuronMoment_event`,
  `exists_measurableSet_global_lazy_training_event_inv_sqrt_width`,
  `global_positive_gap_lazy_training_limit_inv_sqrt_width`,
  `gradientFlow_global_positive_gap_lazy_training_limit_inv_sqrt_width` : **Phase 11.2** - the
  same global
  theorem with kernel drift `O(n⁻¹ᐟ²)` (no logarithm): each neuron's displacement is controlled by
  its own initial scale, and the resulting degree-four neuron moment is averaged over neurons and
  bounded in probability by Markov's inequality, at the price of one extra failure probability `δ`.
- `exists_measurableSet_finite_horizon_lazy_training_event`,
  `tendsto_measure_exists_gt_of_good_events`, `tendsto_measure_jacobian_drift_finite_horizon`,
  `tendsto_measure_jacobian_drift_global_positive_gap`,
  `tendsto_measure_linearization_error_finite_horizon`,
  `tendsto_measure_linearization_error_global_positive_gap`,
  `tendsto_measure_test_linearization_error_finite_horizon`,
  `tendsto_measure_test_linearization_error_global_positive_gap` : **Phase 12** - Jacobian
  (tangent-feature) freezing, proved directly from the Jacobian Lipschitz bound and not from Gram
  freezing, and convergence in probability of the nonlinear network to its initialization
  linearization (training outputs and any test input), on `[0, T]` without a gap and on `[0, ∞)`
  under a positive limiting gap; all four share one generic outer-measure lemma.
- `tendsto_initMeasure_crossKernel_ge_eps`, `tendsto_measure_crossKernel_drift_finite_horizon`,
  `tendsto_measure_crossKernel_drift_global_positive_gap`,
  `tendsto_measure_test_prediction_finite_horizon`,
  `tendsto_measure_test_prediction_global_positive_gap`,
  `test_prediction_kernel_interpolation_limit` : **Phase 14** - the train-test cross-kernel
  `J(θ) ∇f(x; θ)` (a row of the extended-dataset NTK Gram matrix) concentrates at initialization and
  freezes; the trained output at a test input `x` follows the closed-form predictor
  `f₀(x) - a ⬝ᵥ (r₀ - exp(-(t/m) K_∞) r₀)`, `a = K_∞⁻¹ k_∞(x, X)`, at fixed times (no gap) and
  uniformly in time (positive gap), and converges to the ridgeless kernel-regression interpolant
  as `n → ∞` and then `t → ∞`. The deterministic core is
  `abs_inner_displacement_add_frozenPrediction_le(_of_exp_decay)` in `Training.GradientFlow`.
- `exists_kernel_freeze_event_of_positive_gap` : **Phase 6.3** - under a positive limiting gap,
  a deterministic sequence `K n → 0` such that, with probability `≥ 1 - 2δ - 2ε` for all large `n`,
  every gradient flow keeps the empirical NTK within `K n` of its initial value for all `t ≥ 0`;
  all bootstrap constants are chosen explicitly.
-/
