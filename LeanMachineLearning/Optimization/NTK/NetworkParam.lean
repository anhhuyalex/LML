/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization
public import LeanMachineLearning.Optimization.NTK.Kernel
public import LeanMachineLearning.Optimization.NTK.InfiniteNTK
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Two-Layer NTK Parameter Packing, Concentration, and the End-to-End Kernel-Freeze Bound

This module implements Gaps 1, 3, 4, and 6 of the NTK lazy training program
(see `docs/NTK_lazy_training_gap_closure_plan.md`).

Gap 1 bridges the curried `(W, a)` representation used by `evalSingle`/`evalVector`
in `Initialization.lean` to the flat parameter vector
`θ : EuclideanSpace ℝ (Fin (n * d + n))` expected by `tangentFeature`,
`outputJacobian`, and `empiricalNTKMatrix` in `Kernel.lean`. Gap 3 concentrates the output
Jacobian's Frobenius norm at initialization; Gap 4 gives a local Lipschitz bound on the
Jacobian. Gap 6 (`lazy_training_kernel_freeze_bound_of_gaussian_init`) wires all of this,
plus Gap 5's bootstrap in `InfiniteNTK.lean`, into a single fully probabilistic corollary with
no free `hlazy`/`hLip` hypotheses.

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
  under `initMeasure n d`.
- `chebyshev_matrix_empiricalNTKMatrix` : finite-width matrix Frobenius norm Chebyshev
  concentration under `initMeasure n d`.
- `tendsto_initMeasure_empiricalNTKMatrix_ge_eps` : finite-width convergence in probability of
  the empirical NTK matrix in Frobenius norm under `initMeasure n d`.
- `initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le` : Rayleigh lower bound
  transfer from `limitingFullNTKMatrix` under Frobenius distance `λ_min / 2`.
- `chebyshev_matrix_empiricalNTKMatrix_spectral_gap_failure` : finite-width initial spectral-gap
  failure concentration bound under `initMeasure n d`.
- `tendsto_initMeasure_initial_spectral_gap_failure` : spectral-gap failure measure tends to zero
  as width `n → ∞`.
- `measurable_empiricalNTKMatrix_netFromParams_packParams` : measurability of the empirical NTK
  matrix on packed parameters under `initMeasure n d`.
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
  `abs_inner_displacement_add_frozenPrediction_le(_of_exp_decay)` in `InfiniteNTK.lean`.
- `exists_kernel_freeze_event_of_positive_gap` : **Phase 6.3** - under a positive limiting gap,
  a deterministic sequence `K n → 0` such that, with probability `≥ 1 - 2δ - 2ε` for all large `n`,
  every gradient flow keeps the empirical NTK within `K n` of its initial value for all `t ≥ 0`;
  all bootstrap constants are chosen explicitly.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

/-- Canonical bijection between the disjoint union `(Fin n × Fin d) ⊕ Fin n` and the packed
index type `Fin (n * d + n)`. The left summand indexes `W_{i, j}` and the right summand
indexes `a_i`. -/
def paramIndexEquiv (n d : ℕ) : (Fin n × Fin d) ⊕ Fin n ≃ Fin (n * d + n) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv

/-- Index of the weight matrix entry `W_{i, j}` in the packed parameter vector. -/
def idxW {n d : ℕ} (i : Fin n) (j : Fin d) : Fin (n * d + n) :=
  paramIndexEquiv n d (Sum.inl (i, j))

/-- Index of the readout weight `a_i` in the packed parameter vector. -/
def idxA {n d : ℕ} (i : Fin n) : Fin (n * d + n) :=
  paramIndexEquiv n d (Sum.inr i)

@[simp]
lemma paramIndexEquiv_symm_idxW {n d : ℕ} (i : Fin n) (j : Fin d) :
    (paramIndexEquiv n d).symm (idxW i j) = Sum.inl (i, j) :=
  (paramIndexEquiv n d).symm_apply_apply (Sum.inl (i, j))

@[simp]
lemma paramIndexEquiv_symm_idxA {n d : ℕ} (i : Fin n) :
    (paramIndexEquiv n d).symm (idxA i) = Sum.inr i :=
  (paramIndexEquiv n d).symm_apply_apply (Sum.inr i)

/-- Pack input weights `W` and readout weights `a` into a single flat vector in
`EuclideanSpace ℝ (Fin (n * d + n))`. -/
noncomputable def packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (n * d + n)) :=
  WithLp.toLp 2 (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i)

/-- Unpack the input weights `W : Fin n → Fin d → ℝ` from a flat parameter vector `θ`. -/
noncomputable def unpackW {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    Fin n → Fin d → ℝ :=
  fun i j => θ (idxW i j)

/-- Unpack the readout weights `a : Fin n → ℝ` from a flat parameter vector `θ`. -/
noncomputable def unpackA {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    Fin n → ℝ :=
  fun i => θ (idxA i)

lemma packParams_apply_idxW {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (i : Fin n) (j : Fin d) :
    packParams W a (idxW i j) = W i j := by
  dsimp [packParams]
  rw [paramIndexEquiv_symm_idxW]

lemma packParams_apply_idxA {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (i : Fin n) :
    packParams W a (idxA i) = a i := by
  dsimp [packParams]
  rw [paramIndexEquiv_symm_idxA]

@[simp]
lemma unpackW_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    unpackW (packParams W a) = W := by
  ext i j
  exact packParams_apply_idxW W a i j

@[simp]
lemma unpackA_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    unpackA (packParams W a) = a := by
  ext i
  exact packParams_apply_idxA W a i

@[simp]
lemma packParams_unpack {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    packParams (unpackW θ) (unpackA θ) = θ := by
  ext k
  dsimp [packParams]
  cases h : (paramIndexEquiv n d).symm k with
  | inl p =>
    rcases p with ⟨i, j⟩
    have h_k : k = idxW i j := by
      rw [← (paramIndexEquiv n d).apply_symm_apply k, h, idxW]
    rw [h_k]
    rfl
  | inr i =>
    have h_k : k = idxA i := by
      rw [← (paramIndexEquiv n d).apply_symm_apply k, h, idxA]
    rw [h_k]
    rfl

/-- Packing hidden and readout weights into the parameter vector is continuous: it is a coordinate
rearrangement. -/
lemma continuous_packParams {n d : ℕ} :
    Continuous (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => packParams p.1 p.2) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  rcases h : (paramIndexEquiv n d).symm k with ⟨i, j⟩ | i
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  · exact (continuous_apply i).comp continuous_snd

/-- The continuous linear map `θ ↦ unpackW θ i ⊙ x`. Internal helper. -/
private noncomputable def dotW_CLM {n d : ℕ} (i : Fin n) (x : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ :=
  ∑ j : Fin d, (x j) • EuclideanSpace.proj (idxW i j)

private lemma dotW_CLM_apply {n d : ℕ} (i : Fin n) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    dotW_CLM i x θ = unpackW θ i ⊙ x := by
  simp only [dotW_CLM, sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, innerProduct]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [unpackW]
  ring

/-- The inner product `⟪packParams W a, v⟫` expressed as a sum over the
two coordinate blocks. -/
lemma inner_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ⟪packParams W a, v⟫ =
      (∑ i : Fin n, ∑ j : Fin d, W i j * unpackW v i j) +
      ∑ i : Fin n, a i * unpackA v i := by
  have h_inner := EuclideanSpace.inner_toLp_toLp (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i) v.ofLp
  change ⟪packParams W a, v⟫ = _
  rw [show packParams W a = WithLp.toLp 2 (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i) from rfl]
  rw [show v = WithLp.toLp 2 v.ofLp from rfl]
  rw [h_inner]
  simp only [dotProduct, star_trivial]
  rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  have h_w : ∀ x x_1, v.ofLp (paramIndexEquiv n d (Sum.inl (x, x_1))) * W x x_1 =
      W x x_1 * unpackW v x x_1 := by
    intro i j; dsimp [unpackW, idxW]; ring
  have h_a : ∀ x, v.ofLp (paramIndexEquiv n d (Sum.inr x)) * a x =
      a x * unpackA v x := by
    intro i; dsimp [unpackA, idxA]; ring
  simp_rw [h_w, h_a]

/-- Inner product of two packed parameter vectors decomposes into weight-matrix
inner products plus readout-vector inner product. -/
lemma inner_packParams_packParams {n d : ℕ}
    (W₁ W₂ : Fin n → Fin d → ℝ) (a₁ a₂ : Fin n → ℝ) :
    ⟪packParams W₁ a₁, packParams W₂ a₂⟫ =
      (∑ i : Fin n, W₁ i ⊙ W₂ i) + ∑ i : Fin n, a₁ i * a₂ i := by
  rw [inner_packParams]
  simp only [unpackW_packParams, unpackA_packParams]
  rfl

/-- Single-output evaluation of a two-layer network from a packed parameter vector `θ`. -/
noncomputable def netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : ℝ :=
  evalSingle φ (unpackW θ) (unpackA θ) x

lemma netFromParams_eq_normalized_sum (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d x θ = (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⊙ x) :=
  evalSingle_eq_normalized_sum φ (unpackW θ) (unpackA θ) x

@[simp]
lemma trainingOutputs_netFromParams_packParams (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    trainingOutputs (netFromParams φ n d) X (packParams W a) = evalVector φ W a X := by
  unfold trainingOutputs evalVector netFromParams
  simp only [unpackW_packParams, unpackA_packParams]

@[simp]
lemma trainingResidual_netFromParams_packParams (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    trainingResidual (netFromParams φ n d) X y (packParams W a) =
      evalVector φ W a X - y := by
  simp only [trainingResidual, trainingOutputs_netFromParams_packParams]


/-- Gradient block for input weights `W`:
`∂f/∂W_{i, j} = n^{-1/2} a_i φ'(W_i ⊙ x) x_j`. -/
noncomputable def gradW (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : Fin n → Fin d → ℝ :=
  fun i j => (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x) * x j

/-- Gradient block for readout weights `a`:
`∂f/∂a_i = n^{-1/2} φ(W_i ⊙ x)`. -/
noncomputable def gradA (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : Fin n → ℝ :=
  fun i => (n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ x)

/-- The packed gradient vector in `EuclideanSpace ℝ (Fin (n * d + n))`. -/
noncomputable def gradParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    EuclideanSpace ℝ (Fin (n * d + n)) :=
  packParams (gradW φ n d x θ) (gradA φ n d x θ)

/-- Fréchet derivative of `netFromParams` with respect to parameters `θ`. -/
theorem hasFDerivAt_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    HasFDerivAt (netFromParams φ n d x)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n * d + n)))
        (gradParams φ n d x θ)) θ := by
  have h_comp : ∀ i : Fin n, HasFDerivAt (fun θ => φ (unpackW θ i ⊙ x))
      (deriv φ (unpackW θ i ⊙ x) • dotW_CLM i x) θ := by
    intro i
    have h_deriv : HasDerivAt φ (deriv φ (unpackW θ i ⊙ x)) (dotW_CLM i x θ) := by
      rw [dotW_CLM_apply]
      exact (hφ i).hasDerivAt
    have h := HasDerivAt.comp_hasFDerivAt θ h_deriv (dotW_CLM i x).hasFDerivAt
    have h_eq : (φ ∘ (dotW_CLM i x)) = (fun θ => φ (unpackW θ i ⊙ x)) := by
      ext θ'
      simp only [Function.comp_apply, dotW_CLM_apply]
    rwa [h_eq] at h
  have h_a : ∀ i : Fin n, HasFDerivAt (fun θ => unpackA θ i)
      ((EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ)) θ := by
    intro i
    exact (EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ).hasFDerivAt
  have h_mul : ∀ i : Fin n, HasFDerivAt (fun θ => unpackA θ i * φ (unpackW θ i ⊙ x))
      ((unpackA θ i) • (deriv φ (unpackW θ i ⊙ x) • dotW_CLM i x) +
       (φ (unpackW θ i ⊙ x)) •
         (EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ)) θ := by
    intro i
    exact (h_a i).mul (h_comp i)
  have h_sum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i θ => unpackA θ i * φ (unpackW θ i ⊙ x)) (fun i _ => h_mul i)
  have h_sum_fun :
      (∑ i ∈ (Finset.univ : Finset (Fin n)),
        fun θ' => unpackA θ' i * φ (unpackW θ' i ⊙ x)) =
      (fun θ' => ∑ i : Fin n, unpackA θ' i * φ (unpackW θ' i ⊙ x)) := by
    ext θ'
    simp only [Finset.sum_apply]
  rw [h_sum_fun] at h_sum
  have h_scaled := h_sum.const_smul (n : ℝ)⁻¹.sqrt
  have h_net_eq :
      (n : ℝ)⁻¹.sqrt • (fun θ' => ∑ i : Fin n, unpackA θ' i * φ (unpackW θ' i ⊙ x)) =
      netFromParams φ n d x := by
    ext θ'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (netFromParams_eq_normalized_sum φ n d x θ').symm
  rw [h_net_eq] at h_scaled
  convert h_scaled using 1
  ext v
  simp only [smul_apply, sum_apply, add_apply, smul_eq_mul, dotW_CLM_apply,
    PiLp.proj_apply, InnerProductSpace.toDual_apply_apply]
  dsimp [gradParams, unpackA]
  rw [inner_packParams]
  dsimp [gradW, gradA, innerProduct, unpackA]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

/-- Gradient of `netFromParams` with respect to parameters `θ`. -/
theorem hasGradientAt_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    HasGradientAt (netFromParams φ n d x) (gradParams φ n d x θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_netFromParams φ n d x θ hφ

/-- Gradient evaluation lemma for `netFromParams`. -/
theorem gradient_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    gradient (netFromParams φ n d x) θ = gradParams φ n d x θ :=
  (hasGradientAt_netFromParams φ n d x θ hφ).gradient

/-- Equation lemma for `tangentFeature`:
`tangentFeature (netFromParams φ n d) x θ = packParams (gradW ...) (gradA ...)`. -/
theorem tangentFeature_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  gradient_netFromParams φ n d x θ hφ

/-- Equation lemma for `tangentFeature` when `φ` is globally differentiable. -/
theorem tangentFeature_netFromParams_of_differentiable (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (n d : ℕ) (x : Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  tangentFeature_netFromParams φ n d x θ (fun _ => hφ _)

@[simp]
lemma unpackW_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    unpackW (tangentFeature (netFromParams φ n d) x θ) = gradW φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackW_packParams _ _

@[simp]
lemma unpackA_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    unpackA (tangentFeature (netFromParams φ n d) x θ) = gradA φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackA_packParams _ _

/-- Output Jacobian entry for `netFromParams` evaluated at `idxW i j`, delegating to `gradW`. -/
lemma outputJacobian_netFromParams_apply_W (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α : Fin m) (i : Fin n) (j : Fin d) :
    outputJacobian (netFromParams φ n d) X θ α (idxW i j) =
      gradW φ n d (X α) θ i j := by
  change unpackW (tangentFeature (netFromParams φ n d) (X α) θ) i j = _
  rw [unpackW_tangentFeature φ n d (X α) θ (hφ α)]

/-- Output Jacobian entry for `netFromParams` evaluated at `idxA i`, delegating to `gradA`. -/
lemma outputJacobian_netFromParams_apply_a (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α : Fin m) (i : Fin n) :
    outputJacobian (netFromParams φ n d) X θ α (idxA i) =
      gradA φ n d (X α) θ i := by
  change unpackA (tangentFeature (netFromParams φ n d) (X α) θ) i = _
  rw [unpackA_tangentFeature φ n d (X α) θ (hφ α)]

/-- **Readout-weight equation of the training flow.** Along a forward gradient flow of the MSE loss
of a two-layer network, at every positive time
  `∂_t a_i = -(1/m) ∑_α r^α ∂f^α/∂a_i = -(1/(m √n)) ∑_α r^α φ(W_i ⊙ x^α)`,
where `∂f^α/∂a_i = gradA φ n d (x^α) θ i` (`unpackA_tangentFeature`). -/
theorem forwardGF_readout_hasDerivAt (φ : ℝ → ℝ) (n d m : ℕ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW (θ t) i ⊙ X α)) (i : Fin n) :
    HasDerivAt (fun s => unpackA (θ s) i)
      (-((m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual (netFromParams φ n d) X y (θ t) α *
        gradA φ n d (X α) (θ t) i)) t := by
  have h := hasDerivAt_coord_of_forwardGF (netFromParams φ n d) X y hflow ht
    (fun β => (hasFDerivAt_netFromParams φ n d (X β) (θ t) (hφ β)).differentiableAt) (idxA i)
  simp only [outputJacobian_netFromParams_apply_a φ n d m X (θ t) hφ] at h
  exact h

/-- **Input-weight equation of the training flow.** Under the hypotheses of
`forwardGF_readout_hasDerivAt`, at every positive time
  `∂_t W_{ij} = -(1/m) ∑_α r^α ∂f^α/∂W_{ij} = -(1/(m √n)) a_i ∑_α r^α φ'(W_i ⊙ x^α) x^α_j`,
where `∂f^α/∂W_{ij} = gradW φ n d (x^α) θ i j` (`unpackW_tangentFeature`). -/
theorem forwardGF_inputWeight_hasDerivAt (φ : ℝ → ℝ) (n d m : ℕ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW (θ t) i ⊙ X α))
    (i : Fin n) (j : Fin d) :
    HasDerivAt (fun s => unpackW (θ s) i j)
      (-((m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual (netFromParams φ n d) X y (θ t) α *
        gradW φ n d (X α) (θ t) i j)) t := by
  have h := hasDerivAt_coord_of_forwardGF (netFromParams φ n d) X y hflow ht
    (fun β => (hasFDerivAt_netFromParams φ n d (X β) (θ t) (hφ β)).differentiableAt) (idxW i j)
  simp only [outputJacobian_netFromParams_apply_W φ n d m X (θ t) hφ] at h
  exact h

/-- Squared Frobenius norm of an output Jacobian as its coordinate energy. -/
lemma outputJacobian_frobenius_norm_sq_entries (n d m : ℕ) (φ : ℝ → ℝ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 =
      ∑ α : Fin m, ∑ k : Fin (n * d + n),
        (outputJacobian (netFromParams φ n d) X θ α k) ^ (2 : ℝ) := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs]
  rw [← Real.sqrt_eq_rpow]
  have hnonneg : 0 ≤ ∑ α : Fin m, ∑ k : Fin (n * d + n),
      |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ) := by
    apply Finset.sum_nonneg
    intro α hα
    apply Finset.sum_nonneg
    intro k hk
    positivity
  calc
    √(∑ α : Fin m, ∑ k : Fin (n * d + n),
        |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ)) ^ 2 =
        ∑ α : Fin m, ∑ k : Fin (n * d + n),
          |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ) := Real.sq_sqrt hnonneg
    _ = _ := by simp [sq_abs]

/-- Closed-form decomposition of the squared Frobenius norm of the output Jacobian into the
input-weight and readout blocks. -/
lemma outputJacobian_netFromParams_frobenius_norm_sq_rpow (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ (unpackW θ i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 =
      (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ i j) ^ (2 : ℝ)) +
      ∑ α : Fin m, ∑ i : Fin n, (gradA φ n d (X α) θ i) ^ (2 : ℝ) := by
  rw [outputJacobian_frobenius_norm_sq_entries]
  simp_rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α hα
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change outputJacobian (netFromParams φ n d) X θ α (idxW i j) ^ (2 : ℝ) = _
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ hφ α i j]
  · apply Finset.sum_congr rfl
    intro i hi
    change outputJacobian (netFromParams φ n d) X θ α (idxA i) ^ (2 : ℝ) = _
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ hφ α i]

/-- Natural-power form of `outputJacobian_netFromParams_frobenius_norm_sq_rpow`. -/
lemma outputJacobian_netFromParams_frobenius_norm_sq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ (unpackW θ i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 =
      (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ i j) ^ 2) +
      ∑ α : Fin m, ∑ i : Fin n, (gradA φ n d (X α) θ i) ^ 2 := by
  simpa [Real.rpow_two] using
    outputJacobian_netFromParams_frobenius_norm_sq_rpow φ n d m X θ hφ

/-- A pointwise width-normalized output-Jacobian bound. Uniform bounds on `φ` and `φ'`
eliminate the input-weight randomness; the only remaining random quantity is the readout
energy `n⁻¹ ∑ i, a i ^ 2`. -/
lemma outputJacobian_netFromParams_norm_sq_le_readout_energy
    (φ : ℝ → ℝ) (n d m : ℕ) (X : Fin m → Fin d → ℝ)
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ i : Fin n,
        (C₀ ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
  have hC₀_nonneg : 0 ≤ C₀ := (abs_nonneg (φ 0)).trans (hC₀ 0)
  have hC₁_nonneg : 0 ≤ C₁ := (abs_nonneg (deriv φ 0)).trans (hC₁ 0)
  have hroot_sq : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := by
    rw [Real.sq_sqrt]
    positivity
  rw [outputJacobian_netFromParams_frobenius_norm_sq φ n d m X (packParams W a) (by
    simpa only [unpackW_packParams] using hφ)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro α hα
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hderiv_sq : deriv φ (W i ⊙ X α) ^ 2 ≤ C₁ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC₁_nonneg).2 (hC₁ (W i ⊙ X α))
  have hφ_sq : φ (W i ⊙ X α) ^ 2 ≤ C₀ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC₀_nonneg).2 (hC₀ (W i ⊙ X α))
  have hW : ∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2 ≤
      (n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
    calc
      ∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2
        ≤ ∑ j : Fin d, ((n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * X α j ^ 2)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hpre_nonneg : 0 ≤ (n : ℝ)⁻¹ * a i ^ 2 * X α j ^ 2 := by positivity
          dsimp [gradW]
          simp only [unpackA_packParams, unpackW_packParams]
          rw [mul_pow, mul_pow, mul_pow, hroot_sq]
          nlinarith
      _ = (n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
        conv_lhs => rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
  have hA : gradA φ n d (X α) (packParams W a) i ^ 2 ≤ (n : ℝ)⁻¹ * C₀ ^ 2 := by
    dsimp [gradA]
    simp only [unpackW_packParams]
    rw [mul_pow, hroot_sq]
    exact mul_le_mul_of_nonneg_left hφ_sq (by positivity)
  calc
    (∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2) +
        gradA φ n d (X α) (packParams W a) i ^ 2
      ≤ (n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) +
          (n : ℝ)⁻¹ * C₀ ^ 2 := add_le_add hW hA
    _ = (n : ℝ)⁻¹ * (C₀ ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by ring

/-- Regrouping the pointwise Jacobian bound isolates the empirical readout energy
`n⁻¹ ∑ i, a i²`. This is the deterministic Phase 3a form used by the readout concentration
argument. -/
lemma outputJacobian_netFromParams_norm_sq_le
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2 ≤
      (m : ℝ) * C₀ ^ 2 + (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
  calc
    ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2 ≤
        (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ i : Fin n,
          (C₀ ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) :=
      outputJacobian_netFromParams_norm_sq_le_readout_energy φ n d m X W a C₀ C₁ hC₀ hC₁ hφ
    _ = (m : ℝ) * C₀ ^ 2 + (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ _i : Fin n, C₀ ^ 2 =
          (m : ℝ) * C₀ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
      have hvar : (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ i : Fin n,
          (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) =
          (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
            ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
        calc
          (n : ℝ)⁻¹ * ∑ α : Fin m, ∑ i : Fin n,
              (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) =
              (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m,
                (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
              rw [Finset.sum_comm]
          _ = (n : ℝ)⁻¹ * ∑ i : Fin n,
              (a i ^ 2 * C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
          _ = (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
              ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
              rw [show (∑ i : Fin n, a i ^ 2 * C₁ ^ 2 *
                  ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) =
                  (∑ i : Fin n, a i ^ 2) * (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                ring]
              ring
      rw [mul_add, hconst, hvar]

/-- Pointwise Jacobian bound without any bound on `φ`: only the bounded derivative is used, and the
activation enters through its empirical energy `n⁻¹ ∑_{i,α} φ(W_i ⊙ x_α)²`. -/
lemma outputJacobian_netFromParams_norm_sq_le_energies
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (C₁ : ℝ) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⊙ X α) ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
          ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
  have hC₁_nonneg : 0 ≤ C₁ := (abs_nonneg (deriv φ 0)).trans (hC₁ 0)
  have hroot_sq : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := by
    rw [Real.sq_sqrt]; positivity
  rw [outputJacobian_netFromParams_frobenius_norm_sq φ n d m X (packParams W a) (by
    simpa only [unpackW_packParams] using hφ)]
  have hterm : ∀ α : Fin m, ∀ i : Fin n,
      (∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2) +
        gradA φ n d (X α) (packParams W a) i ^ 2 ≤
      (n : ℝ)⁻¹ * (φ (W i ⊙ X α) ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
    intro α i
    have hderiv_sq : deriv φ (W i ⊙ X α) ^ 2 ≤ C₁ ^ 2 := by
      rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg _) hC₁_nonneg).2 (hC₁ _)
    have hW : ∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2 ≤
        (n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
      calc ∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2
          ≤ ∑ j : Fin d, ((n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * X α j ^ 2)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hpre : 0 ≤ (n : ℝ)⁻¹ * a i ^ 2 * X α j ^ 2 := by positivity
            dsimp [gradW]
            simp only [unpackA_packParams, unpackW_packParams]
            rw [mul_pow, mul_pow, mul_pow, hroot_sq]
            nlinarith
        _ = (n : ℝ)⁻¹ * (a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
            simp only [← Finset.mul_sum]
    have hA : gradA φ n d (X α) (packParams W a) i ^ 2 = (n : ℝ)⁻¹ * φ (W i ⊙ X α) ^ 2 := by
      dsimp [gradA]
      simp only [unpackW_packParams]
      rw [mul_pow, hroot_sq]
    rw [hA]
    nlinarith
  calc (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2) +
        ∑ α : Fin m, ∑ i : Fin n, gradA φ n d (X α) (packParams W a) i ^ 2
      = ∑ α : Fin m, ∑ i : Fin n, ((∑ j : Fin d, gradW φ n d (X α) (packParams W a) i j ^ 2) +
          gradA φ n d (X α) (packParams W a) i ^ 2) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ ∑ α : Fin m, ∑ i : Fin n,
          (n : ℝ)⁻¹ * (φ (W i ⊙ X α) ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => hterm α i
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⊙ X α) ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
          ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
        simp only [← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
        have h1 : ∑ α : Fin m, ∑ i : Fin n, φ (W i ⊙ X α) ^ 2 =
            ∑ i : Fin n, ∑ α : Fin m, φ (W i ⊙ X α) ^ 2 := Finset.sum_comm
        have h2 : ∑ α : Fin m, ∑ i : Fin n, a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2 =
            (∑ i : Fin n, a i ^ 2) * (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [h1, h2]
        ring


/-- Under the joint Gaussian initialization, the output Jacobian has the stated Frobenius-norm
bound with probability at least `1 - δ`. The input-weight component of the product measure is
irrelevant after the deterministic bound; only the readout-energy tail remains. -/
theorem outputJacobian_netFromParams_frobenius_norm_concentration
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (C₀ C₁ : ℝ) (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : Differentiable ℝ φ) {δ : ℝ} (hδ : 0 < δ) :
    let M := Real.sqrt ((m : ℝ) * C₀ ^ 2 +
      (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ)
    (initMeasure n d).real {p | ‖outputJacobian (netFromParams φ n d) X
      (packParams p.1 p.2)‖ ≤ M} ≥ 1 - δ := by
  dsimp only
  let K : ℝ := C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2
  let B : ℝ := (m : ℝ) * C₀ ^ 2 + K / δ
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdet (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
      (hp : gaussianReadoutEnergy n p.2 ≤ δ⁻¹) :
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ Real.sqrt B := by
    have hnorm_sq := outputJacobian_netFromParams_norm_sq_le φ n d m hn X p.1 p.2 C₀ C₁
      hC₀ hC₁ (fun _ _ => hφ.differentiableAt)
    have hbound :
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2 ≤ B := by
      calc
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2 ≤
            (m : ℝ) * C₀ ^ 2 + K * gaussianReadoutEnergy n p.2 := by
              simpa [K, gaussianReadoutEnergy] using hnorm_sq
        _ ≤ (m : ℝ) * C₀ ^ 2 + K * δ⁻¹ :=
          add_le_add_right (mul_le_mul_of_nonneg_left hp hK_nonneg) _
        _ = B := by simp [B, div_eq_mul_inv]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hB_nonneg]
    exact hbound
  have htail := prob_gaussianReadout_sum_sq_le n hn hδ
  have hreadout_event :
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | gaussianReadoutEnergy n p.2 ≤ δ⁻¹} =
        Set.univ ×ˢ {a : Fin n → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ δ⁻¹} := by
    ext p
    simp [gaussianReadoutEnergy]
  have hprod_tail :
      (initMeasure n d).real {p | gaussianReadoutEnergy n p.2 ≤ δ⁻¹} ≥ 1 - δ := by
    rw [hreadout_event, MeasureTheory.measureReal_prod_prod]
    simpa using htail
  have hsubset :
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | gaussianReadoutEnergy n p.2 ≤ δ⁻¹} ⊆
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ Real.sqrt B} := by
    intro p hp
    exact hdet p hp
  change (initMeasure n d).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
    ‖outputJacobian (netFromParams φ n d) X
    (packParams p.1 p.2)‖ ≤ Real.sqrt B} ≥ 1 - δ
  exact hprod_tail.trans (MeasureTheory.measureReal_mono (μ := initMeasure n d) hsubset)

/-- **Gap 3 without a bound on `φ`.** Only a bounded derivative, differentiability and Gaussian
square integrability of `φ(w ⊙ x_α)` are used (the latter follows from linear growth, which is
implied by a bounded derivative, see `memLp_gaussianRow_comp_of_linear_growth`). With probability
`≥ 1 - δ` the output Jacobian has Frobenius norm at most
`√(2 (∑_α E φ(w ⊙ x_α)² + 1 + C₁² ∑ ‖x_α‖²) / δ)`, uniformly in the width. -/
theorem outputJacobian_netFromParams_frobenius_norm_concentration_of_L2
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (C₁ : ℝ)
    (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hφ : Differentiable ℝ φ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⊙ X α)) 2 (gaussianRowMeasure d))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (initMeasure n d).real {p | ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      Real.sqrt (2 * ((∑ α : Fin m, ∫ w, φ (w ⊙ X α) ^ 2 ∂(gaussianRowMeasure d)) + 1 +
        C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ)} ≥ 1 - δ := by
  set v : ℝ := ∑ α : Fin m, ∫ w, φ (w ⊙ X α) ^ 2 ∂(gaussianRowMeasure d) with hv
  set K : ℝ := C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2 with hK
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun α _ => integral_nonneg fun w => sq_nonneg _
  have hK0 : 0 ≤ K := by positivity
  set τ : ℝ := 2 * (v + 1) / δ with hτ
  have hτ0 : 0 < τ := by positivity
  have hA := measureReal_gaussianInit_activationEnergy_le hn φ hφ.continuous.measurable X hL2
    (τ := τ) (δ := δ / 2) hτ0 (by
      rw [hτ]; field_simp; linarith [hv0])
  have hB := prob_gaussianReadout_sum_sq_le n hn (δ := δ / 2) (by positivity)
  have hprod : (initMeasure n d).real
      ({W : Fin n → Fin d → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⊙ X α) ^ 2 ≤ τ} ×ˢ
        {a : Fin n → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ (δ / 2)⁻¹}) ≥ 1 - δ := by
    rw [measureReal_prod_prod]
    have h0 : 0 ≤ 1 - δ / 2 := by linarith
    calc (gaussianInit n d).real _ * (gaussianReadoutMeasure n).real _
        ≥ (1 - δ / 2) * (1 - δ / 2) := mul_le_mul hA hB h0 measureReal_nonneg
      _ ≥ 1 - δ := by nlinarith [sq_nonneg δ]
  refine hprod.trans (measureReal_mono ?_)
  rintro ⟨W, a⟩ ⟨hW, ha⟩
  simp only [Set.mem_ofPred_eq] at hW ha ⊢
  have hnorm := outputJacobian_netFromParams_norm_sq_le_energies φ n d m hn X W a C₁ hC₁
    (fun _ _ => hφ.differentiableAt)
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2
      ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⊙ X α) ^ 2 +
        K * ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := hnorm
    _ ≤ τ + K * (δ / 2)⁻¹ := add_le_add hW (mul_le_mul_of_nonneg_left ha hK0)
    _ = 2 * (v + 1 + K) / δ := by rw [hτ]; field_simp

/-! ### Phase 4: Local Lipschitz Bound on the Output Jacobian -/

lemma two_mul_add_two_mul_sq (u v : ℝ) :
    (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  have : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
  linarith

lemma norm_sq_sub_unpack (n d : ℕ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖θ₁ - θ₂‖ ^ 2 =
      (∑ i : Fin n, ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
      ∑ i : Fin n, (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  apply congr_arg₂
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ((θ₁ - θ₂) (idxW i j)) ^ 2 = _
    simp only [PiLp.sub_apply, unpackW]
  · apply Finset.sum_congr rfl
    intro i _
    change ((θ₁ - θ₂) (idxA i)) ^ 2 = _
    simp only [PiLp.sub_apply, unpackA]

lemma innerProduct_sub (d : ℕ) (x y z : Fin d → ℝ) :
    (x - y) ⊙ z = x ⊙ z - y ⊙ z :=
  innerProduct_sub_left x y z

lemma innerProduct_sub_sq_le (d : ℕ) (x y z : Fin d → ℝ) :
    (x ⊙ z - y ⊙ z) ^ 2 ≤ (∑ j : Fin d, (x j - y j) ^ 2) * (∑ j : Fin d, z j ^ 2) := by
  rw [← innerProduct_sub]
  dsimp [innerProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => x j - y j) z

lemma outputJacobian_sub_frobenius_norm_sq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ₁ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₁ i ⊙ X α))
    (hφ₂ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₂ i ⊙ X α)) :
    ‖outputJacobian (netFromParams φ n d) X θ₁ -
        outputJacobian (netFromParams φ n d) X θ₂‖ ^ 2 =
      (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
      ∑ α : Fin m, ∑ i : Fin n,
        (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2 := by
  rw [matrix_frobenius_norm_sq]
  simp_rw [Matrix.sub_apply]
  simp_rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (outputJacobian (netFromParams φ n d) X θ₁ α (idxW i j) -
            outputJacobian (netFromParams φ n d) X θ₂ α (idxW i j)) ^ 2 = _
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ₁ hφ₁ α i j]
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ₂ hφ₂ α i j]
  · apply Finset.sum_congr rfl
    intro i _
    change (outputJacobian (netFromParams φ n d) X θ₁ α (idxA i) -
            outputJacobian (netFromParams φ n d) X θ₂ α (idxA i)) ^ 2 = _
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ₁ hφ₁ α i]
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ₂ hφ₂ α i]

lemma grad_single_neuron_sub_le (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n)
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha₁ : |unpackA θ₁ i| ≤ R) :
    let Sx := ∑ j : Fin d, x j ^ 2
    let Wdiff := ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2
    let Adiff := (unpackA θ₁ i - unpackA θ₂ i) ^ 2
    (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
      (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * (Wdiff + Adiff) := by
  dsimp only
  let Sx := ∑ j : Fin d, x j ^ 2
  let Wdiff := ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2
  let Adiff := (unpackA θ₁ i - unpackA θ₂ i) ^ 2
  have hSx_nonneg : 0 ≤ Sx := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hWdiff_nonneg : 0 ≤ Wdiff := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAdiff_nonneg : 0 ≤ Adiff := sq_nonneg _
  have hroot_sq : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := by
    rw [Real.sq_sqrt]
    positivity
  let u₁ := unpackW θ₁ i ⊙ x
  let u₂ := unpackW θ₂ i ⊙ x
  have hu_diff_sq : (u₁ - u₂) ^ 2 ≤ Wdiff * Sx := by
    dsimp [u₁, u₂, Wdiff, Sx]
    exact innerProduct_sub_sq_le d (unpackW θ₁ i) (unpackW θ₂ i) x
  have hφ_sub_sq : (φ u₁ - φ u₂) ^ 2 ≤ C₁ ^ 2 * (Sx * Wdiff) := by
    have h1 : |φ u₁ - φ u₂| ≤ C₁ * |u₁ - u₂| := hφ_lip u₁ u₂
    have h2 : |φ u₁ - φ u₂| ^ 2 ≤ (C₁ * |u₁ - u₂|) ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) _).2 h1
      exact mul_nonneg hC₁_nonneg (abs_nonneg _)
    rw [sq_abs, mul_pow, sq_abs] at h2
    calc
      (φ u₁ - φ u₂) ^ 2 ≤ C₁ ^ 2 * (u₁ - u₂) ^ 2 := h2
      _ ≤ C₁ ^ 2 * (Wdiff * Sx) :=
        mul_le_mul_of_nonneg_left hu_diff_sq (by positivity)
      _ = C₁ ^ 2 * (Sx * Wdiff) := by ring
  have hderiv_sub_sq : (deriv φ u₁ - deriv φ u₂) ^ 2 ≤ C₂ ^ 2 * (Sx * Wdiff) := by
    have h1 : |deriv φ u₁ - deriv φ u₂| ≤ C₂ * |u₁ - u₂| := hderiv_lip u₁ u₂
    have h2 : |deriv φ u₁ - deriv φ u₂| ^ 2 ≤ (C₂ * |u₁ - u₂|) ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) _).2 h1
      exact mul_nonneg hC₂_nonneg (abs_nonneg _)
    rw [sq_abs, mul_pow, sq_abs] at h2
    calc
      (deriv φ u₁ - deriv φ u₂) ^ 2 ≤ C₂ ^ 2 * (u₁ - u₂) ^ 2 := h2
      _ ≤ C₂ ^ 2 * (Wdiff * Sx) :=
        mul_le_mul_of_nonneg_left hu_diff_sq (by positivity)
      _ = C₂ ^ 2 * (Sx * Wdiff) := by ring
  have hA_term : (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
      (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := by
    dsimp [gradA, u₁, u₂]
    rw [← mul_sub, mul_pow, hroot_sq]
    have h_sub : (φ (unpackW θ₁ i ⊙ x) - φ (unpackW θ₂ i ⊙ x)) ^ 2 ≤
        C₁ ^ 2 * (Sx * Wdiff) := hφ_sub_sq
    have h_prod := mul_le_mul_of_nonneg_left h_sub (by positivity : 0 ≤ (n : ℝ)⁻¹)
    calc
      (n : ℝ)⁻¹ * (φ (unpackW θ₁ i ⊙ x) - φ (unpackW θ₂ i ⊙ x)) ^ 2
        ≤ (n : ℝ)⁻¹ * (C₁ ^ 2 * (Sx * Wdiff)) := h_prod
      _ = (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := by ring
  have hD_sq : (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 ≤
      2 * R ^ 2 * C₂ ^ 2 * Sx * Wdiff + 2 * C₁ ^ 2 * Adiff := by
    have hsplit : unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂ =
        unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂) +
        (unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂ := by ring
    rw [hsplit]
    have h2 := two_mul_add_two_mul_sq (unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂))
      ((unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂)
    have ha₁_sq : (unpackA θ₁ i) ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hR_nonneg).2 ha₁
    have hderiv_sq : (deriv φ u₂) ^ 2 ≤ C₁ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC₁_nonneg).2 (hderiv_bound u₂)
    have hpart1 : (unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂)) ^ 2 ≤
        R ^ 2 * C₂ ^ 2 * Sx * Wdiff := by
      rw [mul_pow]
      calc
        (unpackA θ₁ i) ^ 2 * (deriv φ u₁ - deriv φ u₂) ^ 2
          ≤ R ^ 2 * (deriv φ u₁ - deriv φ u₂) ^ 2 :=
            mul_le_mul_of_nonneg_right ha₁_sq (sq_nonneg _)
        _ ≤ R ^ 2 * (C₂ ^ 2 * (Sx * Wdiff)) :=
          mul_le_mul_of_nonneg_left hderiv_sub_sq (by positivity)
        _ = R ^ 2 * C₂ ^ 2 * Sx * Wdiff := by ring
    have hpart2 : ((unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂) ^ 2 ≤
        C₁ ^ 2 * Adiff := by
      rw [mul_pow]
      dsimp [Adiff]
      calc
        (unpackA θ₁ i - unpackA θ₂ i) ^ 2 * (deriv φ u₂) ^ 2
          ≤ (unpackA θ₁ i - unpackA θ₂ i) ^ 2 * C₁ ^ 2 :=
            mul_le_mul_of_nonneg_left hderiv_sq (sq_nonneg _)
        _ = C₁ ^ 2 * (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by ring
    linarith
  have hW_term : (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) ≤
      (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) := by
    have hj : ∀ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2 =
        (n : ℝ)⁻¹ * (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * x j ^ 2 := by
      intro j
      dsimp [gradW, u₁, u₂]
      have : (n : ℝ)⁻¹.sqrt * unpackA θ₁ i * deriv φ (unpackW θ₁ i ⊙ x) * x j -
             (n : ℝ)⁻¹.sqrt * unpackA θ₂ i * deriv φ (unpackW θ₂ i ⊙ x) * x j =
             (n : ℝ)⁻¹.sqrt *
              (unpackA θ₁ i * deriv φ (unpackW θ₁ i ⊙ x) -
               unpackA θ₂ i * deriv φ (unpackW θ₂ i ⊙ x)) * x j := by ring
      rw [this, mul_pow, mul_pow, hroot_sq]
    simp_rw [hj]
    rw [← Finset.mul_sum]
    have h_sum : (∑ j : Fin d, x j ^ 2) = Sx := rfl
    rw [h_sum]
    have h_prod := mul_le_mul_of_nonneg_right hD_sq hSx_nonneg
    have h_final := mul_le_mul_of_nonneg_left h_prod (by positivity : 0 ≤ (n : ℝ)⁻¹)
    calc
      (n : ℝ)⁻¹ * (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * Sx
        = (n : ℝ)⁻¹ * ((unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * Sx) := by ring
      _ ≤ (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx * Wdiff + 2 * C₁ ^ 2 * Adiff) * Sx) := h_final
      _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) := by ring
  calc
    (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2
      ≤ (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) +
          (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := add_le_add hW_term hA_term
    _ = (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + C₁ ^ 2 * Sx) * Wdiff +
          2 * C₁ ^ 2 * Sx * Adiff) := by ring
    _ ≤ (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * Wdiff +
          (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * Adiff) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hcoeff1 : 2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + C₁ ^ 2 * Sx ≤
          2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx := by
        have : C₁ ^ 2 * Sx ≤ 3 * C₁ ^ 2 * Sx := by nlinarith [sq_nonneg C₁]
        linarith
      have hcoeff2 : 2 * C₁ ^ 2 * Sx ≤
          2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx := by
        have hpos1 : 0 ≤ 2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 := by positivity
        have hpos2 : 2 * C₁ ^ 2 * Sx ≤ 3 * C₁ ^ 2 * Sx := by nlinarith [sq_nonneg C₁]
        linarith
      have h1 := mul_le_mul_of_nonneg_right hcoeff1 hWdiff_nonneg
      have h2 := mul_le_mul_of_nonneg_right hcoeff2 hAdiff_nonneg
      linarith
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * (Wdiff + Adiff) := by
      ring


lemma grad_sum_neurons_sub_le (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha₁ : ∀ i : Fin n, |unpackA θ₁ i| ≤ R) :
    let Sx := ∑ j : Fin d, x j ^ 2
    (∑ i : Fin n, ∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
      ∑ i : Fin n, (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * ‖θ₁ - θ₂‖ ^ 2 := by
  dsimp only
  let Sx := ∑ j : Fin d, x j ^ 2
  have h_single : ∀ i : Fin n,
      (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
          (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
            ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
             (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
    intro i
    exact grad_single_neuron_sub_le φ n d x θ₁ θ₂ i C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg
      hφ_lip hderiv_bound hderiv_lip (ha₁ i)
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : Fin n, ((∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2))
      ≤ ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
          ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
           (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact h_single i
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
        ∑ i : Fin n, ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
           (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
      rw [← Finset.mul_sum]
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * ‖θ₁ - θ₂‖ ^ 2 := by
      rw [Finset.sum_add_distrib]
      rw [← norm_sq_sub_unpack n d θ₁ θ₂]

/-- Local Lipschitz bound on the output Jacobian of `netFromParams` in Frobenius norm.
For parameters `θ₁, θ₂` whose readout weights are bounded by `R`, the Frobenius difference
`‖J(θ₁) - J(θ₂)‖` is bounded by `(K / √n) * ‖θ₁ - θ₂‖`, where `K` is width-independent.
The `1 / √n` scaling rate is explicit. -/
theorem outputJacobian_netFromParams_frobenius_sub_le
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hφ₁ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₁ i ⊙ X α))
    (hφ₂ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₂ i ⊙ X α))
    (ha₁ : ∀ i : Fin n, |unpackA θ₁ i| ≤ R) :
    let K := Real.sqrt (∑ α : Fin m, (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
      3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)))
    ‖outputJacobian (netFromParams φ n d) X θ₁ -
      outputJacobian (netFromParams φ n d) X θ₂‖ ≤
        (K / Real.sqrt (n : ℝ)) * ‖θ₁ - θ₂‖ := by
  dsimp only
  let S : Fin m → ℝ := fun α => ∑ j : Fin d, X α j ^ 2
  let term : Fin m → ℝ := fun α => 2 * R ^ 2 * C₂ ^ 2 * (S α) ^ 2 + 3 * C₁ ^ 2 * S α
  let K := Real.sqrt (∑ α : Fin m, term α)
  have hK_nonneg : 0 ≤ K := Real.sqrt_nonneg _
  have hroot_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h_single : ∀ α : Fin m,
      (∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
      ∑ i : Fin n, (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * term α * ‖θ₁ - θ₂‖ ^ 2 := by
    intro α
    exact grad_sum_neurons_sub_le φ n d (X α) θ₁ θ₂ C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg
      hφ_lip hderiv_bound hderiv_lip ha₁
  have h_norm_sq := outputJacobian_sub_frobenius_norm_sq φ n d m X θ₁ θ₂ hφ₁ hφ₂
  have h_sum_le :
      ‖outputJacobian (netFromParams φ n d) X θ₁ -
          outputJacobian (netFromParams φ n d) X θ₂‖ ^ 2 ≤
        (K / Real.sqrt (n : ℝ)) ^ 2 * ‖θ₁ - θ₂‖ ^ 2 := by
    rw [h_norm_sq]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ α : Fin m,
          ((∑ i : Fin n, ∑ j : Fin d,
            (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
          ∑ i : Fin n, (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2)
        ≤ ∑ α : Fin m, (n : ℝ)⁻¹ * term α * ‖θ₁ - θ₂‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          exact h_single α
      _ = (n : ℝ)⁻¹ * (∑ α : Fin m, term α) * ‖θ₁ - θ₂‖ ^ 2 := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        rw [show (∑ α : Fin m, term α * ‖θ₁ - θ₂‖ ^ 2) =
            (∑ α : Fin m, term α) * ‖θ₁ - θ₂‖ ^ 2 by rw [← Finset.sum_mul]]
      _ = (K / Real.sqrt (n : ℝ)) ^ 2 * ‖θ₁ - θ₂‖ ^ 2 := by
        have h_sum_nonneg : 0 ≤ ∑ α : Fin m, term α := by
          apply Finset.sum_nonneg
          intro α _
          dsimp [term, S]
          positivity
        have hK_sq : K ^ 2 = ∑ α : Fin m, term α := Real.sq_sqrt h_sum_nonneg
        have hroot_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        rw [div_pow, hK_sq, hroot_sq]
        ring
  rw [← mul_pow] at h_sum_le
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h_sum_le

/-- **Second-order Taylor bound for the packed two-layer network.** The network `netFromParams`
trains both the hidden weights and the readout weights, so its linearization at `θ₀` involves the
mixed hidden/readout derivative; the remainder is nevertheless controlled by the Jacobian Lipschitz
bound `outputJacobian_netFromParams_frobenius_sub_le`, which needs a bound `R` only on the readout
weights of the *base point* `θ₀`, not of `θ`. For every `θ`,
`‖f(θ) - f(θ₀) - J(θ₀) (θ - θ₀)‖ ≤ (K / (2 √n)) ‖θ - θ₀‖²`, where `f` and `J` are the training
outputs and the output Jacobian on the dataset `X`, and `K` is the constant of the Jacobian bound.
For a single test input use `m = 1`. -/
theorem norm_trainingOutputs_netFromParams_sub_linearization_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    ‖trainingOutputs (netFromParams φ n d) X θ - trainingOutputs (netFromParams φ n d) X θ₀ -
        WithLp.toLp 2 (outputJacobian (netFromParams φ n d) X θ₀ *ᵥ (θ - θ₀).ofLp)‖ ≤
      (Real.sqrt (∑ α : Fin m, (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ)) / 2 * ‖θ - θ₀‖ ^ 2 :=
  norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) X θ₀ ‖θ - θ₀‖ _
    (fun z _ β => (hasFDerivAt_netFromParams φ n d (X β) z
      fun _ => hφ.differentiableAt).differentiableAt)
    (fun z _ => by
      rw [norm_sub_rev (outputJacobian _ X z), norm_sub_rev z θ₀]
      exact outputJacobian_netFromParams_frobenius_sub_le φ n d m hn X θ₀ z C₁ C₂ R hC₁_nonneg
        hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip (fun _ _ => hφ.differentiableAt)
        (fun _ _ => hφ.differentiableAt) ha)
    le_rfl

/-- **Second-order Taylor bound at a single input.** The scalar form of
`norm_trainingOutputs_netFromParams_sub_linearization_le`, valid at any (training or test) input
`x`: `|f(x; θ) - f(x; θ₀) - ⟪∇f(x; θ₀), θ - θ₀⟫| ≤ (K_x / (2 √n)) ‖θ - θ₀‖²`, where
`K_x² = 2 R² C₂² ‖x‖⁴ + 3 C₁² ‖x‖²` and `R` bounds the readout weights of `θ₀`. -/
theorem abs_netFromParams_sub_linearization_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d : ℕ) (hn : 0 < n) (x : Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    |netFromParams φ n d x θ - netFromParams φ n d x θ₀ -
        ⟪gradParams φ n d x θ₀, θ - θ₀⟫| ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) / 2 * ‖θ - θ₀‖ ^ 2 := by
  have h := norm_trainingOutputs_netFromParams_sub_linearization_le φ hφ n d 1 hn (fun _ => x)
    θ₀ θ C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip ha
  have hcoord : ∀ v : EuclideanSpace ℝ (Fin 1), ‖v‖ = |v 0| := fun v => by
    simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  rw [hcoord] at h
  simp only [trainingOutputs, PiLp.sub_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton] at h
  convert h using 2
  simp only [outputJacobian, Matrix.mulVec_apply, dotProduct, tangentFeature, PiLp.inner_apply]
  rw [gradient_netFromParams φ n d x θ₀ (fun _ => hφ _)]
  simp [mul_comm]

/-- **Lipschitz bound for the tangent feature at one input.** The packed gradient at an input `x`
is `(K_x / √n)`-Lipschitz relative to a base point `θ₀` whose readout weights are bounded by `R`,
`K_x² = 2 R² C₂² ‖x‖⁴ + 3 C₁² ‖x‖²`. This is `outputJacobian_netFromParams_frobenius_sub_le` for
the one-point dataset `{x}`, whose Jacobian is the row `∇f(x; θ)`. -/
theorem norm_gradParams_sub_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d : ℕ) (hn : 0 < n) (x : Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    ‖gradParams φ n d x θ - gradParams φ n d x θ₀‖ ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) * ‖θ - θ₀‖ := by
  have h := outputJacobian_netFromParams_frobenius_sub_le φ n d 1 hn (fun _ => x) θ₀ θ C₁ C₂ R
    hC₁_nonneg hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip (fun _ _ => hφ.differentiableAt)
    (fun _ _ => hφ.differentiableAt) ha
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [norm_sub_rev θ₀ θ] at h
  have hEq : ‖outputJacobian (netFromParams φ n d) (fun _ : Fin 1 => x) θ₀ -
      outputJacobian (netFromParams φ n d) (fun _ : Fin 1 => x) θ‖ =
      ‖gradParams φ n d x θ - gradParams φ n d x θ₀‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [matrix_frobenius_norm_sq, EuclideanSpace.real_norm_sq_eq]
    simp only [outputJacobian, Matrix.sub_apply, Matrix.of_apply, Finset.univ_unique,
      Finset.sum_singleton, tangentFeature_netFromParams_of_differentiable φ hφ, PiLp.sub_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact hEq ▸ h

/-- The empirical NTK Gram matrix of `netFromParams` decomposes into the sum of the
input-weight Gram matrix and the readout Gram matrix (empirical covariance). -/
theorem empiricalNTKMatrix_netFromParams_apply (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X θ α β =
      (∑ i : Fin n, gradW φ n d (X α) θ i ⊙ gradW φ n d (X β) θ i) +
      ∑ i : Fin n, gradA φ n d (X α) θ i * gradA φ n d (X β) θ i := by
  rw [empiricalNTKMatrix_apply]
  rw [tangentFeature_netFromParams φ n d (X α) θ (hφ α)]
  rw [tangentFeature_netFromParams φ n d (X β) θ (hφ β)]
  exact inner_packParams_packParams _ _ _ _

/-! ### Full Neuron-Sum Formula for the Empirical NTK

Derives the explicit single-sum representation of the full empirical NTK Gram matrix
from the two-block decomposition `empiricalNTKMatrix_netFromParams_apply`. Each Gram entry
is expressed directly as an empirical average over the `n` hidden neurons with both
activation and derivative-weight contributions.
-/

section FullTwoLayerNTKFormula

private lemma gradA_mul_gradA (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradA φ n d x θ i * gradA φ n d x' θ i =
      (n : ℝ)⁻¹ * (φ (unpackW θ i ⊙ x) * φ (unpackW θ i ⊙ x')) := by
  dsimp [gradA]
  have h_sqrt : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  calc
    ((n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ x)) * ((n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ x')) =
      ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) *
        (φ (unpackW θ i ⊙ x) * φ (unpackW θ i ⊙ x')) := by ring
    _ = (n : ℝ)⁻¹ * (φ (unpackW θ i ⊙ x) * φ (unpackW θ i ⊙ x')) := by rw [h_sqrt]

private lemma gradW_innerProduct_gradW (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradW φ n d x θ i ⊙ gradW φ n d x' θ i =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) *
        deriv φ (unpackW θ i ⊙ x') * (x ⊙ x')) := by
  have hW1 : gradW φ n d x θ i =
      fun j => ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x)) * x j := by
    ext j; rfl
  have hW2 : gradW φ n d x' θ i =
      fun j => ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x')) * x' j := by
    ext j; rfl
  rw [hW1, hW2, innerProduct_mul_mul]
  have h_sqrt : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  have h_alg : (((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x)) *
      ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x'))) * (x ⊙ x') =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) *
        deriv φ (unpackW θ i ⊙ x') * (x ⊙ x')) := by
    calc
      (((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x)) *
        ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x'))) * (x ⊙ x') =
        ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) *
          (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) *
            deriv φ (unpackW θ i ⊙ x') * (x ⊙ x')) := by ring
      _ = (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) *
            deriv φ (unpackW θ i ⊙ x') * (x ⊙ x')) := by rw [h_sqrt]
  exact h_alg

private lemma gradW_innerProduct_add_gradA_mul (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradW φ n d x θ i ⊙ gradW φ n d x' θ i + gradA φ n d x θ i * gradA φ n d x' θ i =
      (n : ℝ)⁻¹ *
        (φ (unpackW θ i ⊙ x) * φ (unpackW θ i ⊙ x') +
         unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) *
           deriv φ (unpackW θ i ⊙ x') * (x ⊙ x')) := by
  rw [gradW_innerProduct_gradW, gradA_mul_gradA]
  ring

/-- The full empirical NTK matrix of `netFromParams` evaluated at sample pair `(α, β)`
expressed explicitly as an empirical average over the `n` hidden neurons. -/
theorem empiricalNTKMatrix_netFromParams_eq_neuron_sum (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X θ α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ (unpackW θ i ⊙ X α) * φ (unpackW θ i ⊙ X β) +
         unpackA θ i ^ 2 *
           deriv φ (unpackW θ i ⊙ X α) *
           deriv φ (unpackW θ i ⊙ X β) *
           (X α ⊙ X β)) := by
  rw [empiricalNTKMatrix_netFromParams_apply φ n d m X θ hφ α β]
  rw [← Finset.sum_add_distrib]
  simp_rw [gradW_innerProduct_add_gradA_mul]
  rw [← Finset.mul_sum]

/-! ### Scaled-Dataset Network Evaluation and Gradients -/

lemma netFromParams_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ x)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [innerProduct_scaled_input]

lemma netFromParams_scaled_input_div (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((unpackW θ i ⊙ x) / Real.sqrt (d : ℝ)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [innerProduct_scaled_input_div]

lemma gradW_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) (j : Fin d) :
    gradW φ n d (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) θ i j =
      ((n : ℝ)⁻¹.sqrt * (Real.sqrt (d : ℝ))⁻¹) *
        (unpackA θ i * deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ x)) * x j) := by
  dsimp [gradW]
  rw [innerProduct_scaled_input]
  ring

lemma gradA_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradA φ n d (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) θ i =
      (n : ℝ)⁻¹.sqrt * φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ x)) := by
  dsimp [gradA]
  rw [innerProduct_scaled_input]

/-! ### Scaled-Dataset Corollaries -/

/-- The full empirical NTK matrix of `netFromParams` evaluated on the paper's scaled
dataset `(1 / √d) * X`, yielding the canonical two-layer NTK neuron-sum formula with
both activation covariance and `(1 / d) * (X α ⊙ X β)` derivative covariance. -/
theorem empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum
    (φ : ℝ → ℝ) (n d m : ℕ) (hd : 0 < d)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ (unpackW θ i ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ X α)) *
           φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ X β)) +
         unpackA θ i ^ 2 *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ X α)) *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ X β)) *
           ((d : ℝ)⁻¹ * (X α ⊙ X β))) := by
  rw [empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m _ θ hφ α β]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [innerProduct_scaled_input d (unpackW θ i) (X α)]
  rw [innerProduct_scaled_input d (unpackW θ i) (X β)]
  rw [innerProduct_scaled_dataset d hd (X α) (X β)]

/-! ### Sequence-Prefix Bridge -/

/-- The empirical NTK at the parameters obtained by packing the first `n` neurons of an
infinite sequence is the corresponding `n`-neuron empirical average. The packed parameter
expression is written explicitly to avoid introducing a thin sequence-parameter wrapper. -/
lemma empiricalNTKMatrix_netFromParams_of_seq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ)
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ ((seq i.val).1 ⊙ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((seq i.val).1 ⊙ X α) * φ ((seq i.val).1 ⊙ X β) +
          (seq i.val).2 ^ 2 *
            deriv φ ((seq i.val).1 ⊙ X α) * deriv φ ((seq i.val).1 ⊙ X β) *
              (X α ⊙ X β)) := by
  have h := empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m X
    (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2))
    (by intro α i; simp only [unpackW_packParams]; exact hφ α i) α β
  simpa only [unpackW_packParams, unpackA_packParams] using h

/-- Scaled-dataset version of `empiricalNTKMatrix_netFromParams_of_seq`, with the input
Gram factor written as `(X α ⊙ X β) / d`. -/
lemma empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq
    (φ : ℝ → ℝ) (n d m : ℕ) (hd : 0 < d)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ)
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ
        ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⊙ X α)) *
           φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⊙ X β)) +
         (seq i.val).2 ^ 2 *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⊙ X α)) *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⊙ X β)) *
           ((d : ℝ)⁻¹ * (X α ⊙ X β))) := by
  have h := empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum φ n d m hd X
    (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2))
    (by intro α i; simp only [unpackW_packParams]; exact hφ α i) α β
  simpa only [unpackW_packParams, unpackA_packParams] using h

/-- Matrix equation identifying the canonical empirical NTK on the scaled dataset at the
explicitly packed sequence-prefix parameters with the explicit neuron-average matrix. -/
lemma empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq_matrix
    {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ) (n : ℕ) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) =
    ((fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
           φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) +
         (seq i.val).2 ^ 2 *
           deriv φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
           deriv φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) *
           ((d : ℝ)⁻¹ * (X α ⊙ X β)))) : Matrix (Fin m) (Fin m) ℝ) := by
  ext α β
  have h_entry := empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq φ n d m hd X seq
    (fun α i => hφ_diff.differentiableAt) α β
  rw [h_entry]
  simp_rw [innerProduct_mul_right]

/-- Almost-sure convergence of the canonical empirical NTK matrix at the explicitly packed
sequence-prefix initialization parameters to `limitingFullNTKMatrix`. -/
theorem empiricalNTKMatrix_netFromParams_scaled_dataset_tendsto_limitingFullNTKMatrix
    {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ =>
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)))
        Filter.atTop
        (nhds (limitingFullNTKMatrix φ X)) := by
  have h_slln := fullNTKMatrix_scaled_dataset_tendsto_limitingFullNTKMatrix hd φ
    hφ_meas hdφ_meas X hφ_int hdφ_int
  filter_upwards [h_slln] with seq hseq
  have heq (n : ℕ) :
      empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) =
      ((fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n,
          (φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
             φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) +
           (seq i.val).2 ^ 2 *
             deriv φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
             deriv φ ((seq i.val).1 ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) *
             ((d : ℝ)⁻¹ * (X α ⊙ X β)))) : Matrix (Fin m) (Fin m) ℝ) :=
    empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq_matrix hd φ hφ_diff X seq n
  simp_rw [heq]
  exact hseq

end FullTwoLayerNTKFormula

/-! ### Finite-Width NTK Concentration and Transport to `initMeasure` -/

section FiniteWidthNTKConcentration

/-- Evaluation of `empiricalNTKMatrix` on parameters unpacked from the product measure
via `arrowProdEquivProdArrow` matches the single-neuron average summand. -/
private lemma empiricalNTKMatrix_packed_arrowProd_eq_summand {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (n : ℕ)
    (ω : Fin n → (Fin d → ℝ) × ℝ) (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1
                  (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
           φ ((ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
         (ω i).2 ^ 2 *
           deriv φ ((ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
           deriv φ ((ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
           ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⊙
             (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) := by
  have h := empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum φ n d m hd X
    (packParams (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1
                (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2)
    (fun _ _ => hφ_diff.differentiableAt) α β
  rw [h]
  simp only [unpackW_packParams, unpackA_packParams]
  have h_prod : (d : ℝ)⁻¹ * (X α ⊙ X β) =
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) :=
    (innerProduct_scaled_dataset d hd (X α) (X β)).symm
  rw [h_prod]
  have h_w (i : Fin n) :
      (Real.sqrt (d : ℝ))⁻¹ *
        ((MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1 i ⊙ X α) =
      (ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) := by
    rw [innerProduct_mul_right]
    rfl
  have h_w' (i : Fin n) :
      (Real.sqrt (d : ℝ))⁻¹ *
        ((MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1 i ⊙ X β) =
      (ω i).1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) := by
    rw [innerProduct_mul_right]
    rfl
  have h_a (i : Fin n) :
      (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2 i =
      (ω i).2 := rfl
  simp_rw [h_w, h_w', h_a]

/-- Finite-width entrywise Chebyshev concentration of the empirical NTK matrix under
the joint initialization measure `initMeasure n d`. -/
theorem chebyshev_entrywise_empiricalNTKMatrix
    {m d : ℕ} (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (n : ℕ) (hn : 0 < n) (α β : Fin m) {c : ℝ} (hc : 0 < c) :
    (initMeasure n d)
      {p | c ≤ |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) α β - limitingFullNTKMatrix φ X α β|} ≤
      ENNReal.ofReal (fullNTKSummandSecondMoment d φ X α β / ((n : ℝ) * c ^ 2)) := by
  have h_meas_eq : (initMeasure n d) =
      (Measure.pi fun _ : Fin n => singleNeuronMeasure d).map
        (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)) :=
    (measurePreserving_arrowProd_singleNeuronMeasure n d).map_eq.symm
  rw [h_meas_eq, MeasurableEquiv.map_apply]
  set Y := fun u : (Fin d → ℝ) × ℝ =>
    φ (u.1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       φ (u.1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
     u.2 ^ 2 * deriv φ (u.1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       deriv φ (u.1 ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
       ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))
  have hY_L2 : MemLp Y 2 (singleNeuronMeasure d) :=
    memLp_two_fullNTK_summand φ hdφ_meas
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)
      (hφ_L2 α β) (hdφ_L2 α β)
  have h_cheb := chebyshev_average_pi_le_second_moment (singleNeuronMeasure d) hn Y hY_L2 hc
  have h_int : ∫ x, Y x ∂(singleNeuronMeasure d) = limitingFullNTKMatrix φ X α β :=
    integral_fullNTK_summand_scaled_dataset_eq_limiting hd φ X
      (fun a b => (hφ_L2 a b).integrable (by norm_num))
      (fun a b => (hdφ_L2 a b).integrable (by norm_num)) α β
  rw [h_int] at h_cheb
  have h_set_eq : (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)) ⁻¹'
      {p | c ≤ |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) α β - limitingFullNTKMatrix φ X α β|} =
      {ω | c ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i) - limitingFullNTKMatrix φ X α β|} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [empiricalNTKMatrix_packed_arrowProd_eq_summand hd φ hφ_diff X n ω α β]
  rw [h_set_eq]
  exact h_cheb

/-- If a matrix has Frobenius norm at least `ε`, at least one entry has absolute value at
least `ε / m`. Kept private to `NetworkParam.lean` until a second caller appears. -/
private lemma exists_entry_ge_of_frobenius_ge {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε) (hA : ε ≤ ‖A‖) :
    ∃ p : Fin m × Fin m, ε / (m : ℝ) ≤ |A p.1 p.2| := by
  by_contra! h_all
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have h_ne : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 hm
  have h_entry : ∀ (i j : Fin m), ‖A i j‖ ^ (2 : ℝ) < (ε / (m : ℝ)) ^ (2 : ℝ) := by
    intro i j
    have := h_all (i, j)
    rw [Real.norm_eq_abs]
    have h1 : 0 ≤ |A i j| := abs_nonneg _
    have h2 : 0 < ε / (m : ℝ) := div_pos hε hm_pos
    exact Real.rpow_lt_rpow h1 this (by norm_num)
  have h_sum_inner : ∀ (i : Fin m), ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) <
      (m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ) := by
    intro i
    have h : ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) < ∑ _j : Fin m, (ε / (m : ℝ)) ^ (2 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 h_ne) (fun j _ => h_entry i j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have h_sum_outer : ∑ i : Fin m, (∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) <
      (m : ℝ) * ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) := by
    have h : ∑ i : Fin m, (∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) <
        ∑ _i : Fin m, ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 h_ne) (fun i _ => h_sum_inner i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have heq : (m : ℝ) * ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) = ε ^ (2 : ℝ) := by
    have hm_ne : ((m : ℝ) ^ (2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hm_pos 2).ne'
    rw [Real.div_rpow hε.le hm_pos.le]
    calc (m : ℝ) * ((m : ℝ) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)))
      _ = ((m : ℝ) * (m : ℝ)) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)) := by ring
      _ = ((m : ℝ) ^ (2 : ℝ)) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)) := by
        congr 1
        rw [Real.rpow_two]
        ring
      _ = ε ^ (2 : ℝ) := mul_div_cancel₀ _ hm_ne
  rw [heq] at h_sum_outer
  rw [Matrix.frobenius_norm_def] at hA
  have h_sum_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have h_norm_lt : (∑ i : Fin m, ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) <
      (ε ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_lt_rpow h_sum_nonneg h_sum_outer (by norm_num)
  have heq2 : (ε ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ε := by
    rw [← Real.rpow_mul hε.le]
    norm_num
  rw [heq2] at h_norm_lt
  exact not_lt_of_ge hA h_norm_lt

/-- Finite-width matrix Chebyshev concentration of the empirical NTK in Frobenius norm
under the joint initialization measure `initMeasure n d`. -/
theorem chebyshev_matrix_empiricalNTKMatrix
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (initMeasure n d)
      {p | ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
      ENNReal.ofReal (((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * ε ^ 2)) := by
  set E : Fin m × Fin m → Set (Matrix (Fin n) (Fin d) ℝ × (Fin n → ℝ)) := fun p =>
    {pt | ε / (m : ℝ) ≤
      |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) p.1 p.2 - limitingFullNTKMatrix φ X p.1 p.2|}
  have h_sub : {pt | ε ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X‖} ⊆
      ⋃ p : Fin m × Fin m, E p := by
    intro pt hpt
    simp only [Set.mem_ofPred_eq] at hpt
    have h_ex := exists_entry_ge_of_frobenius_ge hm
      (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X) hε hpt
    rcases h_ex with ⟨p, hp⟩
    simp only [Set.mem_iUnion]
    exact ⟨p, hp⟩
  have h_meas_union : (initMeasure n d)
      {pt | ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X‖} ≤
      (initMeasure n d) (⋃ p : Fin m × Fin m, E p) :=
    measure_mono h_sub
  have h_union_le : (initMeasure n d) (⋃ p : Fin m × Fin m, E p) ≤
      ∑ p : Fin m × Fin m, (initMeasure n d) (E p) :=
    measure_iUnion_fintype_le (initMeasure n d) _
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have h_eps_m_pos : 0 < ε / (m : ℝ) := div_pos hε hm_pos
  have h_entry_le : ∀ p : Fin m × Fin m, (initMeasure n d) (E p) ≤
      ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    fun p => chebyshev_entrywise_empiricalNTKMatrix hd φ hφ_diff hdφ_meas X hφ_L2 hdφ_L2 n hn
      p.1 p.2 h_eps_m_pos
  have h_sum_le : (∑ p : Fin m × Fin m, (initMeasure n d) (E p)) ≤
      ∑ p : Fin m × Fin m,
        ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 /
          ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    Finset.sum_le_sum fun p _ => h_entry_le p
  refine h_meas_union.trans (h_union_le.trans (h_sum_le.trans ?_))
  have hn_eps_pos : 0 < (n : ℝ) * (ε / (m : ℝ)) ^ 2 :=
    mul_pos (Nat.cast_pos.2 hn) (sq_pos_of_ne_zero h_eps_m_pos.ne')
  have h_nonneg : ∀ p : Fin m × Fin m,
      0 ≤ fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2) :=
    fun p => div_nonneg (fullNTKSummandSecondMoment_nonneg d φ X p.1 p.2) hn_eps_pos.le
  have h_sum_eq :
      (∑ p : Fin m × Fin m,
        ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2))) =
      ENNReal.ofReal (∑ p : Fin m × Fin m,
        fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    (ENNReal.ofReal_sum_of_nonneg fun p _ => h_nonneg p).symm
  rw [h_sum_eq]
  have heq : (∑ p : Fin m × Fin m,
        fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) =
      ((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * ε ^ 2) := by
    rw [← Finset.sum_div]
    rw [div_pow]
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    calc (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
          ((n : ℝ) * (ε ^ 2 / (m : ℝ) ^ 2))
      _ = (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
            (((n : ℝ) * ε ^ 2) / (m : ℝ) ^ 2) := by
        congr 1
        ring
      _ = (m : ℝ) ^ 2 * (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
            ((n : ℝ) * ε ^ 2) := by
        rw [div_div_eq_mul_div]
        ring
  rw [heq]

/-- Qualitative finite-width convergence in probability of the empirical NTK matrix to
`limitingFullNTKMatrix` under the varying initialization measure `initMeasure n d`. -/
theorem tendsto_initMeasure_empiricalNTKMatrix_ge_eps
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖})
      Filter.atTop
      (nhds 0) := by
  let C := (m : ℝ) ^ 2 * ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2
  have h_le : ∀ n : ℕ, 0 < n →
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
        ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2)) := fun n hn =>
    chebyshev_matrix_empiricalNTKMatrix hm hd φ hφ_diff hdφ_meas X hφ_L2 hdφ_L2 n hn hε
  have h_real : Filter.Tendsto (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) Filter.atTop (nhds 0) := by
    have h_const : (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) =
        (fun n : ℕ => (C / ε ^ 2) * (n : ℝ)⁻¹) := by
      ext n
      ring
    rw [h_const]
    have h_inv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_mul := Filter.Tendsto.const_mul (C / ε ^ 2) h_inv
    rw [mul_zero] at h_mul
    exact h_mul
  have h_lim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2))) Filter.atTop
      (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal h_real
  have h_le_eventually : ∀ᶠ n in Filter.atTop,
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
        ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact h_le n (Nat.zero_lt_one.trans_le hn)
  have h_bot : ∀ᶠ n in Filter.atTop, 0 ≤
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} := by
    filter_upwards with n
    exact bot_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim h_bot h_le_eventually



/-- If the empirical NTK at initialization is within Frobenius distance `lambda_inf / 2` of
`limitingFullNTKMatrix φ X`, it satisfies the Rayleigh quotient lower bound
`(lambda_inf / 2) ‖v‖²`. -/
theorem initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
    {m d : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (n : ℕ) (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (lambda_inf : ℝ)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (h_dist : ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖ ≤ lambda_inf / 2)
    (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_inf / 2) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) *ᵥ v.ofLp) := by
  have h_rr₀ := rayleigh_lower_bound_of_sub_smul_posSemidef (limitingFullNTKMatrix φ X)
    lambda_inf hK_gap
  have h_bound := rayleigh_quotient_lower_bound_of_matrix_dist
    (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams p.1 p.2))
    (limitingFullNTKMatrix φ X) lambda_inf (lambda_inf / 2) h_rr₀ h_dist v
  have heq : lambda_inf - lambda_inf / 2 = lambda_inf / 2 := by ring
  rwa [heq] at h_bound

/-- Finite-width probability bound for initial empirical NTK spectral gap failure under
`initMeasure n d`.
By Chebyshev's inequality and Rayleigh perturbation, the probability that the empirical NTK fails to
satisfy the spectral lower bound `(lambda_inf / 2) ‖v‖²` decays as `O(1 / n)`. -/
theorem chebyshev_matrix_empiricalNTKMatrix_spectral_gap_failure
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (n : ℕ) (hn : 0 < n) :
    (initMeasure n d)
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
        (lambda_inf / 2) * ‖v‖ ^ 2 ≤
          v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ≤
      ENNReal.ofReal (((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * (lambda_inf / 2) ^ 2)) := by
  have h_sub : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_inf / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ⊆
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | lambda_inf / 2 ≤
        ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
          (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    by_contra! h_lt
    exact hp (initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
      φ X n p lambda_inf hK_gap h_lt.le)
  have h_failure_le_tail : (initMeasure n d)
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
        (lambda_inf / 2) * ‖v‖ ^ 2 ≤
          v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ≤
      (initMeasure n d)
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | lambda_inf / 2 ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} :=
    measure_mono h_sub
  have h_eps_pos : 0 < lambda_inf / 2 := half_pos hlambda_inf
  exact h_failure_le_tail.trans (chebyshev_matrix_empiricalNTKMatrix hm hd φ hφ_diff hdφ_meas X
    hφ_L2 hdφ_L2 n hn h_eps_pos)

/-- Spectral-gap failure measure tends to zero:
the measure of the set where the empirical NTK fails the Rayleigh lower bound
`(lambda_inf / 2) ‖v‖²` tends to 0 as width `n → ∞`. -/
theorem tendsto_initMeasure_initial_spectral_gap_failure
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef) :
    Filter.Tendsto
      (fun n : ℕ => (initMeasure n d)
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
          (lambda_inf / 2) * ‖v‖ ^ 2 ≤
            v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)})
      Filter.atTop
      (nhds 0) := by
  have h_eps_pos : 0 < lambda_inf / 2 := half_pos hlambda_inf
  have h_tail := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ_diff hdφ_meas X
    hφ_L2 hdφ_L2 (hε := h_eps_pos)
  apply Filter.Tendsto.squeeze' tendsto_const_nhds h_tail
  · filter_upwards with n
    exact bot_le
  · filter_upwards with n
    exact measure_mono (fun p hp => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      by_contra! h_lt
      exact hp (initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
        φ X n p lambda_inf hK_gap h_lt.le))

end FiniteWidthNTKConcentration

section JointOutputKernelInitialization

/-- Second countability of `Matrix (Fin m) (Fin m) ℝ` for the topology derived from the Frobenius
norm, which is what lemmas quantified over `[SeminormedAddCommGroup E']` see once
`Matrix.frobeniusNormedAddCommGroup` is a local instance. Mathlib's default (product) topology on
`Matrix` is a different term, defeq to this one only at default transparency, so typeclass search
does not accept an instance stated for the default topology; we therefore pin the topology
explicitly. -/
local instance (priority := 2000) instSecondCountableTopologyMatrixFrobenius (m : ℕ) :
    @SecondCountableTopology (Matrix (Fin m) (Fin m) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            Matrix.frobeniusNormedAddCommGroup)))) := by
  let : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) := Matrix.frobeniusNormedAddCommGroup
  let : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) := Matrix.frobeniusNormedSpace
  exact @secondCountable_of_proper _ NormedAddCommGroup.toSeminormedAddCommGroup.toPseudoMetricSpace
    (FiniteDimensional.proper_real (Matrix (Fin m) (Fin m) ℝ))

/-- `BorelSpace` for the Frobenius-derived topology on `Matrix (Fin m) (Fin m) ℝ`; see
`instSecondCountableTopologyMatrixFrobenius`. -/
local instance (priority := 2000) instBorelSpaceMatrixFrobenius (m : ℕ) :
    @BorelSpace (Matrix (Fin m) (Fin m) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _ Matrix.frobeniusNormedAddCommGroup))))
      Matrix.instMeasurableSpace := by
  exact (inferInstance : BorelSpace (Matrix (Fin m) (Fin m) ℝ))

/-- Measurability of the empirical NTK matrix evaluated on packed parameters
`packParams p.1 p.2` on an arbitrary dataset `X`. -/
lemma measurable_empiricalNTKMatrix_netFromParams_packParams
    {m d n : ℕ} (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) :
    Measurable (fun (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) := by
  change Measurable (fun (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) (α β : Fin m) =>
    empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) α β)
  rw [measurable_pi_iff]
  intro α
  rw [measurable_pi_iff]
  intro β
  have h_eq : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) α β) =
      fun p => (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ (p.1 i ⊙ X α) * φ (p.1 i ⊙ X β) +
         p.2 i ^ 2 * deriv φ (p.1 i ⊙ X α) * deriv φ (p.1 i ⊙ X β) * (X α ⊙ X β)) := by
    ext p
    have h := empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m X
      (packParams p.1 p.2) (fun _ _ => hφ_diff.differentiableAt) α β
    simp only [unpackW_packParams, unpackA_packParams] at h
    exact h
  rw [h_eq]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  have h_w : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have h_a : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h_wx (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      p.1 i ⊙ X k) :=
    (measurable_innerProduct_left (X k)).comp h_w
  have h_φ (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      φ (p.1 i ⊙ X k)) :=
    hφ_diff.continuous.measurable.comp (h_wx k)
  have h_dφ (k : Fin m) : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      deriv φ (p.1 i ⊙ X k)) :=
    hdφ_meas.comp (h_wx k)
  have h_a2 : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2 i ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  exact (h_φ α).mul (h_φ β) |>.add <|
    ((h_a2.mul (h_dφ α)).mul (h_dφ β)).mul_const _

/-- Initial training residual weak limit on the paper's scaled dataset `(1 / √d) * X`:
the residual under initialization converges in distribution to `G - y`,
where `G ~ 𝒩(0, Φ^{(∞)}(X / √d))`. -/
theorem tendstoInDistribution_initial_trainingResidual
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (gaussianRowMeasure d)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2))
      Filter.atTop
      (fun G => G - y)
      (fun n => initMeasure n d)
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  simp_rw [trainingResidual_netFromParams_packParams]
  exact tendstoInDistribution_initialResidual_evalVector φ X y hφ_meas hφ_L2

/-- **Theorem (Joint Output and NTK Weak Convergence at Initialization)**:
As width `n → ∞`, the joint law of the initial training residual
`r_n(0) = trainingResidual (netFromParams φ n d) X_scaled y θ_0`
and the full empirical NTK matrix
`K_n(0) = empiricalNTKMatrix (netFromParams φ n d) X_scaled θ_0`
converges in distribution to the joint pair `(G - y, limitingFullNTKMatrix φ X)`
under `initMeasure n d`, where `G ~ 𝒩(0, Φ^{(∞)})` and `K_∞` is deterministic. -/
theorem tendstoInDistribution_joint_initial_residual_empiricalNTK
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        (trainingResidual (netFromParams φ n d)
           (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2),
         empiricalNTKMatrix (netFromParams φ n d)
           (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)))
      Filter.atTop
      (fun G => (G - y, limitingFullNTKMatrix φ X))
      (fun n => initMeasure n d)
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have hX := tendstoInDistribution_initial_trainingResidual φ X y
    hφ_diff.continuous.measurable fun α => memLp_two_of_memLp_two_mul_self
      ((hφ_diff.continuous.measurable.comp
        (measurable_innerProduct_left _)).aestronglyMeasurable) (hφ_L2 α α)
  have hY : ∀ ε > 0, Filter.Tendsto
      (fun n => (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
            limitingFullNTKMatrix φ X‖})
      Filter.atTop (nhds 0) :=
    fun ε hε => tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ_diff hdφ_meas X
      hφ_L2 hdφ_L2 hε
  have hY_meas : ∀ n, AEMeasurable (fun p => empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)) (initMeasure n d) :=
    fun n => (measurable_empiricalNTKMatrix_netFromParams_packParams φ hφ_diff hdφ_meas
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)).aemeasurable
  exact hX.prodMk_of_tendsto_measure_norm_sub_const hY hY_meas

/-- **Uniform residual radius at initialization.** For every failure level `ε > 0` there is a
single deterministic radius `R ≥ 0`, valid for all widths `n`, such that the initial training
residual on the scaled dataset exceeds `R` in norm with `initMeasure n d`-probability at most `ε`.
This is output-law tightness (from the characteristic-function limit) translated by `-y`. -/
theorem exists_initial_residual_radius
    {d m : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hφ_meas : Measurable φ)
    (hφ_L2 : ∀ α, MemLp (fun w => φ (w ⊙ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) 2
      (gaussianRowMeasure d))
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, initMeasure n d
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | R <
        ‖trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖} ≤ ε := by
  have hmeas : ∀ n, Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) := fun n =>
    evalVector_joint_measurable φ hφ_meas _
  have htight := (isTightMeasureSet_range_outputMeasure_scaled_dataset φ X hφ_meas hφ_L2).map
    (continuous_sub_right y)
  simp_rw [trainingResidual_netFromParams_packParams]
  refine exists_forall_measure_norm_gt_le_of_isTightMeasureSet_map
    (μ := fun n => initMeasure n d)
    (X := fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
      evalVector φ p.1 p.2 (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) - y)
    (fun n => ((hmeas n).sub_const y).aemeasurable) htight
    (fun n => ⟨outputMeasure n d φ _, Set.mem_range_self n, ?_⟩) hε
  rw [outputMeasure_eq_map, Measure.map_map (measurable_sub_const y) (hmeas n)]
  rfl

/-- The event that the initial empirical NTK on an arbitrary dataset is at least `ε` away, in
Frobenius norm, from a fixed matrix is measurable. The Frobenius topology instances are local to
this section, so this measurability fact is proved here for use by later event constructions. -/
lemma measurableSet_empiricalNTKMatrix_dist_ge
    {m d n : ℕ} (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2) - K_inf‖} :=
  measurableSet_le measurable_const
    ((measurable_empiricalNTKMatrix_netFromParams_packParams φ hφ_diff hdφ_meas X).sub_const
      K_inf).norm

end JointOutputKernelInitialization



/-! ### Phase 6: End-to-End Kernel-Freeze Bound

Wires Gaps 1-5 together with the Gaussian-initialized two-layer network: Gap 3's Jacobian-norm
concentration and Gap 4b's entrywise readout-weight concentration (both at `θ₀`) combine via a
union bound into one high-probability event; on that event, Gap 4's Lipschitz bound propagates
both the Jacobian norm and the readout-weight bound through the displacement ball (the same
"ball propagation" pattern `rayleigh_quotient_lower_bound_of_displacement`/`h_rr_ball` already use
in `InfiniteNTK.lean`); the result feeds directly into
`lazy_training_kernel_freeze_bound_of_ball_hypotheses`.
-/

/-- Deterministic ball-propagation of an entrywise readout-weight bound: if `θ₀`'s readout
weight `a i` is bounded by `R₀` and `θ` is within displacement `r` of `θ₀`, then `θ`'s readout
weight `a i` is bounded by `R₀ + r`. This is what lets a concentration bound established only at
the random initialization `θ₀` (Gap 4b) supply the uniform-over-a-ball bound Gap 4's Lipschitz
theorem needs. -/
private lemma abs_unpackA_le_of_displacement {n d : ℕ}
    (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n)))
    (i : Fin n) (R₀ r : ℝ) (h₀ : |unpackA θ₀ i| ≤ R₀) (hr : ‖θ - θ₀‖ ≤ r) :
    |unpackA θ i| ≤ R₀ + r := by
  have hproj : |(θ - θ₀).ofLp (idxA i)| ≤ ‖θ - θ₀‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (θ - θ₀) (idxA i)
  have heq : unpackA θ i - unpackA θ₀ i = (θ - θ₀).ofLp (idxA i) := by dsimp [unpackA]
  have hdiff : |unpackA θ i - unpackA θ₀ i| ≤ r := heq ▸ hproj.trans hr
  have h1 := abs_le.mp h₀
  have h2 := abs_le.mp hdiff
  rw [abs_le]
  constructor <;> linarith

/-- **Gaussian-initialization good event for the kernel-freeze bound.** There is a measurable event
`E` of `initMeasure n d`-probability `≥ 1 - 2δ` on which both the initial Jacobian norm and every
readout weight are controlled (Gap 3's Jacobian-norm concentration and Gap 4b's entrywise
readout-weight concentration, combined by a union bound). Deterministic consequences of membership
in `E` are in `freeze_bound_of_initial_jacobian_and_readout_bounds`. -/
lemma exists_measurableSet_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (hφ : Differentiable ℝ φ) (hφ_meas : Measurable φ) (hderiv_meas : Measurable (deriv φ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (M₀ : ℝ)
    (hE1 : (initMeasure n d).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ M₀} ≥ 1 - δ) :
    ∃ E : Set (((Fin n → Fin d → ℝ) × (Fin n → ℝ))),
      MeasurableSet E ∧ (initMeasure n d).real E ≥ 1 - 2 * δ ∧
      ∀ p ∈ E,
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          M₀ ∧
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  have hE2 := initMeasure_forall_abs_readout_ge n d hn hδ hδ1
  have hpi_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have hpre_meas : ∀ α : Fin m, ∀ i : Fin n,
      Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1 i ⊙ X α) := by
    intro α i
    unfold innerProduct
    exact Finset.measurable_sum _ (fun j _ => (hpi_meas i j).mul measurable_const)
  have hE1_meas : MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
        M₀} := by
    have hmeas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) := by
      have heq : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) =
          (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
            (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
              (gradW φ n d (X α) (packParams p.1 p.2) i j) ^ 2) +
            ∑ α : Fin m, ∑ i : Fin n, (gradA φ n d (X α) (packParams p.1 p.2) i) ^ 2) := by
        funext p
        exact outputJacobian_netFromParams_frobenius_norm_sq φ n d m X (packParams p.1 p.2)
          (fun α i => hφ.differentiableAt)
      rw [heq]
      simp only [gradW, gradA, unpackW_packParams, unpackA_packParams]
      refine Measurable.add ?_ ?_
      · exact Finset.measurable_sum _ (fun α _ => Finset.measurable_sum _ (fun i _ =>
          Finset.measurable_sum _ (fun j _ => ((((measurable_const.mul
            ((measurable_pi_apply i).comp measurable_snd)).mul
            (hderiv_meas.comp (hpre_meas α i))).mul measurable_const)).pow_const 2)))
      · exact Finset.measurable_sum _ (fun α _ => Finset.measurable_sum _ (fun i _ =>
          (measurable_const.mul (hφ_meas.comp (hpre_meas α i))).pow_const 2))
    have hmeas' : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖) := by
      have heq2 : (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖) =
          fun p => Real.sqrt
            (‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2) := by
        funext p; rw [Real.sqrt_sq (norm_nonneg _)]
      rw [heq2]
      exact Real.continuous_sqrt.measurable.comp hmeas
    exact measurableSet_le hmeas' measurable_const
  have hE2_meas : MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
    have hset : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} =
        ⋂ i : Fin n, {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply i).comp measurable_snd))
      measurable_const)
  have hcombined := measureReal_inter_ge_of_ge (initMeasure n d) hE1_meas hE2_meas hE1 hE2
  have hδ2 : (1 : ℝ) - δ - δ = 1 - 2 * δ := by ring
  rw [hδ2] at hcombined
  exact ⟨_, hE1_meas.inter hE2_meas, hcombined, fun p hp => hp⟩

/-- **Jacobian bounds on a ball around a good initialization.** If at `θ₀ = packParams W a` the
Jacobian norm and all readout weights satisfy the Gap 3/4b bounds, then on the closed ball of
radius `r` around `θ₀` the output Jacobian is `M`-bounded and `L_J`-Lipschitz (relative to `θ₀`),
for any `M`, `L_J` dominating the concrete formulas. Shared by the gap and no-gap bootstraps. -/
lemma jacobian_ball_bounds_of_initial_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (r L_J M : ℝ) (hr_nonneg : 0 ≤ r) (hL_J : 0 ≤ L_J)
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J) :
    (∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M) ∧
    (∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          L_J * ‖θ - packParams p.1 p.2‖) := by
  set θ₀ := packParams p.1 p.2 with hθ₀_def
  set R₀ : ℝ := Real.sqrt (2 * Real.log (2 * n / δ)) with hR₀_def
  have hR₀_i : ∀ i : Fin n, |unpackA θ₀ i| ≤ R₀ := by
    intro i
    have hival : unpackA θ₀ i = p.2 i := by
      rw [hθ₀_def]; exact congrFun (unpackA_packParams p.1 p.2) i
    rw [hival]; exact hp2 i
  -- Gap 4, applied on the ball of radius `r`: the Jacobian is `L_J`-Lipschitz there, since
  -- every `θ` with `‖θ - θ₀‖ ≤ r` has readout weights bounded by `R₀ + r` (deterministic
  -- ball-propagation of the entrywise concentration bound, `abs_unpackA_le_of_displacement`).
  have hJ_lip_ball : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X θ₀‖ ≤ L_J * ‖θ - θ₀‖ := by
    intro θ hθ
    have hRθ : ∀ i : Fin n, |unpackA θ i| ≤ R₀ + r :=
      fun i => abs_unpackA_le_of_displacement θ θ₀ i R₀ r (hR₀_i i) hθ
    have hKle := outputJacobian_netFromParams_frobenius_sub_le φ n d m hn X θ θ₀ C₁ C₂ (R₀ + r)
      hC₁_nonneg hC₂_nonneg (by positivity) hφ_lip hC₁_bdd hderiv_lip
      (fun _ _ => hφ.differentiableAt) (fun _ _ => hφ.differentiableAt) hRθ
    dsimp only at hKle
    exact hKle.trans (mul_le_mul_of_nonneg_right hL_J_ge (norm_nonneg _))
  have hJ_bdd_ball : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M := by
    intro θ hθ
    have hstep : ‖outputJacobian (netFromParams φ n d) X θ‖ ≤
        ‖outputJacobian (netFromParams φ n d) X θ₀‖ +
        ‖outputJacobian (netFromParams φ n d) X θ - outputJacobian (netFromParams φ n d) X θ₀‖ :=
      norm_le_insert' _ _
    have h1 : ‖outputJacobian (netFromParams φ n d) X θ₀‖ ≤ M₀ := hp1
    have h2 : ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X θ₀‖ ≤ L_J * r :=
      (hJ_lip_ball θ hθ).trans (mul_le_mul_of_nonneg_left hθ hL_J)
    calc
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M₀ + L_J * r := hstep.trans (add_le_add h1 h2)
      _ ≤ M := hM_ge
  exact ⟨hJ_bdd_ball, hJ_lip_ball⟩

/-- **Deterministic half of the lazy-training bounds.** If the initial Jacobian norm and all
readout weights at `θ₀ = packParams W a` satisfy the Gap 3/4b bounds, then for any gradient flow
from `θ₀` and any radius/constant choice obeying the Gap 5/6 relations, for all `t ≥ 0`: the flow
stays within `C` of `θ₀`, the Rayleigh quotient stays above `lambda_min₀ / 2`, the empirical NTK
drifts by at most `(2 * M * L_J) * C`, and the residual norm and MSE loss decay exponentially.
`freeze_bound_of_initial_jacobian_and_readout_bounds` is the drift component. -/
lemma lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ /
      (lambda_min₀ / 2) ≤ C)
    :
    ∀ t : ℝ, 0 ≤ t →
      ‖θ_traj t - packParams p.1 p.2‖ ≤ C ∧
      (∀ v : EuclideanSpace ℝ (Fin m), (lambda_min₀ / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t)) *ᵥ v.ofLp)) ∧
      ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
        empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ (2 * M * L_J) * C ∧
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤
        ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ *
          Real.exp (-((lambda_min₀ / 2) / (m : ℝ)) * t) ∧
      mseLoss (netFromParams φ n d) X y (θ_traj t) ≤
        mseLoss (netFromParams φ n d) X y (packParams p.1 p.2) *
          Real.exp (-(2 * (lambda_min₀ / 2) / (m : ℝ)) * t) := by
  obtain ⟨hJ_bdd_ball, hJ_lip_ball⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn X C₁
    C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r L_J M hr_nonneg hL_J
    hM_ge hL_J_ge
  exact lazy_training_global_bounds_of_ball_hypotheses (netFromParams φ n d) X y hflow
    hdiff M L_J lambda_min₀ r C hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀
    hJ_bdd_ball hJ_lip_ball

/-- **Deterministic half of the kernel-freeze bound.** If the initial Jacobian norm and all
readout weights at `θ₀ = packParams W a` satisfy the Gap 3/4b bounds (as they do on the event of
`exists_measurableSet_initial_jacobian_and_readout_bounds`), then for any gradient flow from `θ₀`
and any radius/constant choice obeying the Gap 5/6 relations, the empirical NTK stays within
`(2 * M * L_J) * C` of its initial value for all `t ≥ 0`. -/
lemma freeze_bound_of_initial_jacobian_and_readout_bounds
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ} (M₀ : ℝ)
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      M₀)
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : M₀ + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J)
    (h_ball_gap : 2 * M * L_J * r ≤ lambda_min₀ / 2)
    (hC_ge : M * ‖trainingResidual (netFromParams φ n d) X y (packParams p.1 p.2)‖ /
      (lambda_min₀ / 2) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
      empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ (2 * M * L_J) * C :=
  (lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm M₀ p hp1 hp2 θ_traj lambda_min₀ r C M L_J
    hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀ hM_ge hL_J_ge h_ball_gap hC_ge t ht).2.2.1

/-- **Phase 6: fully probabilistic end-to-end kernel-freeze bound for the Gaussian-initialized
two-layer network.** With probability `≥ 1 - 2δ` over the joint Gaussian initialization
`(W, a)` of `netFromParams`, the following holds at `θ₀ := packParams W a`: for *any* gradient
flow starting at `θ₀` with a base spectral-gap `lambda_min₀` there, and *any* choice of ball
radius `r`, target bound `C`, Jacobian bound `M` and Lipschitz constant `L_J` satisfying the
Gap 5/6 relations (`hCr`, `h_ball_gap`, `hC_ge`) and dominating the concrete Gap 3/4 formulas
(`hM_ge`, `hL_J_ge`), the empirical NTK matrix never drifts from its value at `θ₀` by more than
`(2 * M * L_J) * C`, for any `t ≥ 0`. No free `hlazy`/`hLip` hypotheses remain anywhere in this
chain - both are derived from the Gaussian initialization, not assumed. -/
theorem lazy_training_kernel_freeze_bound_of_gaussian_init
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (C₀ C₁ C₂ : ℝ) (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂)
    (hφ : Differentiable ℝ φ) (hφ_meas : Measurable φ) (hderiv_meas : Measurable (deriv φ))
    (hm : 0 < (m : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (initMeasure n d).real
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        let θ₀ := packParams p.1 p.2
        ∀ (θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)))
          (lambda_min₀ r C M L_J : ℝ),
          ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj →
          (∀ t : ℝ, ∀ β : Fin m,
            DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t)) →
          0 < lambda_min₀ → 0 ≤ r → C < r → 0 ≤ M → 0 ≤ L_J →
          (∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
            v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X θ₀) *ᵥ v.ofLp)) →
          Real.sqrt ((m : ℝ) * C₀ ^ 2 +
              (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) + L_J * r ≤ M →
          Real.sqrt (∑ α : Fin m,
              (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
                (∑ j : Fin d, X α j ^ 2) ^ 2 +
              3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J →
          2 * M * L_J * r ≤ lambda_min₀ / 2 →
          M * ‖trainingResidual (netFromParams φ n d) X y θ₀‖ / (lambda_min₀ / 2) ≤ C →
          ∀ t : ℝ, 0 ≤ t →
            ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
              empiricalNTKMatrix (netFromParams φ n d) X θ₀‖ ≤ (2 * M * L_J) * C} ≥
      1 - 2 * δ := by
  obtain ⟨E, -, hE, hpE⟩ := exists_measurableSet_initial_jacobian_and_readout_bounds
    φ n d m hn X hφ hφ_meas hderiv_meas hδ hδ1 _
    (outputJacobian_netFromParams_frobenius_norm_concentration φ n d m hn X C₀ C₁ hC₀ hC₁_bdd hφ hδ)
  refine hE.trans (MeasureTheory.measureReal_mono ?_)
  intro p hp
  obtain ⟨hp1, hp2⟩ := hpE p hp
  intro θ_traj lambda_min₀ r C M L_J hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀
    hM_ge hL_J_ge h_ball_gap hC_ge t ht
  exact freeze_bound_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₁ C₂ hC₁_bdd
    hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm _ p hp1 hp2 θ_traj lambda_min₀ r C M L_J hflow
    hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀ hM_ge hL_J_ge h_ball_gap hC_ge t ht

/-! ### Sharp kernel drift from average neuron moments

The maximum-readout argument above controls every neuron by the worst readout weight and therefore
loses a `√(log n)`. Here each neuron is controlled by its *own* initial scale. Along a gradient
flow that stays in a ball of radius `C` and whose residual decays like `R e^{-ν t}`, neuron `i`
moves by at most `b_i R / (m ν)` with `b_i² = O(n⁻¹ (Q_i + C² Λ_i²))` (`neuron_displacement_le`),
so the squared Jacobian variation is `n⁻¹ ∑ᵢ Λ_i² ρ_i² = O(n⁻¹)` times an empirical average of
the degree-four neuron moment `neuronMoment` (`kernel_drift_le_of_neuron_moments`). That average is
bounded in probability by Markov's inequality (`exists_neuronMoment_event`), giving kernel drift
`O(n⁻¹ᐟ²)` without a maximum over neurons. -/

section SharpKernelDrift
variable {n d m : ℕ}

/-- Coordinates of neuron `i` in the packed parameter vector: the readout `idxA i` (`none`) and
the hidden weights `idxW i j` (`some j`). -/
def neuronCoords (n d : ℕ) (i : Fin n) : Option (Fin d) → Fin (n * d + n)
  | none => idxA i
  | some j => idxW i j

private lemma norm_sq_restrictCoords_neuronCoords (i : Fin n)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) v‖ ^ 2 =
      (∑ j : Fin d, v (idxW i j) ^ 2) + v (idxA i) ^ 2 := by
  rw [norm_sq_restrictCoords, Fintype.sum_option]
  simp only [neuronCoords]
  ring

private lemma norm_sq_restrictCoords_neuronCoords_sub (i : Fin n)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) (θ₁ - θ₂)‖ ^ 2 =
      (∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
        (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by
  rw [norm_sq_restrictCoords_neuronCoords]
  rfl

private lemma norm_restrictCoords_neuronCoords_le (i : Fin n)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖restrictCoords (neuronCoords n d i) v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  have h := norm_sq_sub_unpack n d v (0 : EuclideanSpace ℝ (Fin (n * d + n)))
  have h0 := norm_sq_restrictCoords_neuronCoords_sub i v (0 : EuclideanSpace ℝ (Fin (n * d + n)))
  rw [sub_zero] at h h0
  rw [h0, h]
  have h1 : (∑ j : Fin d,
      (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin d,
        (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin n => ∑ j : Fin d,
      (unpackW v i j - unpackW (0 : EuclideanSpace ℝ (Fin (n * d + n))) i j) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2 ≤
      ∑ i : Fin n, (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin n =>
      (unpackA v i - unpackA (0 : EuclideanSpace ℝ (Fin (n * d + n))) i) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- Squared per-neuron Jacobian-Lipschitz scale at readout weight `a`: the coefficient of the
neuron's squared displacement in the squared Jacobian-block variation. -/
def neuronLipschitzScaleSq (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) (a : ℝ) : ℝ :=
  ∑ α : Fin m, (2 * a ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
    3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)

/-- Squared per-neuron activation scale: an upper bound for `n ×` the squared Frobenius norm of the
neuron's Jacobian block (hidden weights `w`, readout weight `a`). -/
noncomputable def neuronJacobianScaleSq (φ : ℝ → ℝ) (C₁ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : ℝ :=
  ∑ α : Fin m, (φ (w ⊙ X α) ^ 2 + a ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)

/-- The single-neuron observable whose empirical average controls the kernel drift at rate
`n⁻¹ᐟ²`. It is a polynomial of degree four in `(φ (w ⊙ x), a)`, so it is integrable under Gaussian
initialization as soon as `φ (w ⊙ x)` is square integrable. -/
noncomputable def neuronMoment (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : ℝ :=
  neuronLipschitzScaleSq C₁ C₂ X a *
    (neuronJacobianScaleSq φ C₁ X w a + neuronLipschitzScaleSq C₁ C₂ X a)

lemma neuronLipschitzScaleSq_nonneg (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) (a : ℝ) :
    0 ≤ neuronLipschitzScaleSq C₁ C₂ X a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma neuronJacobianScaleSq_nonneg (φ : ℝ → ℝ) (C₁ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : 0 ≤ neuronJacobianScaleSq φ C₁ X w a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma neuronMoment_nonneg (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin d → ℝ) (a : ℝ) : 0 ≤ neuronMoment φ C₁ C₂ X w a :=
  mul_nonneg (neuronLipschitzScaleSq_nonneg _ _ _ _)
    (add_nonneg (neuronJacobianScaleSq_nonneg _ _ _ _ _) (neuronLipschitzScaleSq_nonneg _ _ _ _))

/-- The squared norm of neuron `i`'s Jacobian block is its gradient-coordinate energy. -/
private lemma neuron_jacobian_block_sq (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α)) (i : Fin n) :
    ∑ α : Fin m, ∑ o : Option (Fin d),
        outputJacobian (netFromParams φ n d) X θ α (neuronCoords n d i o) ^ 2 =
      ∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
        gradA φ n d (X α) θ i ^ 2) := by
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Fintype.sum_option]
  simp only [neuronCoords, outputJacobian_netFromParams_apply_W φ n d m X θ hφ,
    outputJacobian_netFromParams_apply_a φ n d m X θ hφ]
  ring

private lemma neuron_block_energy_le (φ : ℝ → ℝ) {C₁ : ℝ} (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hn : 0 < n)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) (x : Fin d → ℝ) :
    (∑ j : Fin d, gradW φ n d x θ i j ^ 2) + gradA φ n d x θ i ^ 2 ≤
      (n : ℝ)⁻¹ * (φ (unpackW θ i ⊙ x) ^ 2 + unpackA θ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, x j ^ 2) := by
  have hroot : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hd_sq : deriv φ (unpackW θ i ⊙ x) ^ 2 ≤ C₁ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hC₁ 0))).2 (hC₁ _)
  have hW : (∑ j : Fin d, gradW φ n d x θ i j ^ 2) =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) ^ 2 * ∑ j : Fin d, x j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gradW]
    rw [show (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x) * x j =
        (n : ℝ)⁻¹.sqrt * (unpackA θ i * deriv φ (unpackW θ i ⊙ x) * x j) by ring, mul_pow, hroot]
    ring
  have hA : gradA φ n d x θ i ^ 2 = (n : ℝ)⁻¹ * φ (unpackW θ i ⊙ x) ^ 2 := by
    simp only [gradA]; rw [mul_pow, hroot]
  rw [hW, hA]
  have hSx : 0 ≤ ∑ j : Fin d, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : unpackA θ i ^ 2 * deriv φ (unpackW θ i ⊙ x) ^ 2 * ∑ j : Fin d, x j ^ 2 ≤
      unpackA θ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, x j ^ 2 := by gcongr
  have hn' : 0 ≤ (n : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hn']


/-- The displacement of neuron `i`'s coordinates, in the two forms used in the Jacobian-Lipschitz
estimates. -/
private lemma neuron_displacement_eq (i : Fin n) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) :
    (∑ j : Fin d, (unpackW θ₀ i j - unpackW θ i j) ^ 2) + (unpackA θ₀ i - unpackA θ i) ^ 2 =
      ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
  have hc : ∀ a b : ℝ, (a - b) ^ 2 = (b - a) ^ 2 := fun a b => by ring
  rw [norm_sq_restrictCoords_neuronCoords_sub]
  simp_rw [hc (unpackW θ₀ i _), hc (unpackA θ₀ i)]

/-- `b² ≤ 2 a² + 2 (a - b)²`, i.e. `add_sq_le` for `b = a + (b - a)`. -/
private lemma sq_le_two_mul_sq_add_two_mul_sq_sub (a b : ℝ) :
    b ^ 2 ≤ 2 * a ^ 2 + 2 * (a - b) ^ 2 := by
  have h := add_sq_le (a := a) (b := b - a)
  rw [add_sub_cancel] at h
  nlinarith [h]

/-- **Neuron-block Jacobian energy after a displacement.** -/
private lemma neuron_jacobian_block_energy_le_of_displacement (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    ∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2) ≤
      2 * ((n : ℝ)⁻¹ * neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i)) +
      2 * ((n : ℝ)⁻¹ * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2) := by
  set D := ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 with hD
  have hα : ∀ α : Fin m,
      (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2 ≤
        2 * ((n : ℝ)⁻¹ * (φ (unpackW θ₀ i ⊙ X α) ^ 2 +
          unpackA θ₀ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)) +
        2 * ((n : ℝ)⁻¹ * (2 * unpackA θ₀ i ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
          3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * D) := by
    intro α
    have h0 := neuron_block_energy_le φ hC₁ hn θ₀ i (X α)
    have hd := grad_single_neuron_sub_le φ n d (X α) θ₀ θ i C₁ C₂ |unpackA θ₀ i| hC₁0 hC₂0
      (abs_nonneg _) hφ_lip hC₁ hderiv_lip le_rfl
    dsimp only at hd
    rw [neuron_displacement_eq, sq_abs] at hd
    have hW : (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) ≤
        2 * (∑ j : Fin d, gradW φ n d (X α) θ₀ i j ^ 2) +
        2 * ∑ j : Fin d, (gradW φ n d (X α) θ₀ i j - gradW φ n d (X α) θ i j) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => sq_le_two_mul_sq_add_two_mul_sq_sub _ _
    have hA := sq_le_two_mul_sq_add_two_mul_sq_sub (gradA φ n d (X α) θ₀ i)
      (gradA φ n d (X α) θ i)
    nlinarith
  calc _ ≤ ∑ α : Fin m, (2 * ((n : ℝ)⁻¹ * (φ (unpackW θ₀ i ⊙ X α) ^ 2 +
          unpackA θ₀ i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2)) +
        2 * ((n : ℝ)⁻¹ * (2 * unpackA θ₀ i ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
          3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * D)) := Finset.sum_le_sum fun α _ => hα α
    _ = _ := by
      simp only [neuronJacobianScaleSq, neuronLipschitzScaleSq, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Squared Jacobian variation as a sum over neurons.** -/
lemma outputJacobian_sub_norm_sq_le_neuron_sum (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (X : Fin m → Fin d → ℝ) (θ θ₀ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖outputJacobian (netFromParams φ n d) X θ - outputJacobian (netFromParams φ n d) X θ₀‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
  rw [norm_sub_rev, outputJacobian_sub_frobenius_norm_sq φ n d m X θ₀ θ
    (fun _ _ => hφ.differentiableAt) (fun _ _ => hφ.differentiableAt)]
  simp_rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ α : Fin m, ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * |unpackA θ₀ i| ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) *
        ‖restrictCoords (neuronCoords n d i) (θ - θ₀)‖ ^ 2 := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => ?_
        have hd := grad_single_neuron_sub_le φ n d (X α) θ₀ θ i C₁ C₂ |unpackA θ₀ i| hC₁0 hC₂0
          (abs_nonneg _) hφ_lip hC₁ hderiv_lip le_rfl
        dsimp only at hd
        rwa [neuron_displacement_eq] at hd
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [neuronLipschitzScaleSq, sq_abs, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      ring


/-- **Per-neuron displacement along the flow.** If the flow stays within `C` of `θ₀` and the
residual decays like `R e^{-ν t}`, then neuron `i` moves at most `b_i R / (m ν)` with
`b_i² = 2 n⁻¹ (Q_i + C² Λ_i²)`, where `Q_i, Λ_i²` are the per-neuron scales at initialization. -/
lemma neuron_displacement_le (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n) (hm : 0 < m)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj)
    {C R ν : ℝ} (hν : 0 < ν)
    (hdisp : ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - θ₀‖ ≤ C)
    (hres : ∀ t : ℝ, 0 ≤ t →
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤ R * Real.exp (-ν * t))
    {T : ℝ} (hT : 0 ≤ T) (i : Fin n) :
    ‖restrictCoords (neuronCoords n d i) (θ_traj T - θ₀)‖ ≤
      (m : ℝ)⁻¹ * Real.sqrt (2 * ((n : ℝ)⁻¹ *
        (neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) +
          C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)))) * R / ν := by
  set b := Real.sqrt (2 * ((n : ℝ)⁻¹ *
        (neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) +
          C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)))) with hb
  have hR : 0 ≤ R := by
    have := (norm_nonneg _).trans (hres 0 le_rfl)
    simpa using this
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hspeed : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖restrictCoords (neuronCoords n d i)
        (gradient (mseLoss (netFromParams φ n d) X y) (θ_traj t))‖ ≤
        (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t)) := by
    intro t ht
    have hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ')
        (θ_traj t) := fun β =>
      (hasFDerivAt_netFromParams φ n d (X β) (θ_traj t)
        fun _ => hφ.differentiableAt).differentiableAt
    refine (norm_restrictCoords_gradient_mseLoss_le _ X y (θ_traj t) hdiff
      (neuronCoords n d i)).trans ?_
    rw [neuron_jacobian_block_sq φ X (θ_traj t) (fun _ _ => hφ.differentiableAt) i]
    have hE := neuron_jacobian_block_energy_le_of_displacement φ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip
      hn X (θ_traj t) θ₀ i
    have hD : ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((norm_restrictCoords_neuronCoords_le i _).trans (hdisp t ht.1)) 2
    have hΛ := neuronLipschitzScaleSq_nonneg C₁ C₂ X (unpackA θ₀ i)
    have hsqrt : Real.sqrt (∑ α : Fin m, ((∑ j : Fin d, gradW φ n d (X α) (θ_traj t) i j ^ 2) +
        gradA φ n d (X α) (θ_traj t) i ^ 2)) ≤ b := by
      refine Real.sqrt_le_sqrt ?_
      have hn' : 0 ≤ (n : ℝ)⁻¹ := by positivity
      have : (n : ℝ)⁻¹ * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
          ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
          (n : ℝ)⁻¹ * (C ^ 2 * neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hn'
        nlinarith
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hres t ht.1) (by positivity))
  have hBc : Continuous (fun t : ℝ => (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t))) := by
    fun_prop
  have hBi : IntervalIntegrable (fun t : ℝ => (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t)))
      MeasureTheory.volume 0 T := hBc.intervalIntegrable 0 T
  have hmain := norm_map_sub_le_integral_of_forwardGF hflow
    (restrictCoords (neuronCoords n d i)) hT hspeed hBi
  refine hmain.trans ?_
  have hint : (∫ t in (0 : ℝ)..T, (m : ℝ)⁻¹ * b * (R * Real.exp (-ν * t))) =
      ((m : ℝ)⁻¹ * b * R) * ∫ t in (0 : ℝ)..T, Real.exp (-ν * t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  calc ((m : ℝ)⁻¹ * b * R) * ∫ t in (0 : ℝ)..T, Real.exp (-ν * t)
      ≤ ((m : ℝ)⁻¹ * b * R) * ν⁻¹ :=
        mul_le_mul_of_nonneg_left (integral_exp_neg_le ν T hν hT) (by positivity)
    _ = _ := by ring


/-- **Kernel drift at rate `n⁻¹ᐟ²` from an empirical neuron moment.** Let `θ_traj` be a gradient
flow from `θ₀` for the two-layer MSE loss, staying within `C` of `θ₀` with residual decaying like
`R e^{-ν t}` and output Jacobian bounded by `M` along the flow and at `θ₀`. If the empirical average
of the per-neuron observable `neuronMoment` at initialization is at most `τ`, the empirical NTK
stays within `2 M (R / (m ν)) √(2 (1 + C²) τ) / √n` of its initial value for all `t ≥ 0`.

There is no maximum over neurons: each neuron's displacement is controlled by its own scale
(`neuron_displacement_le`) and the averages are controlled in probability by Markov's inequality. -/
theorem kernel_drift_le_of_neuron_moments (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₁ C₂ : ℝ}
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hn : 0 < n) (hm : 0 < m)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj)
    {C R ν M τ : ℝ} (hν : 0 < ν)
    (hdisp : ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - θ₀‖ ≤ C)
    (hres : ∀ t : ℝ, 0 ≤ t →
      ‖trainingResidual (netFromParams φ n d) X y (θ_traj t)‖ ≤ R * Real.exp (-ν * t))
    (hJ : ∀ t : ℝ, 0 ≤ t → ‖outputJacobian (netFromParams φ n d) X (θ_traj t)‖ ≤ M)
    (hJ₀ : ‖outputJacobian (netFromParams φ n d) X θ₀‖ ≤ M)
    (hmom : (n : ℝ)⁻¹ * ∑ i : Fin n,
      neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) ≤ τ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖empiricalNTKMatrix (netFromParams φ n d) X (θ_traj t) -
        empiricalNTKMatrix (netFromParams φ n d) X θ₀‖ ≤
      2 * M * (R / ((m : ℝ) * ν) * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) := by
  have hR : 0 ≤ R := by simpa using (norm_nonneg _).trans (hres 0 le_rfl)
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₀
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hτ : 0 ≤ τ := le_trans (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    neuronMoment_nonneg φ C₁ C₂ X _ _)) hmom
  set K₁ : ℝ := R / ((m : ℝ) * ν) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- per-neuron bound on `Λ_i² ρ_i²`
  have hneuron : ∀ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
      ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
        K₁ ^ 2 * (2 * (n : ℝ)⁻¹ * (1 + C ^ 2)) *
          neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) := by
    intro i
    set Q := neuronJacobianScaleSq φ C₁ X (unpackW θ₀ i) (unpackA θ₀ i) with hQ
    set Λ := neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) with hΛ
    have hQ0 : 0 ≤ Q := neuronJacobianScaleSq_nonneg _ _ _ _ _
    have hΛ0 : 0 ≤ Λ := neuronLipschitzScaleSq_nonneg _ _ _ _
    have hρ := neuron_displacement_le φ hφ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip hn hm X y hflow hν hdisp
      hres ht i
    set b := Real.sqrt (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ))) with hb
    have hb2 : b ^ 2 = 2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ)) :=
      Real.sq_sqrt (by positivity)
    have hρ2 : ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2 ≤
        K₁ ^ 2 * (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ))) := by
      calc _ ≤ ((m : ℝ)⁻¹ * b * R / ν) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hρ 2
        _ = K₁ ^ 2 * b ^ 2 := by rw [hK₁]; ring
        _ = _ := by rw [hb2]
    have hmomeq : neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) = Λ * (Q + Λ) := rfl
    rw [hmomeq]
    calc Λ * ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2
        ≤ Λ * (K₁ ^ 2 * (2 * ((n : ℝ)⁻¹ * (Q + C ^ 2 * Λ)))) :=
          mul_le_mul_of_nonneg_left hρ2 hΛ0
      _ = K₁ ^ 2 * (2 * (n : ℝ)⁻¹) * (Λ * (Q + C ^ 2 * Λ)) := by ring
      _ ≤ K₁ ^ 2 * (2 * (n : ℝ)⁻¹) * ((1 + C ^ 2) * (Λ * (Q + Λ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [mul_nonneg hΛ0 hQ0, mul_nonneg hΛ0 hΛ0, sq_nonneg C,
            mul_nonneg (mul_nonneg hΛ0 hQ0) (sq_nonneg C),
            mul_nonneg (mul_nonneg hΛ0 hΛ0) (sq_nonneg C)]
      _ = _ := by ring
  have hJsq : ‖outputJacobian (netFromParams φ n d) X (θ_traj t) -
      outputJacobian (netFromParams φ n d) X θ₀‖ ^ 2 ≤
        (K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) ^ 2 := by
    refine (outputJacobian_sub_norm_sq_le_neuron_sum φ hφ hC₁0 hC₂0 hφ_lip hC₁ hderiv_lip X
      (θ_traj t) θ₀).trans ?_
    calc (n : ℝ)⁻¹ * ∑ i : Fin n, neuronLipschitzScaleSq C₁ C₂ X (unpackA θ₀ i) *
          ‖restrictCoords (neuronCoords n d i) (θ_traj t - θ₀)‖ ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, K₁ ^ 2 * (2 * (n : ℝ)⁻¹ * (1 + C ^ 2)) *
            neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hneuron i) (by positivity)
      _ = K₁ ^ 2 * (2 * (1 + C ^ 2)) * (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ i : Fin n,
            neuronMoment φ C₁ C₂ X (unpackW θ₀ i) (unpackA θ₀ i)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ K₁ ^ 2 * (2 * (1 + C ^ 2)) * (n : ℝ)⁻¹ * τ :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = _ := by
          have hrhs : (K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ)) ^ 2 =
            K₁ ^ 2 * (2 * (1 + C ^ 2) * τ) / n := by
            rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn'.le]
          rw [hrhs]
          field_simp
  have hJdiff : ‖outputJacobian (netFromParams φ n d) X (θ_traj t) -
      outputJacobian (netFromParams φ n d) X θ₀‖ ≤
        K₁ * Real.sqrt (2 * (1 + C ^ 2) * τ) / Real.sqrt (n : ℝ) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hJsq
  exact (empiricalNTKMatrix_sub_le_of_jacobian_bound _ X _ _ M (hJ t ht) hJ₀).trans
    (mul_le_mul_of_nonneg_left hJdiff (by positivity))


/-- `neuronMoment` is an explicit polynomial in `a` and the activation energy `∑_α φ (w ⊙ x_α)²`. -/
private lemma neuronMoment_eq_poly (φ : ℝ → ℝ) (C₁ C₂ : ℝ) (X : Fin m → Fin d → ℝ) :
    ∃ c₂ c₃ c₄ : ℝ, ∀ (w : Fin d → ℝ) (a : ℝ),
      neuronMoment φ C₁ C₂ X w a = (c₂ * a ^ 2 + c₃) *
        ((∑ α : Fin m, φ (w ⊙ X α) ^ 2) + c₄ * a ^ 2 + (c₂ * a ^ 2 + c₃)) := by
  refine ⟨∑ α : Fin m, 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2,
    ∑ α : Fin m, 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2,
    ∑ α : Fin m, C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2, fun w a => ?_⟩
  have hΛ : neuronLipschitzScaleSq C₁ C₂ X a =
      (∑ α : Fin m, 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2) * a ^ 2 +
        ∑ α : Fin m, 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2 := by
    simp only [neuronLipschitzScaleSq, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  have hQ : neuronJacobianScaleSq φ C₁ X w a = (∑ α : Fin m, φ (w ⊙ X α) ^ 2) +
      (∑ α : Fin m, C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) * a ^ 2 := by
    simp only [neuronJacobianScaleSq, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [neuronMoment, hQ, hΛ]

lemma measurable_neuronMoment {φ : ℝ → ℝ} (hφ : Measurable φ) (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ) :
    Measurable (fun q : (Fin d → ℝ) × ℝ => neuronMoment φ C₁ C₂ X q.1 q.2) := by
  obtain ⟨c₂, c₃, c₄, h⟩ := neuronMoment_eq_poly φ C₁ C₂ X (m := m) (d := d)
  simp_rw [h]
  have hG : Measurable (fun q : (Fin d → ℝ) × ℝ => ∑ α : Fin m, φ (q.1 ⊙ X α) ^ 2) :=
    Finset.measurable_sum _ fun α _ =>
      (hφ.comp ((measurable_innerProduct_left (X α)).comp measurable_fst)).pow_const 2
  have ha : Measurable (fun q : (Fin d → ℝ) × ℝ => q.2) := measurable_snd
  fun_prop

/-- The single-neuron moment is integrable under the Gaussian single-neuron law. -/
lemma integrable_neuronMoment {φ : ℝ → ℝ} (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⊙ X α)) 2 (gaussianRowMeasure d)) :
    Integrable (fun q : (Fin d → ℝ) × ℝ => neuronMoment φ C₁ C₂ X q.1 q.2)
      (singleNeuronMeasure d) := by
  obtain ⟨c₂, c₃, c₄, h⟩ := neuronMoment_eq_poly φ C₁ C₂ X (m := m) (d := d)
  have hG : Integrable (fun w : Fin d → ℝ => ∑ α : Fin m, φ (w ⊙ X α) ^ 2)
      (gaussianRowMeasure d) := integrable_finsetSum _ fun α _ => (hL2 α).integrable_sq
  have h2 := integrable_sq_gaussianReal
  have h4 := integrable_pow_four_gaussianReal
  have hu : Integrable (fun a : ℝ => c₂ * a ^ 2 + c₃) (gaussianReal 0 1) :=
    (h2.const_mul c₂).add (integrable_const c₃)
  have hv : Integrable (fun a : ℝ => (c₂ * a ^ 2 + c₃) * ((c₄ + c₂) * a ^ 2 + c₃))
      (gaussianReal 0 1) := by
    have : (fun a : ℝ => (c₂ * a ^ 2 + c₃) * ((c₄ + c₂) * a ^ 2 + c₃)) =
        fun a => c₂ * (c₄ + c₂) * a ^ 4 + (c₂ * c₃ + c₃ * (c₄ + c₂)) * a ^ 2 + c₃ * c₃ := by
      ext a; ring
    rw [this]
    exact ((h4.const_mul _).add (h2.const_mul _)).add (integrable_const _)
  have h1 := hG.mul_prod hu
  have h3 := (integrable_const (1 : ℝ) : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
    (gaussianRowMeasure d)).mul_prod hv
  refine (h1.add h3).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.add_apply, one_mul, h]
  ring


/-- **The neuron-moment average is bounded with high probability.** For every `δ > 0` there is a
width-independent threshold `τ` such that the empirical average `n⁻¹ ∑ᵢ neuronMoment (Wᵢ, aᵢ)` is at
most `τ` on a measurable initialization event of probability at least `1 - δ`, for every width. -/
theorem exists_neuronMoment_event {φ : ℝ → ℝ} (hφ : Measurable φ) (C₁ C₂ : ℝ)
    (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⊙ X α)) 2 (gaussianRowMeasure d))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ n : ℕ, 0 < n →
      MeasurableSet {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ X (p.1 i) (p.2 i) ≤ τ} ∧
      (initMeasure n d).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ X (p.1 i) (p.2 i) ≤ τ} ≥ 1 - δ := by
  set I : ℝ := ∫ q, neuronMoment φ C₁ C₂ X q.1 q.2 ∂(singleNeuronMeasure d)
    with hI
  have hI0 : 0 ≤ I := integral_nonneg fun q => neuronMoment_nonneg _ _ _ _ _ _
  refine ⟨I / δ + 1, by positivity, fun n hn => ⟨?_, ?_⟩⟩
  · exact measurableSet_le (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (measurable_neuronMoment hφ C₁ C₂ X).comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))) _) measurable_const
  · refine measureReal_initMeasure_neuronAverage_le hn (measurable_neuronMoment hφ C₁ C₂ X)
      (integrable_neuronMoment C₁ C₂ X hL2) (fun q => neuronMoment_nonneg _ _ _ _ _ _)
      (by positivity) ?_
    rw [add_mul, div_mul_cancel₀ _ hδ.ne']
    linarith

end SharpKernelDrift

/-! ### Training Limits of Trainable Two-Layer Networks

This section establishes the framework and target specifications for the infinite-width
training limits of the full two-layer neural network with trainable input weights `W` and
trainable readout weights `a`.

Following the roadmap in `docs/NTK_full_formalization_plan.md`:
- `FiniteHorizonLimit`: states the finite-horizon lazy training theorem on `[0, T]` for any
  fixed `T ≥ 0`, establishing kernel stationarity and weak convergence of predictions without
  requiring a strictly positive limiting spectral gap.
- `GlobalPositiveGapLimit`: states the global lazy training theorem under a positive limiting
  spectral gap `λ_min(K_∞) > 0`, establishing uniform-in-time kernel control and exponential
  residual / loss decay with high probability.
-/

section FullTwoLayerTrainingLimit

section InitializationEvents

/-! #### Deterministic feasibility of the bootstrap constants

The Gap 4 Jacobian-Lipschitz scale `L_J` evaluated at a *fixed* displacement radius `r` is
`sqrt (∑ α, (a α * (√(2 log (2n / δ)) + r) ^ 2 + b α)) / √n`, which vanishes as the width `n → ∞`.
This is what makes the bootstrap feasibility inequalities hold eventually in `n`. -/

open Filter Topology in
private theorem tendsto_sq_sqrt_two_log_add_div_nat {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ => (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => 2 * (n : ℝ) / δ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < 2 / δ)).congr
      fun n => by ring
  have hlog : Tendsto (fun n : ℕ => Real.log (2 * n / δ) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
    have h2 := h.const_mul (2 / δ)
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp, pow_one, add_zero, one_mul]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hbound : Tendsto (fun n : ℕ => 4 * (Real.log (2 * n / δ) / n) + 2 * r ^ 2 * (1 / (n : ℝ)))
      atTop (𝓝 0) := by
    have h1 := hlog.const_mul 4
    have h2 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * r ^ 2)
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop (max 1 ⌈δ / 2⌉₊)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hδn : δ / 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have h1 : 1 ≤ 2 * (n : ℝ) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hlogn : 0 ≤ Real.log (2 * n / δ) := Real.log_nonneg h1
  have hsq : Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 = 2 * Real.log (2 * n / δ) :=
    Real.sq_sqrt (by positivity)
  have key : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤
      4 * Real.log (2 * n / δ) + 2 * r ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * Real.log (2 * n / δ)) - r)]
  calc (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n
      ≤ (4 * Real.log (2 * n / δ) + 2 * r ^ 2) / n := by gcongr
    _ = 4 * (Real.log (2 * n / δ) / n) + 2 * r ^ 2 * (1 / (n : ℝ)) := by field_simp

open Filter Topology in
private theorem tendsto_sqrt_sum_sq_sqrt_two_log_add_div_sqrt_nat {ι : Type*} [Fintype ι]
    (a b : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ =>
      Real.sqrt (∑ i, (a i * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 + b i))
      / Real.sqrt n) atTop (𝓝 0) := by
  have hu := tendsto_sq_sqrt_two_log_add_div_nat hδ r
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun n : ℕ => ∑ i, (a i * ((Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 / n)
      + b i * (1 / (n : ℝ)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
      ((hu.const_mul (a i)).add (hinv.const_mul (b i)))
    simpa using this
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsum
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [← Real.sqrt_div' _ hn0.le, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- Regularity consequences of the global derivative bounds on the activation: `C₁, C₂ ≥ 0`, the
first-derivative Lipschitz bound `|φ u - φ v| ≤ C₁ |u - v|`, and measurability of `deriv φ`. -/
private lemma activation_regularity_of_bounds (φ : ℝ → ℝ) (C₁ C₂ : ℝ)
    (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|) (hφ : Differentiable ℝ φ) :
    0 ≤ C₁ ∧ 0 ≤ C₂ ∧ (∀ u v, |φ u - φ v| ≤ C₁ * |u - v|) ∧ Measurable (deriv φ) := by
  refine ⟨(abs_nonneg _).trans (hC₁_bdd 0), by simpa using (abs_nonneg _).trans (hderiv_lip 1 0),
    fun u v => ?_, (LipschitzWith.of_dist_le' (K := C₂) fun x y => by
      simpa [Real.dist_eq] using hderiv_lip x y).continuous.measurable⟩
  simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hφ x) (fun x _ => by simpa [Real.norm_eq_abs] using hC₁_bdd x) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)

/-- A bounded measurable function of a Gaussian-row preactivation is in `L²`. -/
private lemma memLp_two_gaussianRow_comp_of_bounded {d : ℕ} (g : ℝ → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x : Fin d → ℝ) :
    MemLp (fun w => g (w ⊙ x)) 2 (gaussianRowMeasure d) :=
  MemLp.of_bound (hg.comp (measurable_innerProduct_left x)).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB _)

/-- A product of two bounded measurable functions of Gaussian-row preactivations is in `L²`. -/
private lemma memLp_two_gaussianRow_mul_comp_of_bounded {d : ℕ} (g : ℝ → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x x' : Fin d → ℝ) :
    MemLp (fun w => g (w ⊙ x) * g (w ⊙ x')) 2 (gaussianRowMeasure d) :=
  MemLp.of_bound ((hg.comp (measurable_innerProduct_left x)).mul
    (hg.comp (measurable_innerProduct_left x'))).aestronglyMeasurable (B * B)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hB 0)))

open Filter Topology in
/-- The Gap 4 Jacobian-Lipschitz scale at a *fixed* displacement radius `r` vanishes as the width
`n → ∞`. This makes the bootstrap feasibility inequalities hold eventually in `n`. -/
private lemma tendsto_jacobianLipschitzScale {d m : ℕ} (X : Fin m → Fin d → ℝ) (C₁ C₂ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  refine (tendsto_sqrt_sum_sq_sqrt_two_log_add_div_sqrt_nat
    (fun α => 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2)
    (fun α => 3 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) hδ r).congr fun n => ?_
  congr 3
  ext α
  ring

open Filter Topology in
/-- The Gap 4 Jacobian-Lipschitz scale at a fixed radius is `O(√(log n / n))`: this is the rate at
which the bootstrap kernel drift vanishes. -/
private lemma jacobianLipschitzScale_le_sqrt_log_div {d m : ℕ} (X : Fin m → Fin d → ℝ)
    (C₁ C₂ : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤
      A * Real.sqrt (Real.log n / n) := by
  set K1 : ℝ := 4 + 4 * |Real.log (2 / δ)| + 2 * r ^ 2 with hK1
  set B : ℝ := ∑ α : Fin m, (2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 * K1 +
    3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) with hB
  have hK1_nonneg : 0 ≤ K1 := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop ⌈δ / 2⌉₊, eventually_gt_atTop 0] with n hn hnδ hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hδn : δ / 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
  have h1 : 1 ≤ 2 * (n : ℝ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hL_nonneg : 0 ≤ Real.log (2 * n / δ) := Real.log_nonneg h1
  have hLsplit : Real.log (2 * n / δ) = Real.log (2 / δ) + Real.log n := by
    rw [show 2 * (n : ℝ) / δ = 2 / δ * n by ring, Real.log_mul (by positivity) hn0'.ne']
  have hsq : Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 = 2 * Real.log (2 * n / δ) :=
    Real.sq_sqrt (by positivity)
  have hkey : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤ K1 * Real.log n := by
    have h2 : (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 ≤
        4 * Real.log (2 * n / δ) + 2 * r ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (2 * Real.log (2 * n / δ)) - r)]
    have h3 : Real.log (2 / δ) ≤ |Real.log (2 / δ)| * Real.log n :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hn)
    nlinarith [sq_nonneg r]
  have hterm : ∀ α : Fin m, 2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2) ≤
      (2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 * K1 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) * Real.log n := by
    intro α
    have hb : 0 ≤ 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2) := by positivity
    have hcoef : 0 ≤ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkey hcoef, mul_le_mul_of_nonneg_left hn hb]
  have hS : ∑ α : Fin m, (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)) ≤
      B * Real.log n := by
    rw [hB, Finset.sum_mul]
    exact Finset.sum_le_sum fun α _ => hterm α
  calc Real.sqrt (∑ α : Fin m, (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, X α j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) /
        Real.sqrt (n : ℝ) ≤ Real.sqrt (B * Real.log n) / Real.sqrt (n : ℝ) := by
        gcongr
    _ = Real.sqrt B * Real.sqrt (Real.log n / n) := by
        rw [Real.sqrt_mul hB_nonneg, Real.sqrt_div' _ hn0'.le, mul_div_assoc]

/-- **Smooth activation.** The bundled activation hypotheses shared by the paper-facing theorems:
`φ` is differentiable with bounded derivative (`C₁`) and `C₂`-Lipschitz derivative. No bound on the
value of `φ` is assumed: a bounded derivative already gives linear growth
`|φ z| ≤ |φ 0| + C₁ |z|` (`activation_growth`), which is all that Gaussian initialization needs.
Every consequence used by the proofs (`C₁, C₂ ≥ 0`, Lipschitzness of `φ`, measurability of
`deriv φ`, `L²` integrability against Gaussians) is derived from these three facts. Lower-level
deterministic lemmas keep taking the unbundled hypotheses they use; the forward gradient-flow
construction (`exists_forwardGradientFlow`) needs nothing beyond this structure. -/
structure SmoothActivation (φ : ℝ → ℝ) (C₁ C₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ φ
  deriv_bdd : ∀ z, |deriv φ z| ≤ C₁
  deriv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|

/-- A bounded derivative gives linear growth of the activation. -/
private lemma activation_growth {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂) :
    ∀ z, |φ z| ≤ |φ 0| + C₁ * |z| := fun z => by
  obtain ⟨-, -, hφlip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have := hφlip z 0
  rw [sub_zero] at this
  calc |φ z| = |φ z - φ 0 + φ 0| := by ring_nf
    _ ≤ |φ z - φ 0| + |φ 0| := abs_add_le _ _
    _ ≤ |φ 0| + C₁ * |z| := by linarith

/-- Gaussian second moments of the activation and of its derivative along rows, derived from the
bounded derivative alone: `φ` has linear growth and `deriv φ` is bounded. -/
private lemma activation_memLp_two {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂)
    {d : ℕ} :
    (∀ x : Fin d → ℝ, MemLp (fun w => φ (w ⊙ x)) 2 (gaussianRowMeasure d)) ∧
    (∀ x x' : Fin d → ℝ,
      MemLp (fun w => φ (w ⊙ x) * φ (w ⊙ x')) 2 (gaussianRowMeasure d)) ∧
    (∀ x : Fin d → ℝ, MemLp (fun w => deriv φ (w ⊙ x)) 2 (gaussianRowMeasure d)) ∧
    (∀ x x' : Fin d → ℝ,
      MemLp (fun w => deriv φ (w ⊙ x) * deriv φ (w ⊙ x')) 2 (gaussianRowMeasure d)) := by
  obtain ⟨hC₁0, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hmeas : Measurable φ := hact.differentiable.continuous.measurable
  have hA : 0 ≤ |φ 0| := abs_nonneg _
  have h1 : ∀ x : Fin d → ℝ, MemLp (fun w => φ (w ⊙ x)) 2 (gaussianRowMeasure d) := fun x => by
    simpa using memLp_gaussianRow_comp_of_linear_growth φ hmeas hA hC₁0
      (activation_growth hact) x 2
  exact ⟨h1, fun x x' => memLp_two_gaussianRow_mul_comp_of_linear_growth φ hmeas hA hC₁0
      (activation_growth hact) x x',
    fun x => memLp_two_gaussianRow_comp_of_bounded (deriv φ) hderiv_meas hact.deriv_bdd x,
    fun x x' => memLp_two_gaussianRow_mul_comp_of_bounded (deriv φ) hderiv_meas hact.deriv_bdd x
      x'⟩

private lemma activation_locallyLipschitz {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) :
    LocallyLipschitz φ ∧ LocallyLipschitz (deriv φ) := by
  obtain ⟨hφ, hC₁, hderiv_lip⟩ := hact
  obtain ⟨-, -, hφlip, -⟩ := activation_regularity_of_bounds φ _ _ hC₁ hderiv_lip hφ
  exact ⟨(LipschitzWith.of_dist_le' (K := C₁) fun x y => by
      simpa [Real.dist_eq] using hφlip x y).locallyLipschitz,
    (LipschitzWith.of_dist_le' (K := C₂) fun x y => by
      simpa [Real.dist_eq] using hderiv_lip x y).locallyLipschitz⟩

/-- **Jacobian and readout good events for a smooth activation.** For every `δ ∈ (0, 1]` there is a
constant `M₀` (independent of the width) such that, for every width `n ≥ 1`, there is a measurable
event of `initMeasure n d`-probability `≥ 1 - 2 δ` on which the initial output Jacobian has
Frobenius norm at most `M₀` and every readout weight is at most `√(2 log (2 n / δ))`. The Jacobian
bound uses only the bounded derivative
(`outputJacobian_netFromParams_frobenius_norm_concentration_of_L2`), not a bound on `φ`. -/
private lemma exists_jacobian_bound_and_good_events {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {d m : ℕ} (X : Fin m → Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ n : ℕ, 0 < n →
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)),
        MeasurableSet E ∧ (initMeasure n d).real E ≥ 1 - 2 * δ ∧
        ∀ p ∈ E,
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ M₀ ∧
          ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hL2 := (activation_memLp_two hact (d := d)).1
  refine ⟨Real.sqrt (2 * ((∑ α : Fin m, ∫ w, φ (w ⊙ X α) ^ 2 ∂(gaussianRowMeasure d)) + 1 +
      C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ), Real.sqrt_nonneg _, fun n hn => ?_⟩
  exact exists_measurableSet_initial_jacobian_and_readout_bounds φ n d m hn X hact.differentiable
    hact.differentiable.continuous.measurable hderiv_meas hδ hδ1 _
    (outputJacobian_netFromParams_frobenius_norm_concentration_of_L2 φ n d m hn X C₁ hact.deriv_bdd
      hact.differentiable (fun α => hL2 (X α)) hδ hδ1)

/-- **Global lazy-training event with an extra good event and a bootstrap certificate.** This is the
proof of `exists_measurableSet_global_lazy_training_event` with two additions: the good event may be
intersected with any measurable family `Extra n` of probability at least `1 - κ`, and the bootstrap
constants `C` (displacement radius), `M` (Jacobian bound) and `R` (initial residual bound) are
exposed together with the corresponding bounds along every gradient flow. They feed the sharper
average-moment drift estimate `kernel_drift_le_of_neuron_moments`. -/
private theorem exists_measurableSet_global_lazy_training_event_with_extra
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (Extra : ∀ n : ℕ, Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)))
    (hExtra_meas : ∀ n, 0 < n → MeasurableSet (Extra n)) {κ : ℝ}
    (hExtra : ∀ n, 0 < n → (initMeasure n d).real (Extra n) ≥ 1 - κ) :
    ∃ (freezeRate jacRate taylorRate : ℕ → ℝ) (N : ℕ) (C M R : ℝ),
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto jacRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto taylorRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      0 ≤ C ∧ 0 ≤ M ∧ 0 ≤ R ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - 2 * ε - κ ∧ ∀ p ∈ E, p ∈ Extra n ∧
          ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ M ∧
          (∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ((∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0)) ∧
            ∀ t : ℝ, 0 ≤ t → ‖θ_traj t - packParams p.1 p.2‖ ≤ C ∧
              ‖outputJacobian (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)‖ ≤ M ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                R * Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              ‖outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                jacRate n ∧
              ‖trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
                WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
                    (θ_traj t - packParams p.1 p.2).ofLp)‖ ≤ taylorRate n) ∧
          ∀ i : Fin n, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  -- Consequences of the global derivative bounds, so callers need not supply them.
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  -- `L²` integrability of the activation-side observables (from linear growth).
  obtain ⟨hL2, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) :=
    fun α => hL2 (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⊙ Xs α) * φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => hL2mul (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⊙ Xs α) * deriv φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => hdL2mul (Xs α) (Xs β)
  -- Initial residual radius and initial spectral-gap failure.
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hU_ev := (tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
    hφ_L2 hdφ_L2 (half_pos hlambda_inf)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  -- Deterministic bootstrap constants.
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_jacobian_bound_and_good_events hact Xs hδ hδ1
  set M : ℝ := M₀ + 1 with hM
  set C : ℝ := M * R / (lambda_inf / 2 / 2) with hC
  set r : ℝ := C + 1 with hr
  set ℓ : ℕ → ℝ := fun n => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, Xs α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, Xs α j ^ 2))) / Real.sqrt (n : ℝ) with hℓ_def
  have hM_pos : 0 < M := by positivity
  have hℓ_nonneg : ∀ n, 0 ≤ ℓ n := fun n => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hℓ : Filter.Tendsto ℓ Filter.atTop (nhds 0) :=
    tendsto_jacobianLipschitzScale Xs C₁ C₂ hδ r
  have hrate : Filter.Tendsto (fun n => 2 * M * ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using (hℓ.const_mul (2 * M)).mul_const C
  have hjac : Filter.Tendsto (fun n => ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using hℓ.mul_const C
  have htay : Filter.Tendsto (fun n => ℓ n * C ^ 2 / 2) Filter.atTop (nhds 0) := by
    simpa using (hℓ.mul_const (C ^ 2)).div_const 2
  have hc : 0 < min 1 (lambda_inf / (8 * M)) := lt_min one_pos (by positivity)
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < min 1 (lambda_inf / (8 * M)) := by
    exact (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact hc))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_gt_atTop 0).and (hsmall.and hU_ev))
  obtain ⟨A, hA, hAev⟩ := jacobianLipschitzScale_le_sqrt_log_div Xs C₁ C₂ hδ r
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hAev
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨fun n => 2 * M * ℓ n * C, fun n => ℓ n * C, fun n => ℓ n * C ^ 2 / 2, max N N₂, C, M, R,
    hrate, hjac, htay, ⟨2 * M * A * C, by positivity, fun n hn => ?_⟩, hC0, hM_pos.le, hR_nonneg,
    fun n hn => ?_⟩
  · calc 2 * M * ℓ n * C ≤ 2 * M * (A * Real.sqrt (Real.log n / n)) * C := by
          gcongr; exact hN₂ n ((le_max_right _ _).trans hn)
      _ = 2 * M * A * C * Real.sqrt (Real.log n / n) := by ring
  obtain ⟨hn0, hsm, hU⟩ := hN n ((le_max_left _ _).trans hn)
  obtain ⟨E, hEm, hEμ, hEp⟩ := hM₀ n hn0
  set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | lambda_inf / 2 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) -
      limitingFullNTKMatrix φ X‖} with hUdef
  set T : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | R <
    ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖} with hTdef
  have hUm : MeasurableSet U :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs (limitingFullNTKMatrix φ X) _
  have hres_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)) := by
    simp_rw [trainingResidual_netFromParams_packParams]
    exact (evalVector_joint_measurable φ hmeasφ Xs).sub_const y
  have hTm : MeasurableSet T := measurableSet_lt measurable_const hres_meas.norm
  have hUr : (initMeasure n d).real U ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hU.le
  have hTr : (initMeasure n d).real T ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le (hR n)
  have hEc : (initMeasure n d).real Eᶜ ≤ 2 * δ := by
    rw [probReal_compl_eq_one_sub hEm]; linarith
  -- Union bound on the complement of `G = E ∩ Uᶜ ∩ Tᶜ`.
  have hG3c : (initMeasure n d).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ ≤ 2 * δ + ε + ε :=
    calc (initMeasure n d).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ
        ≤ (initMeasure n d).real (E ∩ Uᶜ)ᶜ + (initMeasure n d).real Tᶜᶜ :=
          measureReal_compl_inter_le _ _ _
      _ ≤ ((initMeasure n d).real Eᶜ + (initMeasure n d).real Uᶜᶜ) +
            (initMeasure n d).real Tᶜᶜ := by
          gcongr; exact measureReal_compl_inter_le _ _ _
      _ ≤ 2 * δ + ε + ε := by rw [compl_compl, compl_compl]; linarith
  have hXc : (initMeasure n d).real (Extra n)ᶜ ≤ κ := by
    rw [probReal_compl_eq_one_sub (hExtra_meas n hn0)]; linarith [hExtra n hn0]
  have hGc : (initMeasure n d).real ((E ∩ Uᶜ ∩ Tᶜ) ∩ Extra n)ᶜ ≤ 2 * δ + ε + ε + κ :=
    (measureReal_compl_inter_le _ _ _).trans (add_le_add hG3c hXc)
  refine ⟨(E ∩ Uᶜ ∩ Tᶜ) ∩ Extra n, ((hEm.inter hUm.compl).inter hTm.compl).inter
    (hExtra_meas n hn0),
    by linarith [one_sub_le_measureReal_of_measureReal_compl_le _ hGc], ?_⟩
  rintro p ⟨⟨⟨hpE, hpU⟩, hpT⟩, hpX⟩
  obtain ⟨hp1, hp2⟩ := hEp p hpE
  have hrr : ∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 2) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) *ᵥ v.ofLp) :=
    fun v => initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le φ X n p lambda_inf
      hK_gap (not_le.1 (show ¬ (lambda_inf / 2 ≤ _) from hpU)).le v
  have hres : ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ ≤ R :=
    not_lt.1 (show ¬ (R < _) from hpT)
  have hM_ge : M₀ + ℓ n * r ≤ M := by linarith [hsm.le.trans (min_le_left _ _)]
  have hr_nonneg : 0 ≤ r := by positivity
  obtain ⟨hJ_bdd_ball, hJ_lip_ball⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn0 Xs C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r (ℓ n) M hr_nonneg
    (hℓ_nonneg n) hM_ge le_rfl
  refine ⟨hpX, hJ_bdd_ball _ (by simpa using hr_nonneg), fun θ_traj hflow => ?_, hp2⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  have hg := lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn0 Xs y
    C₁ C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ (Nat.cast_pos.2 hm) M₀ p hp1 hp2
    θ_traj (lambda_inf / 2) r C M (ℓ n) hflow hdiff (half_pos hlambda_inf) (by positivity)
    (lt_add_one C) hM_pos.le (hℓ_nonneg n) hrr
    hM_ge le_rfl
    (by
      calc 2 * M * ℓ n * r = 2 * M * (ℓ n * r) := by ring
        _ ≤ 2 * M * (lambda_inf / (8 * M)) :=
          mul_le_mul_of_nonneg_left (hsm.le.trans (min_le_right _ _)) (by positivity)
        _ = lambda_inf / 2 / 2 := by field_simp; ring)
    (by
      calc M * ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ /
            (lambda_inf / 2 / 2) ≤ M * R / (lambda_inf / 2 / 2) := by gcongr
        _ = C := rfl)
  have hloss_decay : ∀ t : ℝ, 0 ≤ t → mseLoss (netFromParams φ n d) Xs y (θ_traj t) ≤
      mseLoss (netFromParams φ n d) Xs y (packParams p.1 p.2) *
        Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t) := fun t ht => by
    have h := (hg t ht).2.2.2.2
    rwa [show -(2 * (lambda_inf / 2 / 2) / (m : ℝ)) * t = -(lambda_inf / (2 * (m : ℝ))) * t by
      ring] at h
  refine ⟨⟨fun t ht => ?_, tendsto_zero_of_le_mul_exp_neg (by positivity)
    (fun t _ => by unfold mseLoss; positivity) hloss_decay⟩, fun t ht => ?_⟩
  · obtain ⟨-, hray, hdrift, hres_d, -⟩ := hg t ht
    refine ⟨fun v => ?_, hdrift, ?_, hloss_decay t ht⟩
    · have := hray v
      rwa [show lambda_inf / 2 / 2 = lambda_inf / 4 by ring] at this
    · rwa [show -(lambda_inf / 2 / 2 / (m : ℝ)) * t = -(lambda_inf / (4 * (m : ℝ))) * t by ring]
        at hres_d
  · obtain ⟨hdisp, -, -, hres_d, -⟩ := hg t ht
    have hball : ‖θ_traj t - packParams p.1 p.2‖ ≤ r := hdisp.trans (lt_add_one C).le
    refine ⟨hdisp, hJ_bdd_ball _ hball, ?_,
      (hJ_lip_ball _ hball).trans (mul_le_mul_of_nonneg_left hdisp (hℓ_nonneg n)),
      (norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) Xs (packParams p.1 p.2) r
        (ℓ n) (fun z _ β => (hasFDerivAt_netFromParams φ n d (Xs β) z
          fun i => hφ.differentiableAt).differentiableAt) hJ_lip_ball hball).trans ?_⟩
    · rw [show -(lambda_inf / (4 * (m : ℝ))) * t = -(lambda_inf / 2 / 2 / (m : ℝ)) * t by ring]
      exact hres_d.trans (mul_le_mul_of_nonneg_right hres (Real.exp_nonneg _))
    · calc ℓ n / 2 * ‖θ_traj t - packParams p.1 p.2‖ ^ 2 ≤ ℓ n / 2 * C ^ 2 := by gcongr
        _ = ℓ n * C ^ 2 / 2 := by ring

/-- **Measurable good event for global positive-gap lazy training, with all bootstrap constants
discharged.** Assume a
`SmoothActivation` (differentiable, bounded derivative, Lipschitz derivative; no bound on the
value of `φ`), and that the limiting kernel satisfies `K_∞ ≥ lambda_inf • 1` with
`lambda_inf > 0`. For every `δ ∈ (0, 1]` and `ε > 0` there are a deterministic sequence
`freezeRate n → 0` and a width `N` such that for every `n ≥ N`,
there is a *measurable* event `E` of `initMeasure n d`-probability at least `1 - 2 * δ - 2 * ε`
such that from every initialization in `E`, every gradient flow started at `θ₀ = packParams W a`
satisfies, for all `t ≥ 0`:

* the empirical NTK has Rayleigh quotient at least `lambda_inf / 4`, i.e. a uniform spectral gap
  (the initial half-gap `lambda_inf / 2` is halved once more inside the bootstrap ball);
* the kernel drift is at most `freezeRate n`;
* the residual norm and the MSE loss decay exponentially, at rates `lambda_inf / (4 m)` and
  `lambda_inf / (2 m)`;

and the training loss tends to `0` as `t → ∞`.

No hypothesis is shaped like the conclusion: the four failure probabilities (Jacobian norm,
maximum readout weight, initial spectral gap, initial residual size) are allocated explicitly, the
residual radius comes from output tightness (`exists_initial_residual_radius`), and the
feasibility inequalities of the deterministic bootstrap hold eventually in `n` because the
Jacobian-Lipschitz scale at a fixed radius vanishes with the width. As for the other event
theorems, this is an a priori estimate for any `ForwardGFTrajectory`. -/
theorem exists_measurableSet_global_lazy_training_event
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - 2 * ε ∧ ∀ p ∈ E,
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, _, _, N, C, M, R, hrate, -, -, hK₀, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap hδ hδ1 hε (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ) (κ := 0)
      (fun n _ => by simp)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, by linarith, fun p hp θ_traj hflow => ((hEp p hp).2.2.1 θ_traj hflow).1⟩

/-- **Global lazy training with kernel drift `O(n⁻¹ᐟ²)`.** Under the hypotheses of
`exists_measurableSet_global_lazy_training_event`, with the same conclusions, the drift rate obeys
`freezeRate n ≤ K₀ / √n` (no logarithm) on a measurable event of probability at least
`1 - 3 δ - 2 ε`. The extra `δ` pays for the Markov bound on the empirical neuron moment
(`exists_neuronMoment_event`); the deterministic estimate is
`kernel_drift_le_of_neuron_moments`. The logarithmic theorem is kept because its event does not need
the fourth-moment observable. -/
theorem exists_measurableSet_global_lazy_training_event_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 3 * δ - 2 * ε ∧ ∀ p ∈ E,
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ_traj t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ_traj t)) Filter.atTop (nhds 0) := by
  have hφ := hact.differentiable
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, -⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, -, -, -⟩ := activation_memLp_two hact (d := d)
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  obtain ⟨τ, hτ, hτev⟩ := exists_neuronMoment_event hφ.continuous.measurable C₁ C₂ Xs
    (fun α => hL2 (Xs α)) hδ
  obtain ⟨freezeRate, _, _, N, C, M, R, hrate, -, -, -, hC, hM, hR, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap hδ hδ1 hε
      (fun n => {p | (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ Xs (p.1 i) (p.2 i) ≤ τ})
      (fun n hn => (hτev n hn).1) (κ := δ) (fun n hn => (hτev n hn).2)
  have hν : 0 < lambda_inf / (4 * (m : ℝ)) := by positivity
  set K : ℝ := 2 * M * (R / ((m : ℝ) * (lambda_inf / (4 * (m : ℝ)))) *
    Real.sqrt (2 * (1 + C ^ 2) * τ)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨fun n => min (freezeRate n) (K / Real.sqrt (n : ℝ)), max N 1, ?_, ⟨K, hK0,
    fun n _ => min_le_right _ _⟩, fun n hn => ?_⟩
  · simpa using hrate.min (tendsto_const_div_sqrt_nat_atTop K)
  obtain ⟨E, hEm, hE, hEp⟩ := h n ((le_max_left _ _).trans hn)
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
  refine ⟨E, hEm, by linarith, fun p hp θ_traj hflow => ?_⟩
  obtain ⟨hpX, hJ0, hall, -⟩ := hEp p hp
  obtain ⟨⟨horig, htend⟩, hcert⟩ := hall θ_traj hflow
  refine ⟨fun t ht => ?_, htend⟩
  obtain ⟨hray, hdrift, hres, hloss⟩ := horig t ht
  refine ⟨hray, le_min hdrift ?_, hres, hloss⟩
  have hmom : (n : ℝ)⁻¹ * ∑ i : Fin n, neuronMoment φ C₁ C₂ Xs
      (unpackW (packParams p.1 p.2) i) (unpackA (packParams p.1 p.2) i) ≤ τ := by
    simpa [unpackW_packParams, unpackA_packParams] using hpX
  have hsharp := kernel_drift_le_of_neuron_moments φ hφ hC₁_nonneg hC₂_nonneg hφ_lip
    hact.deriv_bdd hact.deriv_lip hn0 hm Xs y hflow hν (fun t ht => (hcert t ht).1)
    (fun t ht => (hcert t ht).2.2.1) (fun t ht => (hcert t ht).2.1) hJ0 hmom ht
  refine hsharp.trans (le_of_eq ?_)
  rw [hK]; ring

/-- **Kernel freeze on `[0, ∞)` from a positive limiting gap.** The kernel-drift component of
`exists_measurableSet_global_lazy_training_event`: with probability at least
`1 - 2 * δ - 2 * ε` every gradient flow keeps the empirical NTK within `freezeRate n → 0` of its
initial value for all `t ≥ 0`. -/
theorem exists_kernel_freeze_event_of_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t : ℝ, 0 ≤ t →
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ freezeRate n} ≥
        1 - 2 * δ - 2 * ε := by
  obtain ⟨freezeRate, N, hrate, -, h⟩ := exists_measurableSet_global_lazy_training_event hm hd φ
    hact X y lambda_inf hlambda_inf hK_gap hδ hδ1 hε
  refine ⟨freezeRate, N, hrate, fun n hn => ?_⟩
  obtain ⟨E, -, hE, hEp⟩ := h n hn
  exact hE.trans (measureReal_mono fun p hp θ_traj hflow t ht =>
    ((hEp p hp θ_traj hflow).1 t ht).2.1)

/-- **Global positive-gap lazy training limit (paper-facing form).** Let `θ n p` be trajectories
that solve the gradient-flow ODE for `initMeasure n d`-almost every initialization, and assume the
limiting kernel satisfies `K_∞ ≥ lambda_inf • 1`, `lambda_inf > 0`. For every confidence
`η ∈ (0, 1]` there are a drift rate `freezeRate n → 0`, with
`freezeRate n ≤ K₀ √(log n / n)` (the logarithm comes from the maximum readout weight), and a width
`N` such that for `n ≥ N` there is a *measurable* initialization event `E` of probability at least
`1 - η` on which, for almost every initialization, and all `t ≥ 0`: the empirical NTK has Rayleigh
quotient at least `lambda_inf / 4`, it stays within `freezeRate n` of `K_n(0)`, and the residual
norm and MSE loss decay exponentially; moreover the loss tends to `0` as `t → ∞`.

The exact limiting trajectory and the fixed-time weak limits are the separate theorems
`tendstoInDistribution_trainingResidual_matrix_exp` and
`tendstoInDistribution_trainingOutputs_matrix_exp`. -/
theorem global_positive_gap_lazy_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - η ∧ ∀ᵐ p ∂(initMeasure n d), p ∈ E →
          (∀ t : ℝ, 0 ≤ t →
            (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
              v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
            ‖empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
              empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
              freezeRate n ∧
            ‖trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
            mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                (θ n p t) ≤
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (packParams p.1 p.2) *
                Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
          Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, N, hrate, hK₀, h⟩ := exists_measurableSet_global_lazy_training_event hm hd
    φ hact X y lambda_inf hlambda_inf hK_gap (δ := η / 4) (ε := η / 4) (by positivity)
    (by linarith) (by positivity)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, le_of_eq_of_le (by ring) hE, (hθ_flow n).mono fun p hflow hpE =>
    hEp p hpE (θ n p) hflow⟩

/-- **Global positive-gap lazy training limit with drift `O(n⁻¹ᐟ²)`.** The statement of
`global_positive_gap_lazy_training_limit` with the drift rate improved from `O(√(log n / n))` to
`freezeRate n ≤ K₀ / √n`, at the same confidence `1 - η`. The improvement replaces the maximum
readout weight by an average of a per-neuron moment
(`exists_measurableSet_global_lazy_training_event_inv_sqrt_width`). -/
theorem global_positive_gap_lazy_training_limit_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - η ∧ ∀ᵐ p ∂(initMeasure n d), p ∈ E →
          (∀ t : ℝ, 0 ≤ t →
            (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
              v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
            ‖empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
              empiricalNTKMatrix (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
              freezeRate n ∧
            ‖trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
            mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                (θ n p t) ≤
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (packParams p.1 p.2) *
                Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
          Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0) := by
  obtain ⟨freezeRate, N, hrate, hK₀, h⟩ :=
    exists_measurableSet_global_lazy_training_event_inv_sqrt_width hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap (δ := η / 5) (ε := η / 5) (by positivity)
    (by linarith) (by positivity)
  refine ⟨freezeRate, N, hrate, hK₀, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, le_of_eq_of_le (by ring) hE, (hθ_flow n).mono fun p hflow hpE =>
    hEp p hpE (θ n p) hflow⟩

/-- **Single-confidence form of `exists_kernel_freeze_event_of_positive_gap`.** For every
confidence level `η ∈ (0, 1]` there are a deterministic drift rate `freezeRate n → 0` and a width
`N` such that for `n ≥ N`, with `initMeasure n d`-probability at least `1 - η`, every gradient flow
from `packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value for all
`t ≥ 0`. This is the main theorem with `δ = ε = η / 4`.

This is an a priori estimate for any `ForwardGFTrajectory`; it does not assert that gradient flows
exist. -/
theorem exists_kernel_freeze_event_of_positive_gap_of_confidence
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t : ℝ, 0 ≤ t →
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - η := by
  obtain ⟨freezeRate, N, hrate, h⟩ := exists_kernel_freeze_event_of_positive_gap hm hd φ hact X y
    lambda_inf hlambda_inf hK_gap (δ := η / 4) (ε := η / 4)
    (by positivity) (by linarith) (by positivity)
  exact ⟨freezeRate, N, hrate, fun n hn => le_of_eq_of_le (by ring) (h n hn)⟩

/-- **Measurable good event for finite-horizon lazy training (no spectral gap).** Assume a
`SmoothActivation` (no bound on the value of `φ`). For every horizon
`T ≥ 0`, `δ ∈ (0, 1]` and `ε > 0` there are a radius `R ≥ 0`, a deterministic sequence
`freezeRate n → 0` and a width `N` such that for `n ≥ N` there is a *measurable* event `E` of
`initMeasure n d`-probability at least `1 - 2 * δ - ε` on which the initial residual has norm at
most `R` and every gradient flow from `packParams W a`, for all `t ∈ [0, T]`,
keeps the empirical NTK within `freezeRate n` of its initial value, keeps the output Jacobian within
`jacRate n` of its initial value (*Jacobian* freezing, which is strictly stronger than kernel
freezing since `K = J Jᵀ`), and stays within `taylorRate n` of its initialization linearization
`f(θ₀) + J(θ₀) (θ(t) - θ₀)`. All three rates tend to `0`; they come from the single displacement
bound `‖θ(t) - θ₀‖ ≤ C` and the Jacobian Lipschitz scale `ℓ n` (`jacRate n = ℓ n C`,
`taylorRate n = ℓ n C² / 2` by `norm_trainingOutputs_sub_linearization_le`).

Unlike the positive-gap event, no lower bound on the spectrum of the limiting kernel is assumed:
positive semidefiniteness bounds the residual by its initial size
(`finite_horizon_kernel_freeze_bound`), the initial residual is controlled by
`exists_initial_residual_radius`, and the displacement radius `r = C + 1` with `C = T * M * R / m`
depends on `T`. Exposing a measurable event (rather than only its measure) lets later arguments
intersect it with other events and take complements. This is an a priori estimate for any
`GFTrajectory`; it does not assert that gradient flows exist. -/
theorem exists_measurableSet_finite_horizon_lazy_training_event
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (R C M : ℝ) (freezeRate jacRate taylorRate : ℕ → ℝ) (N : ℕ), 0 ≤ R ∧
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto jacRate Filter.atTop (nhds 0) ∧
      Filter.Tendsto taylorRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - ε ∧
        ∀ p ∈ E,
          ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ ≤ R ∧
          (∀ i : Fin n, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))) ∧
          ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤ M ∧
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                jacRate n ∧
              ‖trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                trainingOutputs (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) -
                WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
                    (θ_traj t - packParams p.1 p.2).ofLp)‖ ≤ taylorRate n ∧
              ‖θ_traj t - packParams p.1 p.2‖ ≤ C := by
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) := fun α =>
    (activation_memLp_two hact (d := d)).1 (Xs α)
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  -- Deterministic bootstrap constants; the displacement target `C` grows linearly with `T`.
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_jacobian_bound_and_good_events hact Xs hδ hδ1
  set M : ℝ := M₀ + 1 with hM
  set C : ℝ := T * M * R / m with hC
  set r : ℝ := C + 1 with hr
  set ℓ : ℕ → ℝ := fun n => Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, Xs α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, Xs α j ^ 2))) / Real.sqrt (n : ℝ) with hℓ_def
  have hM_pos : 0 < M := by positivity
  have hr_nonneg : 0 ≤ r := by positivity
  have hℓ_nonneg : ∀ n, 0 ≤ ℓ n := fun n => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hℓ : Filter.Tendsto ℓ Filter.atTop (nhds 0) :=
    tendsto_jacobianLipschitzScale Xs C₁ C₂ hδ r
  have hrate : Filter.Tendsto (fun n => 2 * M * ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using (hℓ.const_mul (2 * M)).mul_const C
  have hjac : Filter.Tendsto (fun n => ℓ n * C) Filter.atTop (nhds 0) := by
    simpa using hℓ.mul_const C
  have htay : Filter.Tendsto (fun n => ℓ n * C ^ 2 / 2) Filter.atTop (nhds 0) := by
    simpa using (hℓ.mul_const (C ^ 2)).div_const 2
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < 1 :=
    (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact one_pos))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.eventually_gt_atTop 0).and hsmall)
  refine ⟨R, C, M, fun n => 2 * M * ℓ n * C, fun n => ℓ n * C, fun n => ℓ n * C ^ 2 / 2, N,
    hR_nonneg, hrate, hjac, htay, fun n hn => ?_⟩
  obtain ⟨hn0, hsm⟩ := hN n hn
  obtain ⟨E, hEm, hEμ, hEp⟩ := hM₀ n hn0
  set Tail : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | R <
    ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖} with hTail
  have hTr : (initMeasure n d).real Tail ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le (hR n)
  have hEc : (initMeasure n d).real Eᶜ ≤ 2 * δ := by
    rw [probReal_compl_eq_one_sub hEm]; linarith
  have hGc : (initMeasure n d).real (E ∩ Tailᶜ)ᶜ ≤ 2 * δ + ε :=
    (measureReal_compl_inter_le _ _ _).trans (by rw [compl_compl]; linarith)
  have hres_meas : Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) =>
      trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)) := by
    simp_rw [trainingResidual_netFromParams_packParams]
    exact (evalVector_joint_measurable φ hmeasφ Xs).sub_const y
  refine ⟨E ∩ Tailᶜ, hEm.inter (measurableSet_lt measurable_const hres_meas.norm).compl,
    by linarith [one_sub_le_measureReal_of_measureReal_compl_le _ hGc], ?_⟩
  rintro p ⟨hpE, hpT⟩
  obtain ⟨hp1, hp2⟩ := hEp p hpE
  have hres : ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ ≤ R :=
    not_lt.1 (show ¬ (R < _) from hpT)
  obtain ⟨hJ_bdd, hJ_lip⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn0 Xs C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ M₀ p hp1 hp2 r (ℓ n) M hr_nonneg
    (hℓ_nonneg n) (by linarith) le_rfl
  refine ⟨hres, hp2, hJ_bdd _ (by simpa using hr_nonneg), fun θ_traj hflow t ht => ?_⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  have hdisp := finite_horizon_displacement_bound (netFromParams φ n d) Xs y hflow hdiff T M r C hT
    hM_pos.le (Nat.cast_pos.2 hm) hr_nonneg (lt_add_one C) (by rw [hC]; gcongr) hJ_bdd t ht
  have hball : ‖θ_traj t - packParams p.1 p.2‖ ≤ r := hdisp.trans (lt_add_one C).le
  refine ⟨finite_horizon_kernel_freeze_bound (netFromParams φ n d) Xs y hflow hdiff T M (ℓ n) r C
    hT hM_pos.le (hℓ_nonneg n) (Nat.cast_pos.2 hm) hr_nonneg (lt_add_one C)
    (by rw [hC]; gcongr) hJ_bdd hJ_lip t ht,
    (hJ_lip _ hball).trans (mul_le_mul_of_nonneg_left hdisp (hℓ_nonneg n)),
    (norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) Xs (packParams p.1 p.2) r
      (ℓ n) (fun z _ β => (hasFDerivAt_netFromParams φ n d (Xs β) z
        fun i => hφ.differentiableAt).differentiableAt) hJ_lip hball).trans ?_, hdisp⟩
  calc ℓ n / 2 * ‖θ_traj t - packParams p.1 p.2‖ ^ 2 ≤ ℓ n / 2 * C ^ 2 := by
        gcongr
    _ = ℓ n * C ^ 2 / 2 := by ring

/-- **Measurable good event for the finite-horizon kernel freeze (no spectral gap).** The kernel
component of `exists_measurableSet_finite_horizon_lazy_training_event`: with probability at least
`1 - 2 * δ - ε` the initial residual has norm at most `R` and every gradient flow keeps the
empirical NTK within `freezeRate n → 0` of its initial value on `[0, T]`. -/
theorem exists_measurableSet_finite_horizon_kernel_freeze
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (R : ℝ) (freezeRate : ℕ → ℝ) (N : ℕ), 0 ≤ R ∧
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - ε ∧
        ∀ p ∈ E,
          ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ ≤ R ∧
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n := by
  obtain ⟨R, _, _, freezeRate, _, _, N, hR, hrate, -, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT hδ hδ1 hε
  refine ⟨R, freezeRate, N, hR, hrate, fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  exact ⟨E, hEm, hE, fun p hp => ⟨(hEp p hp).1, fun θ_traj hflow t ht =>
    ((hEp p hp).2.2.2 θ_traj hflow t ht).1⟩⟩

/-- **Finite-horizon kernel freeze with no spectral gap.** Consequence of
`exists_measurableSet_finite_horizon_kernel_freeze`: for every horizon `T ≥ 0`, `δ ∈ (0, 1]` and
`ε > 0` there are a deterministic sequence `freezeRate n → 0` and a width `N` such that for `n ≥ N`,
with `initMeasure n d`-probability at least `1 - 2 * δ - ε`, every gradient flow started at
`packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value on `[0, T]`.
No lower bound on the spectrum of the limiting kernel is assumed, in contrast to
`exists_kernel_freeze_event_of_positive_gap`. -/
theorem exists_finite_horizon_kernel_freeze_event
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - 2 * δ - ε := by
  obtain ⟨R, freezeRate, N, -, hrate, h⟩ :=
    exists_measurableSet_finite_horizon_kernel_freeze hm φ hact X y T hT hδ hδ1 hε
  refine ⟨freezeRate, N, hrate, fun n hn => ?_⟩
  obtain ⟨E, -, hE, hEp⟩ := h n hn
  exact hE.trans (measureReal_mono fun p hp => (hEp p hp).2)

/-- **Single-confidence form of `exists_finite_horizon_kernel_freeze_event`** (`δ = ε = η / 3`):
probability at least `1 - η` for `η ∈ (0, 1]`. -/
theorem exists_finite_horizon_kernel_freeze_event_of_confidence
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
            ForwardGFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n} ≥ 1 - η := by
  obtain ⟨freezeRate, N, hrate, h⟩ := exists_finite_horizon_kernel_freeze_event hm φ hact X y T hT
    (δ := η / 3) (ε := η / 3) (by positivity)
    (by linarith) (by positivity)
  exact ⟨freezeRate, N, hrate, fun n hn => le_of_eq_of_le (by ring) (h n hn)⟩

end InitializationEvents

section FiniteHorizonLimit

/-!
#### Target Theorem 1: Finite-Horizon NTK Training Limit (Phase 0 Target)

**Status.** Proved, with bundled activation hypotheses `SmoothActivation` in place of
`hderiv_lip` alone: conclusion 1 is `tendsto_measure_kernel_drift_finite_horizon`, conclusion 2 is
`tendstoInDistribution_trainingResidual_matrix_exp`, and conclusion 3 is
`tendstoInDistribution_trainingOutputs_matrix_exp`. The commented signature below is kept as the
original target.

**Formal Probability Data**:
For each width `n : ℕ`:
- Parameter probability space: `Ω n := (Fin n → Fin d → ℝ) × (Fin n → ℝ)` with measure
  `μ n := initMeasure n d`.
- Parameter packing: `θ₀ n (p : Ω n) := packParams p.1 p.2`.
- Random trajectory family:
  `θ : ∀ n : ℕ, Ω n → ℝ → EuclideanSpace ℝ (Fin (n * d + n))`
  satisfying:
  - Initial condition and gradient flow ODE: for each `n`, for `initMeasure n d`-almost every `p`,
    `ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)`.
    Here `mseLoss` already contains the `1 / m` normalization, so `ForwardGFTrajectory`
    corresponds to `θ' = -∇ mseLoss`, yielding the intended residual dynamics
    `r'(t) = -(1 / m) K(t) r(t)`.
  - Trajectory measurability: `∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d)`.
    Path continuity in `t` and measurability in `p` reduce the uniform supremum event
    `{p | ∃ t ∈ Set.Icc 0 T, ‖K n t p - K n 0 p‖ > ε}` to a countable dense subset of `[0, T]`,
    ensuring measurability of the supremum event.
- Observable random variables:
  - Residual:
    `r n t p := trainingResidual (netFromParams φ n d)`
      `(fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)`.
  - Predictions:
    `trainingOutputs (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)`.
  - Empirical NTK:
    `K n t p := empiricalNTKMatrix (netFromParams φ n d)`
      `(fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)`.

**Conclusions** (on any compact time horizon `[0, T]` with `T ≥ 0`):
1. **Kernel Stationarity**: The empirical NTK remains asymptotically stationary on `[0, T]`:
   `∀ ε > 0, Filter.Tendsto (fun n => (μ n) {p | ∃ t ∈ Set.Icc 0 T,`
     `‖K n t p - K n 0 p‖ > ε}) Filter.atTop (nhds 0)`.
2. **Fixed-Time Residual Weak Convergence**: For each fixed `t ∈ [0, T]`, the residual vector
   converges in distribution to the linearized infinite-width trajectory:
   `MeasureTheory.TendstoInDistribution (fun n p => r n t p) Filter.atTop`
     `(fun G => WithLp.toLp 2`
     `  ((NormedSpace.exp (- (t / m : ℝ) • limitingFullNTKMatrix φ X)) *ᵥ (G - y).ofLp))`
     `(fun n => initMeasure n d) (multivariateGaussian 0 (limitingCovariance φ scaledX))`.
3. **Fixed-Time Prediction Convergence**: The network predictions converge in distribution:
   `MeasureTheory.TendstoInDistribution (fun n p => trainingOutputs ... (θ n p t)) Filter.atTop`
     `(fun G => y + WithLp.toLp 2`
     `  ((NormedSpace.exp (- (t / m : ℝ) • limitingFullNTKMatrix φ X)) *ᵥ (G - y).ofLp))`
     `(fun n => initMeasure n d) (multivariateGaussian 0 (limitingCovariance φ scaledX))`.

**Mechanism**:
This theorem does not require a positive spectral gap. PSD controls the residual norm, while
finite-horizon displacement and the width-decaying Jacobian Lipschitz estimate imply kernel
stationarity.

**Commented Formal Lean Signature**:
```lean
/-
theorem finite_horizon_ntk_training_limit
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hderiv_lip : ∃ L_φ' : ℝ, 0 ≤ L_φ' ∧ LipschitzWith (Real.toNNReal L_φ') (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    (∀ ε > 0, Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc 0 T,
        ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖ > ε})
      Filter.atTop (nhds 0)) ∧
    (∀ t ∈ Set.Icc 0 T,
      MeasureTheory.TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t))
        Filter.atTop
        (fun (G : EuclideanSpace ℝ (Fin m)) =>
          (WithLp.toLp 2 ((NormedSpace.exp (- (t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))) ∧
    (∀ t ∈ Set.Icc 0 T,
      MeasureTheory.TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t))
        Filter.atTop
        (fun (G : EuclideanSpace ℝ (Fin m)) =>
          y + (WithLp.toLp 2 ((NormedSpace.exp (- (t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k))))
-/
```
-/


/-! #### Proved consequences of the finite-horizon freeze event

The measurable good event of `exists_measurableSet_finite_horizon_kernel_freeze` yields, for a
family of trajectories that solve the gradient-flow ODE almost everywhere in the initialization,
kernel stationarity in probability on `[0, T]` and, below, convergence of the residual to the
frozen matrix-exponential residual. -/

/-- Any positive `κ : ℝ≥0∞` dominates `ENNReal.ofReal c` for some real `c > 0`. -/
private lemma exists_pos_real_ofReal_le {κ : ENNReal} (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c ≤ κ := by
  by_cases h : κ = ⊤
  · exact ⟨1, one_pos, by simp [h]⟩
  · exact ⟨κ.toReal, ENNReal.toReal_pos hκ.ne' h, (ENNReal.ofReal_toReal h).le⟩

/-- `μ S ≤ ofReal c` from the corresponding bound on `μ.real S`, for a finite measure. -/
private lemma measure_le_ofReal_of_measureReal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {S : Set α} {c : ℝ} (h : μ.real S ≤ c) :
    μ S ≤ ENNReal.ofReal c :=
  (ENNReal.ofReal_toReal (measure_ne_top μ S)).symm.le.trans (ENNReal.ofReal_le_ofReal h)

/-- **Generic "supremum of a drift tends to zero in probability", budget depending on the
tolerance.** Let `μ n` be probability measures and `Good n p` a property holding almost surely (in
applications, "the trajectory `θ n p` solves the gradient-flow ODE"). Fix `ε₀ > 0`. Suppose that for
every confidence level `c > 0` and all large `n` there is a measurable event `E` of failure
probability at most `c` on which `D n p t ≤ ε₀` for all `t ∈ S` (whenever `Good n p`). Then the
probability that `D n p t` exceeds `ε₀` at some `t ∈ S` tends to zero. The bad set need not be
measurable, so `μ n` evaluates it as an outer measure. -/
theorem tendsto_measure_exists_gt_of_eventually_good_events {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (S : Set ℝ) (Good : ∀ n, Ω n → Prop) (D : ∀ n, Ω n → ℝ → ℝ)
    (hgood : ∀ n, ∀ᵐ p ∂(μ n), Good n p) {ε₀ : ℝ}
    (hev : ∀ c : ℝ, 0 < c → ∀ᶠ n in Filter.atTop, ∃ E : Set (Ω n), MeasurableSet E ∧
      (μ n).real Eᶜ ≤ c ∧ ∀ p ∈ E, Good n p → ∀ t ∈ S, D n p t ≤ ε₀) :
    Filter.Tendsto (fun n => μ n {p | ∃ t ∈ S, ε₀ < D n p t}) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨c, hc, hcκ⟩ := exists_pos_real_ofReal_le hκ
  filter_upwards [hev c hc] with n hEn
  obtain ⟨E, hEm, hEc, hEp⟩ := hEn
  have hnull : μ n {p | ¬ Good n p} = 0 := ae_iff.1 (hgood n)
  calc μ n {p | ∃ t ∈ S, ε₀ < D n p t} ≤ μ n (Eᶜ ∪ {p | ¬ Good n p}) := by
        refine measure_mono fun p hp => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon
        obtain ⟨hpE, hg⟩ := hcon
        obtain ⟨t, ht, hgt⟩ := hp
        have := hEp p hpE hg t ht
        linarith
    _ ≤ μ n Eᶜ + 0 := by rw [← hnull]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal c := by rw [add_zero]; exact measure_le_ofReal_of_measureReal_le _ hEc
    _ ≤ κ := hcκ

/-- **Generic "supremum of a drift tends to zero in probability".** The special case of
`tendsto_measure_exists_gt_of_eventually_good_events` in which, for each confidence level `c`, the
good event forces `D n p t ≤ ρ n` for a fixed sequence `ρ → 0`. This is the shared endgame of the
kernel-, Jacobian- and linearization-drift theorems below. -/
theorem tendsto_measure_exists_gt_of_good_events {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)] (S : Set ℝ)
    (Good : ∀ n, Ω n → Prop) (D : ∀ n, Ω n → ℝ → ℝ)
    (hgood : ∀ n, ∀ᵐ p ∂(μ n), Good n p)
    (hev : ∀ c : ℝ, 0 < c → ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, ∃ E : Set (Ω n), MeasurableSet E ∧ (μ n).real Eᶜ ≤ c ∧
        ∀ p ∈ E, Good n p → ∀ t ∈ S, D n p t ≤ ρ n)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto (fun n => μ n {p | ∃ t ∈ S, ε₀ < D n p t}) Filter.atTop (nhds 0) :=
  tendsto_measure_exists_gt_of_eventually_good_events μ S Good D hgood fun c hc => by
    obtain ⟨ρ, hρ, hn⟩ := hev c hc
    filter_upwards [hn, hρ.eventually (gt_mem_nhds hε₀)] with n hEn hlt
    obtain ⟨E, hEm, hEc, hEp⟩ := hEn
    exact ⟨E, hEm, hEc, fun p hp hg t ht => (hEp p hp hg t ht).trans hlt.le⟩

/-- **Kernel stationarity in probability on `[0, T]`.** If the trajectories `θ n p` solve the
gradient-flow ODE for `initMeasure n d`-almost every initialization, then for every `ε₀ > 0` the
probability that the empirical NTK drifts by more than `ε₀` somewhere on `[0, T]` tends to zero.
The event is not shown measurable, so `initMeasure n d` evaluates it as an *outer* probability; the
proof bounds it by the complement of the measurable good event of
`exists_measurableSet_finite_horizon_kernel_freeze`. No spectral gap is assumed. -/
theorem tendsto_measure_kernel_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, freezeRate, N, -, hrate, h⟩ := exists_measurableSet_finite_horizon_kernel_freeze hm φ
    hact X y T hT (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity))
    (min_le_left _ _) (by positivity)
  refine ⟨freezeRate, hrate, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (hEp p hp).2 (θ n p) hflow t ht
    rwa [hflow.init]

/-- **Jacobian stationarity in probability on `[0, T]`.** Under the hypotheses of
`tendsto_measure_kernel_drift_finite_horizon`, for every `ε₀ > 0` the probability that the output
Jacobian `J(θ(t))` moves by more than `ε₀` (in Frobenius norm) from `J(θ(0))` somewhere on `[0, T]`
tends to zero. This is the tangent-feature freezing statement proper: it is not deduced from
`tendsto_measure_kernel_drift_finite_horizon`, since `K = J Jᵀ` can stay put while `J` rotates. It
comes from the same displacement bound and the Jacobian Lipschitz estimate
(`exists_measurableSet_finite_horizon_lazy_training_event`). -/
theorem tendsto_measure_jacobian_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, _, _, _, jacRate, _, N, -, -, hjac, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨jacRate, hjac, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := ((hEp p hp).2.2.2 (θ n p) hflow t ht).2.1
    rwa [hflow.init]

/-- **The trained network stays close to its initialization linearization on `[0, T]`.** Under the
hypotheses of `tendsto_measure_kernel_drift_finite_horizon`, for every `ε₀ > 0` the probability that
`‖f(θ(t)) - f(θ(0)) - J(θ(0)) (θ(t) - θ(0))‖ > ε₀` somewhere on `[0, T]` tends to zero, where `f`
is the vector of training outputs and `J` the output Jacobian. The remainder is bounded
deterministically by `norm_trainingOutputs_sub_linearization_le` (Lipschitz Jacobian on the
displacement ball). Test inputs are handled by
`tendsto_measure_test_linearization_error_finite_horizon`. -/
theorem tendsto_measure_linearization_error_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
              (θ n p t - θ n p 0).ofLp)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
          (θ n p t - θ n p 0).ofLp)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, _, _, _, _, taylorRate, N, -, -, -, htay, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨taylorRate, htay, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := ((hEp p hp).2.2.2 (θ n p) hflow t ht).2.2.1
    rwa [hflow.init]

/-- **Jacobian stationarity in probability on `[0, ∞)` from a positive limiting gap.** If the
limiting kernel satisfies `K_∞ ≥ lambda_inf • 1` with `lambda_inf > 0` and the trajectories `θ n p`
solve the gradient-flow ODE for almost every initialization, then for every `ε₀ > 0` the probability
that the output Jacobian moves by more than `ε₀` from `J(θ(0))` at *some* time `t ≥ 0` tends to
zero, i.e. `P(sup_{t ≥ 0} ‖J(θ(t)) - J(θ(0))‖ > ε₀) → 0`. The displacement bound is uniform in time
because the positive gap makes the residual decay exponentially; the finite-horizon counterpart
needs no gap (`tendsto_measure_jacobian_drift_finite_horizon`). Jacobian freezing is proved directly
from the Jacobian Lipschitz bound, not inferred from kernel freezing. -/
theorem tendsto_measure_jacobian_drift_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, jacRate, _, N, C, M, R, -, hjac, htay, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨jacRate, hjac, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (((hEp p hp).2.2.1 (θ n p) hflow).2 t ht).2.2.2.1
    rwa [hflow.init]

/-- **Linearization error in probability on `[0, ∞)` from a positive limiting gap.** Under the
hypotheses of `tendsto_measure_jacobian_drift_global_positive_gap`, for every `ε₀ > 0` the
probability that `‖f(θ(t)) - f(θ(0)) - J(θ(0)) (θ(t) - θ(0))‖ > ε₀` at some `t ≥ 0` tends to zero:
the full nonlinear network stays within `o(1)` of its initialization linearization for all time at
the training inputs. Test inputs are handled by
`tendsto_measure_test_linearization_error_global_positive_gap`. -/
theorem tendsto_measure_linearization_error_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
              (θ n p t - θ n p 0).ofLp)‖})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => ‖trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
      trainingOutputs (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
          (θ n p t - θ n p 0).ofLp)‖) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, _, taylorRate, N, C, M, R, -, hjac, htay, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨taylorRate, htay, (Filter.eventually_ge_atTop N).mono fun n hn => ?_⟩
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · have hb := (((hEp p hp).2.2.1 (θ n p) hflow).2 t ht).2.2.2.2
    rwa [hflow.init]

/-- Deterministic test-point linearization bound: at any input `x`, if the readout weights of `θ₀`
are bounded by `R` and `‖θ - θ₀‖ ≤ C`, the network differs from its linearization at `θ₀` by at most
`(K_x(R) / (2 √n)) C²`. Instantiates `abs_netFromParams_sub_linearization_le` for a
`SmoothActivation`. -/
private lemma abs_netFromParams_sub_linearization_le_of_disp {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {n d : ℕ} (hn : 0 < n) (x : Fin d → ℝ)
    {θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n))} {R C : ℝ}
    (hR : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) (hΔ : ‖θ - θ₀‖ ≤ C) :
    |netFromParams φ n d x θ - netFromParams φ n d x θ₀ - ⟪gradParams φ n d x θ₀, θ - θ₀⟫| ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) / 2 * C ^ 2 := by
  obtain ⟨hC₁, hC₂, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  refine (abs_netFromParams_sub_linearization_le φ hact.differentiable n d hn x θ₀ θ C₁ C₂ R hC₁
    hC₂ ((abs_nonneg _).trans (hR ⟨0, hn⟩)) hφ_lip hact.deriv_bdd hact.deriv_lip hR).trans ?_
  gcongr

open Filter Topology in
/-- The test-point remainder rate `(K_x(R₀(n)) / (2 √n)) C²` with `R₀(n) = √(2 log (2 n / δ))`
(the high-probability bound on the readout weights) tends to `0`. -/
private lemma tendsto_testLinearizationRate {d : ℕ} (x : Fin d → ℝ) (C₁ C₂ C : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, x j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) /
        Real.sqrt (n : ℝ)) / 2 * C ^ 2) atTop (𝓝 0) := by
  have h := ((tendsto_jacobianLipschitzScale (fun _ : Fin 1 => x) C₁ C₂ hδ 0).div_const 2).mul_const
    (C ^ 2)
  simpa using h

/-- **Linearization error at a test input, in probability on `[0, T]`.** For any test input `x`
(scaled like the training inputs by `1 / √d`), the probability that the network output at `x`
differs from its initialization linearization `f(x; θ(0)) + ⟪∇f(x; θ(0)), θ(t) - θ(0)⟫` by more than
`ε₀` somewhere on `[0, T]` tends to zero. The flow is still trained on the training set; only the
readout weights at initialization and the displacement radius enter the deterministic bound
`abs_netFromParams_sub_linearization_le`. -/
theorem tendsto_measure_test_linearization_error_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (x : Fin d → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
          ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0), θ n p t - θ n p 0⟫|})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc (0 : ℝ) T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
        netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
      ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0),
        θ n p t - θ n p 0⟫|) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, C, _, _, _, _, N, -, -, -, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  refine ⟨_, tendsto_testLinearizationRate (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) C₁ C₂ C
    (lt_min one_pos (by positivity : 0 < c / 8)),
    (Filter.eventually_ge_atTop (max N 1)).mono fun n hn' => ?_⟩
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · obtain ⟨-, hp2, -, hall⟩ := hEp p hp
    have hdisp := (hall (θ n p) hflow t ht).2.2.2
    rw [hflow.init]
    exact abs_netFromParams_sub_linearization_le_of_disp hact hn0
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j)
      (fun i => by simpa [unpackA_packParams] using hp2 i) hdisp

/-- **Linearization error at a test input, in probability on `[0, ∞)` from a positive gap.**
The test-point counterpart of `tendsto_measure_linearization_error_global_positive_gap`: for every
test input `x` and `ε₀ > 0`,
`P(sup_{t ≥ 0} |f(x; θ(t)) - f(x; θ(0)) - ⟪∇f(x; θ(0)), θ(t) - θ(0)⟫| > ε₀) → 0`. -/
theorem tendsto_measure_test_linearization_error_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (x : Fin d → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
          ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0), θ n p t - θ n p 0⟫|})
      Filter.atTop (nhds 0) := by
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici (0 : ℝ))
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    (fun n p t => |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
        netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) -
      ⟪gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0),
        θ n p t - θ n p 0⟫|) hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, _, _, N, C, M, R, -, -, -, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  refine ⟨_, tendsto_testLinearizationRate (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) C₁ C₂ C
    (lt_min one_pos (by positivity : 0 < c / 8)),
    (Filter.eventually_ge_atTop (max N 1)).mono fun n hn' => ?_⟩
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  refine ⟨E, hEm, ?_, fun p hp hflow t ht => ?_⟩
  · rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  · obtain ⟨-, -, hall, hp2⟩ := hEp p hp
    have hdisp := ((hall (θ n p) hflow).2 t ht).1
    rw [hflow.init]
    exact abs_netFromParams_sub_linearization_le_of_disp hact hn0
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j)
      (fun i => by simpa [unpackA_packParams] using hp2 i) hdisp

/-- Scaling the extended dataset `(X, x)` by `1 / √d` scales both parts. -/
private lemma scaled_snoc {m d : ℕ} (X : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
      Fin d → ℝ) α j) =
    Fin.snoc (α := fun _ => Fin d → ℝ) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) := by
  funext α
  refine Fin.lastCases ?_ (fun i => ?_) α <;> simp

/-- Deterministic cross-kernel drift bound. Let `k_θ(x) = J(θ) ∇f(x; θ)` be the train-test
cross-kernel vector (`k_θ(x)_α = ⟪∇f(x; θ), ∇f(X α; θ)⟫`). If the readout weights of `θ₀` are
bounded by `R`, `‖θ - θ₀‖ ≤ Cd`, `‖J(θ₀)‖ ≤ M`, `‖J(θ) - J(θ₀)‖ ≤ jr` and `‖∇f(x; θ₀)‖ ≤ G₀`, then
`‖k_θ(x) - k_{θ₀}(x)‖ ≤ jr G₀ + (M + jr) (K_x / √n) Cd`, where `K_x` is the tangent-feature
Lipschitz scale of `norm_gradParams_sub_le`. -/
private lemma norm_crossKernel_sub_le {φ : ℝ → ℝ} {C₁ C₂ : ℝ} (hact : SmoothActivation φ C₁ C₂)
    {n d m : ℕ} (hn : 0 < n) (Xs : Fin m → Fin d → ℝ) (xs : Fin d → ℝ)
    {θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n))} {R Cd M jr G₀ : ℝ}
    (hR : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) (hΔ : ‖θ - θ₀‖ ≤ Cd)
    (hJ₀ : ‖outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ M)
    (hJ : ‖outputJacobian (netFromParams φ n d) Xs θ -
      outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jr)
    (hg₀ : ‖gradParams φ n d xs θ₀‖ ≤ G₀) :
    ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ).ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ
        (gradParams φ n d xs θ₀).ofLp)‖ ≤
      jr * G₀ + (M + jr) * ((Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) / Real.sqrt (n : ℝ)) * Cd) := by
  obtain ⟨hC₁, hC₂, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR ⟨0, hn⟩)
  have hg := norm_gradParams_sub_le φ hact.differentiable n d hn xs θ₀ θ C₁ C₂ R hC₁ hC₂ hR0
    hφ_lip hact.deriv_bdd hact.deriv_lip hR
  set Lx : ℝ := Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 +
    3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) / Real.sqrt (n : ℝ) with hLx
  have hLx0 : 0 ≤ Lx := by positivity
  have hjr0 : 0 ≤ jr := (norm_nonneg _).trans hJ
  have hsplit : (WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ).ofLp) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ
        (gradParams φ n d xs θ₀).ofLp) =
      WithLp.toLp 2 ((outputJacobian (netFromParams φ n d) Xs θ -
        outputJacobian (netFromParams φ n d) Xs θ₀) *ᵥ (gradParams φ n d xs θ₀).ofLp) +
      WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ *ᵥ
        (gradParams φ n d xs θ - gradParams φ n d xs θ₀).ofLp) := by
    ext i
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (mulVec_frobenius_norm_le _ _).trans (mul_le_mul hJ hg₀ (norm_nonneg _) hjr0)
  · refine (mulVec_frobenius_norm_le _ _).trans ?_
    have hJθ : ‖outputJacobian (netFromParams φ n d) Xs θ‖ ≤ M + jr := by
      have := norm_sub_le_norm_sub_add_norm_sub (outputJacobian (netFromParams φ n d) Xs θ)
        (outputJacobian (netFromParams φ n d) Xs θ₀) 0
      simp only [sub_zero] at this
      linarith
    exact mul_le_mul hJθ (hg.trans (mul_le_mul_of_nonneg_left hΔ hLx0)) (norm_nonneg _)
      ((norm_nonneg _).trans hJθ)

open Filter Topology in
/-- The tangent-feature Lipschitz scale `K_x(R₀(n)) / √n` at a test input, with the high-probability
readout bound `R₀(n) = √(2 log (2 n / δ))`, tends to `0`. -/
private lemma tendsto_testGradLipschitzRate {d : ℕ} (x : Fin d → ℝ) (C₁ C₂ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
        (∑ j : Fin d, x j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) /
        Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  simpa using tendsto_jacobianLipschitzScale (fun _ : Fin 1 => x) C₁ C₂ hδ 0

/-- **Initialization concentration of the train-test cross-kernel.** For a test input `x`, the
empirical cross-kernel vector `α ↦ ⟪∇f(x; θ₀), ∇f(X α; θ₀)⟫ = (J(θ₀) ∇f(x; θ₀))_α` converges in
probability to `α ↦ limitingFullNTKMatrix φ (X, x) (last, α)`, the train-test entries of the
limiting NTK of the extended dataset. No separate cross-kernel law of large numbers is needed: the
cross-kernel is a row of the empirical NTK Gram matrix of the extended dataset `(X, x)`
(`empiricalNTKMatrix_snoc_last`), whose convergence is
`tendsto_initMeasure_empiricalNTKMatrix_ge_eps`. -/
theorem tendsto_initMeasure_crossKernel_ge_eps
    {d m : ℕ} (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) (X : Fin m → Fin d → ℝ) (x : Fin d → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => (initMeasure n d) {p | ε ≤
        ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (fun α : Fin m => limitingFullNTKMatrix φ
            (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ)
              (Fin.last m) (Fin.castSucc α))‖})
      Filter.atTop (nhds 0) := by
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU' (fun n => bot_le)
    (fun n => measure_mono fun p hp => ?_)
  rw [Set.mem_ofPred_eq] at hp ⊢
  refine hp.trans (le_of_eq_of_le ?_ (norm_row_castSucc_le
    (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j)
      (packParams p.1 p.2) - limitingFullNTKMatrix φ X') (Fin.last m)).1)
  congr 1
  ext α
  have hsn : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
      (Fin.snoc (α := fun _ => Fin d → ℝ) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
  simp only [PiLp.sub_apply, Matrix.sub_apply]
  rw [hsn, ← tangentFeature_netFromParams_of_differentiable φ hφ n d,
    outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]

/-- **Cross-kernel freezing in probability on `[0, T]`.** For a test input `x`, the train-test
cross-kernel vector `k_θ(x) = J(θ) ∇_θ f(x; θ)` (entries `⟪∇f(x; θ), ∇f(X α; θ)⟫`) stays within `ε₀`
of its initial value on `[0, T]` with probability tending to one. No spectral gap is assumed. The
proof splits `k_{θ(t)} - k_{θ(0)} = (J(θ(t)) - J(θ(0))) ∇f(x; θ(0)) + J(θ(t)) (∇f(x; θ(t)) -
∇f(x; θ(0)))` and uses the Jacobian drift of the finite-horizon event, the Lipschitz bound of the
tangent feature at `x` (`norm_gradParams_sub_le`), and concentration of `‖∇f(x; θ(0))‖² = K'(x, x)`
from the extended dataset. -/
theorem tendsto_measure_crossKernel_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) with hXs
  set xs : Fin d → ℝ := (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) one_pos
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Icc 0 T)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t => ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖)
    hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨R, C, M, _, jacRate, _, N, -, -, hjr, -, h⟩ :=
    exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y T hT
      (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity)) (min_le_left _ _)
      (by positivity)
  set δ : ℝ := min 1 (c / 8) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hLx := tendsto_testGradLipschitzRate xs C₁ C₂ hδpos
  refine ⟨fun n => jacRate n * G₀ + (M + jacRate n) *
    (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
      (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
      Real.sqrt (n : ℝ) * C), ?_, ?_⟩
  · simpa using (hjr.mul_const G₀).add ((hjr.const_add M).mul (hLx.mul_const C))
  filter_upwards [Filter.eventually_ge_atTop (max N 1),
    hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn' hUn'
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | 1 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
      Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
  have hUm' : MeasurableSet U' :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' 1
  have hU'r : (initMeasure n d).real U' ≤ c / 4 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
        (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
    simp only [hU'def, ← this]
    exact hUn'.le
  refine ⟨E ∩ U'ᶜ, hEm.inter hUm'.compl, ?_, ?_⟩
  · have hEc : (initMeasure n d).real Eᶜ ≤ 2 * δ + c / 4 := by
      rw [probReal_compl_eq_one_sub hEm]
      linarith
    have h2 := measureReal_compl_inter_le (initMeasure n d) E U'ᶜ
    rw [compl_compl] at h2
    have := min_le_right 1 (c / 8)
    have h3 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
    linarith
  · rintro p ⟨hpE, hpU'⟩ hflow t ht
    obtain ⟨-, hp2, hJ0, hall⟩ := hEp p hpE
    have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
        Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < 1 := not_le.1 hpU'
    have hrow := norm_row_castSucc_le
      (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L') (Fin.last m)
    have hg0 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ≤ G₀ := by
      rw [hG₀]
      refine Real.le_sqrt_of_sq_le ?_
      have h1 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ^ 2 = empiricalNTKMatrix
          (netFromParams φ n d)
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ)
          (packParams p.1 p.2) (Fin.last m) (Fin.last m) := by
        rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2,
          tangentFeature_netFromParams_of_differentiable φ hφ, real_inner_self_eq_norm_sq]
      have h2 := hrow.2
      rw [Matrix.sub_apply] at h2
      have h3 := (abs_le.1 (h2.trans hpU2.le)).2
      have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
      rw [h1]
      linarith
    have hreadout : ∀ i : Fin n, |unpackA (packParams p.1 p.2) i| ≤
        Real.sqrt (2 * Real.log (2 * n / δ)) := fun i => by
      simpa [unpackA_packParams] using hp2 i
    have hall' := hall (θ n p) hflow t ht
    have := norm_crossKernel_sub_le hact hn0 Xs xs hreadout hall'.2.2.2 hJ0 hall'.2.1 hg0
    rw [hflow.init]
    exact this

/-- **Cross-kernel freezing in probability on `[0, ∞)` from a positive limiting gap.** The
counterpart of `tendsto_measure_crossKernel_drift_finite_horizon` for all times `t ≥ 0`: if
`K_∞ ≥ lambda_inf • 1` with `lambda_inf > 0`, the train-test cross-kernel vector
`k_θ(x) = J(θ) ∇_θ f(x; θ)` stays within `ε₀` of its initial value for *all* `t ≥ 0` with
probability tending to one. The proof is the same splitting
`k_{θ(t)} - k_{θ(0)} = (J(θ(t)) - J(θ(0))) ∇f(x; θ(0)) + J(θ(t)) (∇f(x; θ(t)) - ∇f(x; θ(0)))`
and uses the Jacobian drift of the finite-horizon event, the Lipschitz bound of the
tangent feature at `x` (`norm_gradParams_sub_le`), and concentration of `‖∇f(x; θ(0))‖² = K'(x, x)`
from the extended dataset. -/
theorem tendsto_measure_crossKernel_drift_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ),
        ε₀ < ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) with hXs
  set xs : Fin d → ℝ := (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  have hφ := hact.differentiable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hφ
  obtain ⟨-, hL2mul, -, hdL2mul⟩ := activation_memLp_two hact (d := d)
  set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
  have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ hderiv_meas X'
    (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) one_pos
  refine tendsto_measure_exists_gt_of_good_events (fun n => initMeasure n d) (Set.Ici 0)
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t => ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t)).ofLp) :
              EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (outputJacobian (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0) *ᵥ
            (gradParams φ n d
              (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0)).ofLp)‖)
    hθ_flow (fun c hc => ?_) hε₀
  obtain ⟨_, jacRate, _, N, C, M, R, -, hjr, -, -, -, -, -, h⟩ :=
    exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lambda_inf
      hlambda_inf hK_gap (δ := min 1 (c / 8)) (ε := c / 8) (lt_min one_pos (by positivity))
      (min_le_left _ _) (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ)
      (κ := 0) (fun n _ => by simp)
  set δ : ℝ := min 1 (c / 8) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hLx := tendsto_testGradLipschitzRate xs C₁ C₂ hδpos
  refine ⟨fun n => jacRate n * G₀ + (M + jacRate n) *
    (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
      (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
      Real.sqrt (n : ℝ) * C), ?_, ?_⟩
  · simpa using (hjr.mul_const G₀).add ((hjr.const_add M).mul (hLx.mul_const C))
  filter_upwards [Filter.eventually_ge_atTop (max N 1),
    hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn' hUn'
  have hn : n ≥ N := (le_max_left _ _).trans hn'
  have hn0 : 0 < n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn')
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | 1 ≤
    ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
      Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
  have hUm' : MeasurableSet U' :=
    measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' 1
  have hU'r : (initMeasure n d).real U' ≤ c / 4 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
        (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
    simp only [hU'def, ← this]
    exact hUn'.le
  refine ⟨E ∩ U'ᶜ, hEm.inter hUm'.compl, ?_, ?_⟩
  · have hEc : (initMeasure n d).real Eᶜ ≤ 2 * δ + 2 * (c / 8) := by
      rw [probReal_compl_eq_one_sub hEm]
      linarith
    have h2 := measureReal_compl_inter_le (initMeasure n d) E U'ᶜ
    rw [compl_compl] at h2
    have := min_le_right 1 (c / 8)
    have h3 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
    linarith
  · rintro p ⟨hpE, hpU'⟩ hflow t ht
    obtain ⟨-, hJ0, hall, hp2⟩ := hEp p hpE
    have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
        Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < 1 := not_le.1 hpU'
    have hrow := norm_row_castSucc_le
      (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L') (Fin.last m)
    have hg0 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ≤ G₀ := by
      rw [hG₀]
      refine Real.le_sqrt_of_sq_le ?_
      have h1 : ‖gradParams φ n d xs (packParams p.1 p.2)‖ ^ 2 = empiricalNTKMatrix
          (netFromParams φ n d)
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ)
          (packParams p.1 p.2) (Fin.last m) (Fin.last m) := by
        rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2,
          tangentFeature_netFromParams_of_differentiable φ hφ, real_inner_self_eq_norm_sq]
      have h2 := hrow.2
      rw [Matrix.sub_apply] at h2
      have h3 := (abs_le.1 (h2.trans hpU2.le)).2
      have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
      rw [h1]
      linarith
    have hreadout : ∀ i : Fin n, |unpackA (packParams p.1 p.2) i| ≤
        Real.sqrt (2 * Real.log (2 * n / δ)) := fun i => by
      simpa [unpackA_packParams] using hp2 i
    have hall' := (hall (θ n p) hflow).2 t ht
    have := norm_crossKernel_sub_le hact hn0 Xs xs hreadout hall'.1 hJ0 hall'.2.2.2.1 hg0
    rw [hflow.init]
    exact this

/-- **Actual residual vs. frozen matrix-exponential residual, in probability.** If the trajectories
`θ n p` solve the gradient-flow ODE for almost every initialization, then at each fixed time `t ≥ 0`
the trained residual `r_n(t)` and the frozen residual `exp(-(t / m) K_∞) r_n(0)` are asymptotically
equal: for every `ε₀ > 0`, `initMeasure n d {ε₀ ≤ ‖r_n(t) - exp(-(t / m) K_∞) r_n(0)‖} → 0`
(outer probability, as for `tendsto_measure_kernel_drift_finite_horizon`). No spectral gap is
assumed. -/
theorem tendsto_measure_residual_sub_matrix_exp_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ε₀ ≤
        ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t) -
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)).ofLp) :
            EuclideanSpace ℝ (Fin m))‖})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨c, hc, hcκ⟩ := exists_pos_real_ofReal_le hκ
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hφ := hact.differentiable
  have hC₁_bdd := hact.deriv_bdd
  have hderiv_lip := hact.deriv_lip
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) :=
    fun α => hL2 (Xs α)
  have hdφ_out_L2 : ∀ α, MemLp (fun w => deriv φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) :=
    fun α => hdL2 (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⊙ Xs α) * φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => hL2mul (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⊙ Xs α) * deriv φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => hdL2mul (Xs α) (Xs β)
  have hK_inf : ∀ v : EuclideanSpace ℝ (Fin m),
      0 ≤ v.ofLp ⬝ᵥ (limitingFullNTKMatrix φ X *ᵥ v.ofLp) :=
    dotProduct_mulVec_nonneg_of_posSemidef
      (limitingFullNTKMatrix_posSemidef φ X hmeasφ hderiv_meas hφ_out_L2 hdφ_out_L2)
  obtain ⟨R, freezeRate, N, hR, hrate, h⟩ := exists_measurableSet_finite_horizon_kernel_freeze hm φ
    hact X y t ht (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity))
    (min_le_left _ _) (by positivity)
  -- Kernel error budget `e`, chosen so that `(1 / m) * (2 e) * R * t < ε₀`.
  set cst : ℝ := (m : ℝ)⁻¹ * R * t with hcst
  have hcst_nonneg : 0 ≤ cst := by positivity
  set e : ℝ := ε₀ / (2 * (cst + 1)) with he_def
  have he : 0 < e := by positivity
  have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X hφ_L2 hdφ_L2
    he
  filter_upwards [Filter.eventually_ge_atTop N, hrate.eventually (gt_mem_nhds he),
    hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
    with n hn hfr hUn
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  have hEc : (initMeasure n d).real Eᶜ ≤ c / 2 := by
    rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  have hnull : (initMeasure n d) {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y)
      (packParams p.1 p.2) (θ n p)} = 0 := ae_iff.1 (hθ_flow n)
  calc (initMeasure n d) {p | ε₀ ≤ ‖trainingResidual (netFromParams φ n d) Xs y (θ n p t) -
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)).ofLp) :
            EuclideanSpace ℝ (Fin m))‖}
      ≤ (initMeasure n d) ((Eᶜ ∪ {p | e ≤ ‖empiricalNTKMatrix (netFromParams φ n d) Xs
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖}) ∪
          {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
            (θ n p)}) := by
        refine measure_mono fun p hp => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not,
          not_le] at hcon
        obtain ⟨⟨hpE, hpU⟩, hflow⟩ := hcon
        obtain ⟨hres0, hEK⟩ := hEp p hpE
        have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
            (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
          (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
            fun i => hφ.differentiableAt).differentiableAt
        have hKb : ∀ u ∈ Set.Icc (0 : ℝ) t,
            ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u) -
              limitingFullNTKMatrix φ X‖ ≤ 2 * e := by
          intro u hu
          have h1 := hEK (θ n p) hflow u hu
          have h2 := norm_sub_le_norm_sub_add_norm_sub
            (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u))
            (empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2))
            (limitingFullNTKMatrix φ X)
          linarith
        have happrox := residual_sub_matrix_exp_le
          (fun u => empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p u))
          (limitingFullNTKMatrix φ X)
          (fun u => trainingResidual (netFromParams φ n d) Xs y (θ n p u)) (T := t) ht hm'
          (continuousOn_trainingResidual_comp (netFromParams φ n d) Xs y (s := Set.Icc 0 t)
            (hflow.continuousOn.mono Set.Icc_subset_Ici_self) fun u _ => hdiff u)
          (fun u hu => gradient_flow_residual_vector_ode (netFromParams φ n d) Xs y u
            (hflow.ode u hu.1) (hdiff u))
          (fun u _ v => dotProduct_mulVec_nonneg_of_posSemidef
            (empiricalNTKMatrix_posSemidef _ _ _) v) hK_inf hKb t ⟨ht, le_rfl⟩
        simp only [hflow.init] at happrox
        have hbound : (m : ℝ)⁻¹ * (2 * e * ‖trainingResidual (netFromParams φ n d) Xs y
            (packParams p.1 p.2)‖) * t ≤ 2 * e * cst := by
          rw [hcst]
          have : 0 ≤ e := he.le
          calc (m : ℝ)⁻¹ * (2 * e * ‖trainingResidual (netFromParams φ n d) Xs y
                (packParams p.1 p.2)‖) * t ≤ (m : ℝ)⁻¹ * (2 * e * R) * t := by gcongr
            _ = 2 * e * ((m : ℝ)⁻¹ * R * t) := by ring
        have hlt : 2 * e * cst < ε₀ := by
          rw [he_def]
          have hpos : 0 < cst + 1 := by linarith
          rw [show 2 * (ε₀ / (2 * (cst + 1))) * cst = ε₀ * (cst / (cst + 1)) by
            field_simp]
          have : cst / (cst + 1) < 1 := (div_lt_one hpos).2 (by linarith)
          nlinarith
        rw [Set.mem_ofPred_eq] at hp
        linarith [hp, happrox, hbound, hlt]
    _ ≤ (initMeasure n d) (Eᶜ ∪ {p | e ≤ ‖empiricalNTKMatrix (netFromParams φ n d) Xs
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖}) + 0 := by
        rw [← hnull]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 4) := by
        rw [add_zero]
        refine (measure_union_le _ _).trans (add_le_add ?_ hUn.le)
        exact measure_le_ofReal_of_measureReal_le _ hEc
    _ ≤ κ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hcκ

/-- **Fixed-time test prediction (finite horizon, no spectral gap).** Let `θ n p` be trajectories
solving the gradient-flow ODE for almost every initialization, let `K_∞ = limitingFullNTKMatrix φ X`
be invertible and `k_∞(x, X)_α` the train-test entry of the limiting NTK of the extended dataset
`(X, x)`. Then for every fixed `t ≥ 0`, test input `x` and `ε₀ > 0`, the probability that the
trained network output at `x` deviates from the kernel-regression prediction
`f₀(x) - a ⬝ᵥ (r₀ - exp(-(t / m) K_∞) r₀)`, `a = K_∞⁻¹ k_∞(x, X)`, `r₀ = f₀(X) - y`, by more than
`ε₀` tends to zero. Equivalently `f_t(x) ≈ f₀(x) + k_∞(x, X)ᵀ K_∞⁻¹ (I - exp(-(t / m) K_∞))
(y - f₀(X))`, the closed-form predictor of the source, where `f₀` is the (random) initial network.
The proof combines the Taylor bound at the test input, the Jacobian and kernel drift of the
finite-horizon lazy-training event, initialization concentration of the extended NTK Gram matrix
(whose last row is the train-test cross-kernel, so no separate cross-kernel concentration is
needed),
and the deterministic `abs_inner_displacement_add_frozenPrediction_le`. -/
theorem tendsto_measure_test_prediction_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKinv : IsUnit (limitingFullNTKMatrix φ X)) (t : ℝ) (ht : 0 ≤ t) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X) *ᵥ
                (trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp)|})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set xs : Fin d → ℝ := fun j => (Real.sqrt (d : ℝ))⁻¹ * x j with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  set kv : Fin m → ℝ := fun α => L' (Fin.last m) (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁, hC₂, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hK_inf : L.PosSemidef :=
    limitingFullNTKMatrix_posSemidef φ X hmeasφ hderiv_meas (fun α => hL2 (Xs α))
      (fun α => hdL2 (Xs α))
  have hLa : L *ᵥ (L⁻¹ *ᵥ kv) = kv := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hKinv),
      Matrix.one_mulVec]
  refine (tendsto_measure_exists_gt_of_eventually_good_events (fun n => initMeasure n d) {t}
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t' => |netFromParams φ n d xs (θ n p t') -
        netFromParams φ n d xs (θ n p 0) +
      (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
        NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|) hθ_flow
    (ε₀ := ε₀) (fun c hc => ?hev)).congr (fun n => ?heq)
  case heq =>
    congr 1
    ext p
    simp
  case hev =>
    -- the finite-horizon lazy-training event
    obtain ⟨R, C, _, freezeRate, jacRate, taylorRate, N, hR0, hfr, hjr, -, h⟩ :=
      exists_measurableSet_finite_horizon_lazy_training_event hm φ hact X y t ht
        (δ := min 1 (c / 8)) (ε := c / 4) (lt_min one_pos (by positivity)) (min_le_left _ _)
        (by positivity)
    set δ : ℝ := min 1 (c / 8) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    -- constants of the error budget
    set kn : ℝ := ‖(WithLp.toLp 2 kv : EuclideanSpace ℝ (Fin m))‖ with hkn
    set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
    set A₁ : ℝ := t * ((m : ℝ)⁻¹ * (G₀ * R)) with hA₁
    set A₂ : ℝ := t * ((m : ℝ)⁻¹ * (kn * ((m : ℝ)⁻¹ * R * t))) with hA₂
    set a₁ : ℝ := t * ((m : ℝ)⁻¹ * R) + A₂ with ha₁
    have hA₁0 : 0 ≤ A₁ := by positivity
    have hA₂0 : 0 ≤ A₂ := by positivity
    have ha₁0 : 0 ≤ a₁ := by positivity
    set e : ℝ := min 1 (ε₀ / (4 * (a₁ + 1))) with he_def
    have he : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hea : a₁ * e ≤ ε₀ / 4 := by
      have h1 : e ≤ ε₀ / (4 * (a₁ + 1)) := min_le_right _ _
      calc a₁ * e ≤ (a₁ + 1) * (ε₀ / (4 * (a₁ + 1))) :=
            mul_le_mul (by linarith) h1 he.le (by positivity)
        _ = ε₀ / 4 := by field_simp
    -- initialization concentration: training kernel and extended kernel
    have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
      (fun α β => hL2mul (Xs α) (Xs β)) (fun α β => hdL2mul (Xs α) (Xs β)) he
    have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ
      hderiv_meas X'
      (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) he
    have hτ := tendsto_testLinearizationRate xs C₁ C₂ C hδpos
    have hsmall : Filter.Tendsto (fun n => taylorRate n * 0 + 0) Filter.atTop (nhds 0) := by simp
    have hb : Filter.Tendsto (fun n : ℕ =>
        (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 *
        C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
        Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n) Filter.atTop
        (nhds 0) := by
      simpa using (hτ.add (hjr.const_mul A₁)).add (hfr.const_mul A₂)
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0,
      hb.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)),
      hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity))),
      hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
      with n hn hn0 hbn hUn hUn'
    obtain ⟨E, hEm, hE, hEp⟩ := h n hn
    set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖} with hUdef
    set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
    have hUm : MeasurableSet U :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs L e
    have hUm' : MeasurableSet U' :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' e
    have hUr : (initMeasure n d).real U ≤ c / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hUn.le
    have hU'r : (initMeasure n d).real U' ≤ c / 4 := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
      simp only [hU'def, ← this]
      exact hUn'.le
    refine ⟨(E ∩ Uᶜ) ∩ U'ᶜ, (hEm.inter hUm.compl).inter hUm'.compl, ?_, ?_⟩
    · have hEc : (initMeasure n d).real Eᶜ ≤ c / 4 + c / 4 := by
        rw [probReal_compl_eq_one_sub hEm]
        have := min_le_right 1 (c / 8)
        have h2 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
        linarith
      have := (measureReal_compl_inter_le (initMeasure n d) (E ∩ Uᶜ) U'ᶜ)
      have h2 := measureReal_compl_inter_le (initMeasure n d) E Uᶜ
      rw [compl_compl] at this h2
      linarith
    · rintro p ⟨⟨hpE, hpU⟩, hpU'⟩ hflow t' ht'
      have ht'eq : t' = t := ht'
      obtain ⟨hres0, hp2, -, hall⟩ := hEp p hpE
      have hpU1 : ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖ < e :=
        not_le.1 hpU
      have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
          Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < e := not_le.1 hpU'
      set θ₀ := packParams p.1 p.2 with hθ₀
      set g : EuclideanSpace ℝ (Fin (n * d + n)) :=
        tangentFeature (netFromParams φ n d) xs θ₀ with hg
      simp only [ht'eq, hflow.init]
      have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
          (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
        (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
          fun i => hφ.differentiableAt).differentiableAt
      have hallt := fun s (hs : s ∈ Set.Icc (0 : ℝ) t) => hall (θ n p) hflow s hs
      have hJ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖outputJacobian (netFromParams φ n d) Xs (θ n p s) -
          outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jacRate n := fun s hs => (hallt s hs).2.1
      have hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s) -
          L‖ ≤ freezeRate n + e := fun s hs => by
        have h1 := (hallt s hs).1
        have h2 := norm_sub_le_norm_sub_add_norm_sub
          (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s))
          (empiricalNTKMatrix (netFromParams φ n d) Xs θ₀) L
        linarith
      have hrow := norm_row_castSucc_le
        (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
          Fin (m + 1) → Fin d → ℝ) θ₀ - L') (Fin.last m)
      have hk : ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ g.ofLp) :
          EuclideanSpace ℝ (Fin m)) - WithLp.toLp 2 kv‖ ≤ e := by
        refine le_of_eq_of_le ?_ (hrow.1.trans hpU2.le)
        congr 1
        ext α
        simp only [PiLp.sub_apply, Matrix.sub_apply, hg, hkv, hL']
        rw [outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]
      have hgnorm : ‖g‖ ≤ G₀ := by
        rw [hG₀]
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : ‖g‖ ^ 2 = empiricalNTKMatrix (netFromParams φ n d)
            (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) θ₀
            (Fin.last m) (Fin.last m) := by
          rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2, hg,
            real_inner_self_eq_norm_sq]
        have h2 := hrow.2
        rw [Matrix.sub_apply] at h2
        have h3 := (abs_le.1 (h2.trans hpU2.le)).2
        have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
        rw [h1]
        linarith
      have hKa' := abs_inner_displacement_add_frozenPrediction_le (netFromParams φ n d) Xs y hm'
        hflow hdiff g ht L hK_inf (L⁻¹ *ᵥ kv) kv hLa hJ hK hk t ⟨ht, le_rfl⟩
      have hg' : gradParams φ n d xs θ₀ = g := (tangentFeature_netFromParams_of_differentiable φ
        hφ n d xs θ₀).symm
      have hreadout : ∀ i : Fin n, |unpackA θ₀ i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) :=
        fun i => by simpa [hθ₀, unpackA_packParams] using hp2 i
      have hdisp := (hallt t ⟨ht, le_rfl⟩).2.2.2
      have htay := abs_netFromParams_sub_linearization_le_of_disp hact hn0 xs hreadout hdisp
      rw [hg'] at htay
      -- collect the error budget
      have hjr0 : 0 ≤ jacRate n := (norm_nonneg _).trans (hJ 0 ⟨le_rfl, ht⟩)
      have hfr0 : 0 ≤ freezeRate n := (norm_nonneg _).trans (hallt 0 ⟨le_rfl, ht⟩).1
      have hr0 : ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤ R := hres0
      have hr00 := norm_nonneg (trainingResidual (netFromParams φ n d) Xs y θ₀)
      have hkn0 : 0 ≤ kn := norm_nonneg _
      have hbudget : t * ((m : ℝ)⁻¹ * (‖g‖ * jacRate n *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + e *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + kn *
            ((m : ℝ)⁻¹ * ((freezeRate n + e) *
              ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * t))) ≤
          A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
        have hgR : ‖g‖ * jacRate n * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤
            G₀ * jacRate n * R := by gcongr
        have hrR : kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * t) ≤
            kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * t) := by gcongr
        calc _ ≤ t * ((m : ℝ)⁻¹ * (G₀ * jacRate n * R + e * R +
              kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * t))) := by
              gcongr
          _ = A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
              rw [hA₁, hA₂, ha₁]; ring
      have hD : |netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ +
          (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
            NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
              (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)| ≤
          (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + (A₁ * jacRate n + A₂ * freezeRate n + a₁ * e) := by
        have hsplit : netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ +
            (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp) =
            (netFromParams φ n d xs (θ n p t) - netFromParams φ n d xs θ₀ - ⟪g, θ n p t - θ₀⟫) +
              (⟪g, θ n p t - θ₀⟫ + (L⁻¹ *ᵥ kv) ⬝ᵥ
                ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
                  NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                    (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)) := by ring
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add htay (hKa'.trans hbudget))
      have hbn' : (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n < ε₀ / 2 := hbn
      linarith

/-- **Test prediction uniformly in time under a positive limiting gap.** Let `K_∞ =
limitingFullNTKMatrix φ X` be positive definite (for instance under feature independence,
`limitingFullNTKMatrix_posDef_of_ae_independent`) and `θ n p` gradient-flow trajectories for almost
every initialization. For every test input `x` and `ε₀ > 0` the probability that, at *some* time
`t ≥ 0`, the trained output at `x` deviates from `f₀(x) - a ⬝ᵥ (r₀ - exp(-(t / m) K_∞) r₀)`,
`a = K_∞⁻¹ k_∞(x, X)`, by more than `ε₀` tends to zero. This is
`tendsto_measure_test_prediction_finite_horizon` with the horizon removed: the positive gap makes
the residual, the frozen residual and hence the error curve's derivative decay exponentially, which
controls the tail beyond a window
(`abs_inner_displacement_add_frozenPrediction_le_of_exp_decay`). -/
theorem tendsto_measure_test_prediction_global_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKpd : (limitingFullNTKMatrix φ X).PosDef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Ici (0 : ℝ), ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d)
                (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X) *ᵥ
                (trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp)|})
      Filter.atTop (nhds 0) := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set xs : Fin d → ℝ := fun j => (Real.sqrt (d : ℝ))⁻¹ * x j with hxs
  set X' : Fin (m + 1) → Fin d → ℝ :=
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) with hX'
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set L' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := limitingFullNTKMatrix φ X' with hL'
  set kv : Fin m → ℝ := fun α => L' (Fin.last m) (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁, hC₂, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd hact.deriv_lip hφ
  obtain ⟨hL2, hL2mul, hdL2, hdL2mul⟩ := activation_memLp_two hact (d := d)
  have hKinv : IsUnit L := hKpd.isUnit
  have hK_inf : L.PosSemidef := hKpd.posSemidef
  obtain ⟨lam, hlam, hgapK⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hKpd
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef L lam hgapK
  have hLa : L *ᵥ (L⁻¹ *ᵥ kv) = kv := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hKinv),
      Matrix.one_mulVec]
  refine (tendsto_measure_exists_gt_of_eventually_good_events (fun n => initMeasure n d)
    (Set.Ici (0 : ℝ))
    (fun n p => ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
      (θ n p)) (fun n p t' => |netFromParams φ n d xs (θ n p t') -
        netFromParams φ n d xs (θ n p 0) +
      (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
        NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|) hθ_flow
    (ε₀ := ε₀) (fun c hc => ?hev)).congr (fun n => ?heq)
  case heq => rfl
  case hev =>
    -- the global lazy-training event with a positive gap
    obtain ⟨freezeRate, jacRate, taylorRate, N, C, M, R, hfr, hjr, -, -, hC0, hM0, hR0, h⟩ :=
      exists_measurableSet_global_lazy_training_event_with_extra hm hd φ hact X y lam hlam hgapK
        (δ := min 1 (c / 8)) (ε := c / 8) (lt_min one_pos (by positivity)) (min_le_left _ _)
        (by positivity) (fun _ => Set.univ) (fun _ _ => MeasurableSet.univ) (κ := 0)
        (fun n _ => by simp)
    set δ : ℝ := min 1 (c / 8) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    set ν : ℝ := lam / (4 * (m : ℝ)) with hν
    have hν0 : 0 < ν := by positivity
    have hνlam : ν ≤ lam / m := by
      rw [hν]
      exact div_le_div_of_nonneg_left hlam.le hm' (by linarith)
    -- constants of the error budget
    set kn : ℝ := ‖(WithLp.toLp 2 kv : EuclideanSpace ℝ (Fin m))‖ with hkn
    set G₀ : ℝ := Real.sqrt (|L' (Fin.last m) (Fin.last m)| + 1) with hG₀
    set Bmax : ℝ := (m : ℝ)⁻¹ * R * (G₀ + 1 + 2 * kn) with hBmax
    have hBmax0 : 0 ≤ Bmax := by positivity
    obtain ⟨S, hS0, hStail⟩ : ∃ S : ℝ, 0 ≤ S ∧ Bmax / ν * Real.exp (-ν * S) ≤ ε₀ / 4 := by
      have htend : Filter.Tendsto (fun S : ℝ => Bmax / ν * Real.exp (-ν * S)) Filter.atTop
          (nhds 0) := by
        have := (Real.tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop hν0))).const_mul
            (Bmax / ν)
        simpa [Function.comp_def] using this
      obtain ⟨S, hS⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and
        (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 4 by positivity)))).exists
      exact ⟨S, hS.1, hS.2.le⟩
    set A₁ : ℝ := S * ((m : ℝ)⁻¹ * (G₀ * R)) with hA₁
    set A₂ : ℝ := S * ((m : ℝ)⁻¹ * (kn * ((m : ℝ)⁻¹ * R * S))) with hA₂
    set a₁ : ℝ := S * ((m : ℝ)⁻¹ * R) + A₂ with ha₁
    have hA₁0 : 0 ≤ A₁ := by positivity
    have hA₂0 : 0 ≤ A₂ := by positivity
    have ha₁0 : 0 ≤ a₁ := by positivity
    set e : ℝ := min 1 (ε₀ / (4 * (a₁ + 1))) with he_def
    have he : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hea : a₁ * e ≤ ε₀ / 4 := by
      have h1 : e ≤ ε₀ / (4 * (a₁ + 1)) := min_le_right _ _
      calc a₁ * e ≤ (a₁ + 1) * (ε₀ / (4 * (a₁ + 1))) :=
            mul_le_mul (by linarith) h1 he.le (by positivity)
        _ = ε₀ / 4 := by field_simp
    have hU := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
      (fun α β => hL2mul (Xs α) (Xs β)) (fun α β => hdL2mul (Xs α) (Xs β)) he
    have hU' := tendsto_initMeasure_empiricalNTKMatrix_ge_eps (Nat.succ_pos m) hd φ hφ
      hderiv_meas X' (fun α β => hL2mul _ _) (fun α β => hdL2mul _ _) he
    have hτ := tendsto_testLinearizationRate xs C₁ C₂ C hδpos
    have hb : Filter.Tendsto (fun n : ℕ =>
        (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 *
          C₂ ^ 2 * (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
          Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n) Filter.atTop
        (nhds 0) := by
      simpa using (hτ.add (hjr.const_mul A₁)).add (hfr.const_mul A₂)
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0,
      hb.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)),
      hjr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hU.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity))),
      hU'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < c / 4 by positivity)))]
      with n hn hn0 hbn hjn hUn hUn'
    obtain ⟨E, hEm, hE, hEp⟩ := h n hn
    set U : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖} with hUdef
    set U' : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) := {p | e ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
        Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖} with hU'def
    have hUm : MeasurableSet U :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas Xs L e
    have hUm' : MeasurableSet U' :=
      measurableSet_empiricalNTKMatrix_dist_ge φ hφ hderiv_meas _ L' e
    have hUr : (initMeasure n d).real U ≤ c / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hUn.le
    have hU'r : (initMeasure n d).real U' ≤ c / 4 := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      have : (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X' α j) =
          (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) := scaled_snoc X x
      simp only [hU'def, ← this]
      exact hUn'.le
    refine ⟨(E ∩ Uᶜ) ∩ U'ᶜ, (hEm.inter hUm.compl).inter hUm'.compl, ?_, ?_⟩
    · have hEc : (initMeasure n d).real Eᶜ ≤ c / 4 + c / 4 := by
        rw [probReal_compl_eq_one_sub hEm]
        have := min_le_right 1 (c / 8)
        have h2 : 2 * δ ≤ c / 4 := by rw [hδ]; linarith
        linarith
      have := (measureReal_compl_inter_le (initMeasure n d) (E ∩ Uᶜ) U'ᶜ)
      have h2 := measureReal_compl_inter_le (initMeasure n d) E Uᶜ
      rw [compl_compl] at this h2
      linarith
    · rintro p ⟨⟨hpE, hpU⟩, hpU'⟩ hflow t' ht'
      obtain ⟨-, -, hall, hp2⟩ := hEp p hpE
      obtain ⟨⟨horig, -⟩, hcert⟩ := hall (θ n p) hflow
      have hpU1 : ‖empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) - L‖ < e :=
        not_le.1 hpU
      have hpU2 : ‖empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ)
          Xs xs : Fin (m + 1) → Fin d → ℝ) (packParams p.1 p.2) - L'‖ < e := not_le.1 hpU'
      set θ₀ := packParams p.1 p.2 with hθ₀
      set g : EuclideanSpace ℝ (Fin (n * d + n)) :=
        tangentFeature (netFromParams φ n d) xs θ₀ with hg
      simp only [hflow.init]
      have hdiff : ∀ u : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
          (fun θ' => netFromParams φ n d (Xs β) θ') (θ n p u) := fun u β =>
        (hasFDerivAt_netFromParams φ n d (Xs β) (θ n p u)
          fun i => hφ.differentiableAt).differentiableAt
      have hJ : ∀ s : ℝ, 0 ≤ s → ‖outputJacobian (netFromParams φ n d) Xs (θ n p s) -
          outputJacobian (netFromParams φ n d) Xs θ₀‖ ≤ jacRate n := fun s hs =>
        (hcert s hs).2.2.2.1
      have hK : ∀ s ∈ Set.Icc (0 : ℝ) S, ‖empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s) -
          L‖ ≤ freezeRate n + e := fun s hs => by
        have h1 := (horig s hs.1).2.1
        have h2 := norm_sub_le_norm_sub_add_norm_sub
          (empiricalNTKMatrix (netFromParams φ n d) Xs (θ n p s))
          (empiricalNTKMatrix (netFromParams φ n d) Xs θ₀) L
        linarith
      have hrow := norm_row_castSucc_le
        (empiricalNTKMatrix (netFromParams φ n d) (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs :
          Fin (m + 1) → Fin d → ℝ) θ₀ - L') (Fin.last m)
      have hk : ‖(WithLp.toLp 2 (outputJacobian (netFromParams φ n d) Xs θ₀ *ᵥ g.ofLp) :
          EuclideanSpace ℝ (Fin m)) - WithLp.toLp 2 kv‖ ≤ e := by
        refine le_of_eq_of_le ?_ (hrow.1.trans hpU2.le)
        congr 1
        ext α
        simp only [PiLp.sub_apply, Matrix.sub_apply, hg, hkv, hL']
        rw [outputJacobian_mulVec_tangentFeature, (empiricalNTKMatrix_snoc_last _ _ _ _ α).1]
      have hgnorm : ‖g‖ ≤ G₀ := by
        rw [hG₀]
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : ‖g‖ ^ 2 = empiricalNTKMatrix (netFromParams φ n d)
            (Fin.snoc (α := fun _ => Fin d → ℝ) Xs xs : Fin (m + 1) → Fin d → ℝ) θ₀
            (Fin.last m) (Fin.last m) := by
          rw [(empiricalNTKMatrix_snoc_last _ _ _ _ (⟨0, hm⟩ : Fin m)).2, hg,
            real_inner_self_eq_norm_sq]
        have h2 := hrow.2
        rw [Matrix.sub_apply] at h2
        have h3 := (abs_le.1 (h2.trans hpU2.le)).2
        have h4 := le_abs_self (L' (Fin.last m) (Fin.last m))
        rw [h1]
        linarith
      have hres0 : ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤ R := by
        have := (hcert 0 le_rfl).2.2.1
        simpa [hflow.init, ν] using this
      have hglob := abs_inner_displacement_add_frozenPrediction_le_of_exp_decay
        (netFromParams φ n d) Xs y hm' hflow hdiff g hS0 L hK_inf hrr (L⁻¹ *ᵥ kv) kv hLa hν0
        hνlam hJ hK hk (fun s hs => by simpa [hν] using (horig s hs).2.2.1) t' ht'
      have hg' : gradParams φ n d xs θ₀ = g := (tangentFeature_netFromParams_of_differentiable φ
        hφ n d xs θ₀).symm
      have hreadout : ∀ i : Fin n, |unpackA θ₀ i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) :=
        fun i => by simpa [hθ₀, unpackA_packParams] using hp2 i
      have hdisp := (hcert t' ht').1
      have htay := abs_netFromParams_sub_linearization_le_of_disp hact hn0 xs hreadout hdisp
      rw [hg'] at htay
      have hjr0 : 0 ≤ jacRate n := (norm_nonneg _).trans (hJ 0 le_rfl)
      have hfr0 : 0 ≤ freezeRate n := (norm_nonneg _).trans (horig 0 le_rfl).2.1
      have hr00 := norm_nonneg (trainingResidual (netFromParams φ n d) Xs y θ₀)
      have hkn0 : 0 ≤ kn := norm_nonneg _
      have hg0 := norm_nonneg g
      have hbudget : S * ((m : ℝ)⁻¹ * (‖g‖ * jacRate n *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + e *
            ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ + kn *
            ((m : ℝ)⁻¹ * ((freezeRate n + e) *
              ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖) * S))) ≤
          A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
        have hgR : ‖g‖ * jacRate n * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ ≤
            G₀ * jacRate n * R := by gcongr
        calc _ ≤ S * ((m : ℝ)⁻¹ * (G₀ * jacRate n * R + e * R +
              kn * ((m : ℝ)⁻¹ * ((freezeRate n + e) * R) * S))) := by
              gcongr
          _ = A₁ * jacRate n + A₂ * freezeRate n + a₁ * e := by
              rw [hA₁, hA₂, ha₁]; ring
      have htail : ((m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
          (‖g‖ * jacRate n + e + 2 * kn)) / ν * Real.exp (-ν * S) ≤ ε₀ / 4 := by
        refine le_trans ?_ hStail
        have hexp : 0 ≤ Real.exp (-ν * S) := (Real.exp_pos _).le
        have : (m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
            (‖g‖ * jacRate n + e + 2 * kn) ≤ Bmax := by
          rw [hBmax]
          have h1 : ‖g‖ * jacRate n ≤ G₀ * 1 := by gcongr
          have hmi : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.2 hm'.le
          calc (m : ℝ)⁻¹ * ‖trainingResidual (netFromParams φ n d) Xs y θ₀‖ *
                (‖g‖ * jacRate n + e + 2 * kn)
              ≤ (m : ℝ)⁻¹ * R * (G₀ * 1 + 1 + 2 * kn) := by gcongr
            _ = _ := by ring
        gcongr
      have hD : |netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ +
          (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
            NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
              (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)| ≤
          (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 +
            ((A₁ * jacRate n + A₂ * freezeRate n + a₁ * e) + ε₀ / 4) := by
        have hsplit : netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ +
            (L⁻¹ *ᵥ kv) ⬝ᵥ ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
              NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp) =
            (netFromParams φ n d xs (θ n p t') - netFromParams φ n d xs θ₀ - ⟪g, θ n p t' - θ₀⟫) +
              (⟪g, θ n p t' - θ₀⟫ + (L⁻¹ *ᵥ kv) ⬝ᵥ
                ((trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp -
                  NormedSpace.exp (-(t' / (m : ℝ)) • L) *ᵥ
                    (trainingResidual (netFromParams φ n d) Xs y θ₀).ofLp)) := by ring
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add htay
          (hglob.trans (add_le_add hbudget htail)))
      have hbn' : (Real.sqrt (2 * Real.sqrt (2 * Real.log (2 * n / δ)) ^ 2 * C₂ ^ 2 *
            (∑ j : Fin d, xs j ^ 2) ^ 2 + 3 * C₁ ^ 2 * (∑ j : Fin d, xs j ^ 2)) /
            Real.sqrt (n : ℝ)) / 2 * C ^ 2 + A₁ * jacRate n + A₂ * freezeRate n < ε₀ / 2 := hbn
      linarith

/-- **Kernel interpolation at a test point (ridgeless kernel regression).** Under the hypotheses of
`tendsto_measure_test_prediction_global_positive_gap`, the trained network converges, first as the
width grows and then as time grows, to the ridgeless kernel-regression interpolant: for every
`ε₀, c > 0` there is a time `T₀` such that for all large `n`, with probability at least `1 - c`,
`|f_t(x) - (f₀(x) + k_∞(x, X)ᵀ K_∞⁻¹ (y - f₀(X)))| ≤ ε₀` simultaneously for all `t ≥ T₀`. Here
`a ⬝ᵥ r₀ = -k_∞ᵀ K_∞⁻¹ (y - f₀(X))` with `a = K_∞⁻¹ k_∞` and `r₀ = f₀(X) - y`. (This is
zero-ridge regression, i.e. minimum-norm interpolation, not positive-ridge kernel ridge regression;
for the frozen empirical features it is the minimum-norm solution of `affine_minNorm_pythagoras`.)
The time `T₀` depends on `ε₀`, `c` and the tightness radius of the initial residual, not on `n`. -/
theorem test_prediction_kernel_interpolation_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hKpd : (limitingFullNTKMatrix φ X).PosDef) (x : Fin d → ℝ)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ c : ℝ} (hε₀ : 0 < ε₀) (hc : 0 < c) :
    ∃ T₀ : ℝ, ∀ᶠ n in Filter.atTop, (initMeasure n d) {p | ∃ t ∈ Set.Ici T₀, ε₀ <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          ((limitingFullNTKMatrix φ X)⁻¹ *ᵥ (fun α : Fin m =>
            limitingFullNTKMatrix φ (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) →
              Fin d → ℝ) (Fin.last m) (Fin.castSucc α))) ⬝ᵥ
            (trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)).ofLp|} ≤
      ENNReal.ofReal c := by
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  set L : Matrix (Fin m) (Fin m) ℝ := limitingFullNTKMatrix φ X with hL
  set kv : Fin m → ℝ := fun α => limitingFullNTKMatrix φ
    (Fin.snoc (α := fun _ => Fin d → ℝ) X x : Fin (m + 1) → Fin d → ℝ) (Fin.last m)
      (Fin.castSucc α) with hkv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hL2, -, -, -⟩ := activation_memLp_two hact (d := d)
  obtain ⟨lam, hlam, hgapK⟩ := exists_pos_sub_smul_one_posSemidef_of_posDef hKpd
  have hrr := rayleigh_lower_bound_of_sub_smul_posSemidef L lam hgapK
  -- tightness of the initial residual
  obtain ⟨R₁, hR₁0, hR₁⟩ := exists_initial_residual_radius φ X y hmeasφ (fun α => hL2 (Xs α))
    (ε := ENNReal.ofReal (c / 2)) (ENNReal.ofReal_pos.2 (by positivity))
  set an : ℝ := ‖(WithLp.toLp 2 (L⁻¹ *ᵥ kv) : EuclideanSpace ℝ (Fin m))‖ with han
  have han0 : 0 ≤ an := norm_nonneg _
  -- a time after which the frozen residual is negligible
  obtain ⟨T₀, hT₀0, hT₀⟩ : ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      an * R₁ * Real.exp (-(lam / (m : ℝ)) * T₀) ≤ ε₀ / 2 := by
    have htend : Filter.Tendsto (fun T : ℝ => an * R₁ * Real.exp (-(lam / (m : ℝ)) * T))
        Filter.atTop (nhds 0) := by
      have := (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_id.const_mul_atTop (show 0 < lam / (m : ℝ) by positivity)))).const_mul
          (an * R₁)
      simpa [Function.comp_def] using this
    obtain ⟨T, hT⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and
      (htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε₀ / 2 by positivity)))).exists
    exact ⟨T, hT.1, hT.2.le⟩
  refine ⟨T₀, ?_⟩
  have hglob := tendsto_measure_test_prediction_global_positive_gap hm hd φ hact X y hKpd x θ
    hθ_flow (ε₀ := ε₀ / 2) (by positivity)
  filter_upwards [hglob.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2
    (show 0 < c / 2 by positivity)))] with n hn
  have hnull : (initMeasure n d) {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y)
      (packParams p.1 p.2) (θ n p)} = 0 := ae_iff.1 (hθ_flow n)
  calc _ ≤ (initMeasure n d) (({p | ∃ t ∈ Set.Ici (0 : ℝ), ε₀ / 2 <
        |netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
          netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p 0) +
          (L⁻¹ *ᵥ kv) ⬝ᵥ
            ((trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp -
              NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ
                (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)).ofLp)|} ∪
        {p | R₁ < ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖}) ∪
        {p | ¬ ForwardGFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
          (θ n p)}) := by
        refine measure_mono fun p hp => ?_
        obtain ⟨t, ht, hgt⟩ := hp
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt,
          not_not] at hcon
        obtain ⟨⟨h1, h2⟩, hflow⟩ := hcon
        have h1t := h1 t (Set.mem_Ici.2 (hT₀0.trans ht))
        have hinit : θ n p 0 = packParams p.1 p.2 := hflow.init
        have hρ := matrix_exp_residual_decay L
          (trainingResidual (netFromParams φ n d) Xs y (θ n p 0)) lam hrr hm' t (hT₀0.trans ht)
        rw [hinit] at h1t hρ hgt
        set r₀ := trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2) with hr₀
        set ρv : Fin m → ℝ := NormedSpace.exp (-(t / (m : ℝ)) • L) *ᵥ r₀.ofLp with hρv
        have hdot : |(L⁻¹ *ᵥ kv) ⬝ᵥ ρv| ≤ ε₀ / 2 := by
          refine (abs_dotProduct_le_norm_mul_norm _ _).trans ?_
          have hρ' : ‖(WithLp.toLp 2 ρv : EuclideanSpace ℝ (Fin m))‖ ≤ R₁ *
              Real.exp (-(lam / (m : ℝ)) * T₀) := by
            refine hρ.trans ?_
            have hexp : Real.exp (-(lam / (m : ℝ)) * t) ≤ Real.exp (-(lam / (m : ℝ)) * T₀) :=
              Real.exp_le_exp.2 (by nlinarith [show 0 < lam / (m : ℝ) by positivity, ht.out])
            exact mul_le_mul h2 hexp (Real.exp_pos _).le hR₁0
          calc _ ≤ an * (R₁ * Real.exp (-(lam / (m : ℝ)) * T₀)) :=
                mul_le_mul_of_nonneg_left hρ' han0
            _ = an * R₁ * Real.exp (-(lam / (m : ℝ)) * T₀) := by ring
            _ ≤ ε₀ / 2 := hT₀
        have hsplit : netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
            netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2) +
            (L⁻¹ *ᵥ kv) ⬝ᵥ r₀.ofLp =
            (netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (θ n p t) -
              netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) (packParams p.1 p.2) +
              (L⁻¹ *ᵥ kv) ⬝ᵥ (r₀.ofLp - ρv)) + (L⁻¹ *ᵥ kv) ⬝ᵥ ρv := by
          rw [dotProduct_sub]; ring
        rw [hsplit] at hgt
        have := (abs_add_le _ _).trans (add_le_add h1t hdot)
        linarith
    _ ≤ ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) + 0 := by
        rw [← hnull]
        refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add hn.le (hR₁ n))) le_rfl)
    _ = ENNReal.ofReal c := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The residual `θ ↦ r(θ)` of a differentiable-activation two-layer network is continuous in the
packed parameters. -/
private lemma continuous_trainingResidual_netFromParams {m : ℕ} (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (n d : ℕ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      trainingResidual (netFromParams φ n d) X y θ) := by
  have hnet : ∀ x : Fin d → ℝ, Continuous (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      netFromParams φ n d x θ) := fun x =>
    continuous_iff_continuousAt.2 fun θ =>
      (hasFDerivAt_netFromParams φ n d x θ fun i => hφ.differentiableAt).continuousAt
  exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => hnet (X α))).sub
    continuous_const

/-- **Fixed-time residual limit (no spectral gap).** Let `θ n p` be trajectories that are
measurable in the initialization and solve the gradient-flow ODE almost everywhere. Then for every
fixed `t ≥ 0` the trained residual on the paper's scaled dataset converges in distribution to the
frozen-kernel prediction `exp(-(t / m) K_∞) (G - y)` with `G ~ 𝒩(0, Φ^{(∞)})`. This is the residual
half of the finite-horizon target: the initial residual weak limit is pushed through the matrix
exponential and compared with the actual residual by
`tendsto_measure_residual_sub_matrix_exp_finite_horizon`. -/
theorem tendstoInDistribution_trainingResidual_matrix_exp
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        trainingResidual (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t))
      Filter.atTop
      (fun G : EuclideanSpace ℝ (Fin m) =>
        (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
          (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
      (fun n => initMeasure n d)
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have hφ := hact.differentiable
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin m) =>
      (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
        v.ofLp) : EuclideanSpace ℝ (Fin m))) :=
    (Matrix.toEuclideanLin (NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X))
      ).continuous_of_finiteDimensional
  have hX := tendstoInDistribution_initial_trainingResidual φ X y hmeasφ fun α =>
    (activation_memLp_two hact (d := d)).1 _
  exact tendstoInDistribution_of_tendsto_measure_norm_sub _ _ _
    (hX.continuous_comp (g := fun v : EuclideanSpace ℝ (Fin m) =>
      (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
        v.ofLp) : EuclideanSpace ℝ (Fin m))) hcont)
    (fun ε₀ hε₀ => tendsto_measure_residual_sub_matrix_exp_finite_horizon hm hd φ hact X y t ht θ
      hθ_flow hε₀)
    fun n => (continuous_trainingResidual_netFromParams φ hφ n d _ y).measurable.comp_aemeasurable
      (hθ_meas n t)

/-- **Fixed-time prediction limit (no spectral gap).** The network predictions on the scaled
dataset converge in distribution to `y + exp(-(t / m) K_∞) (G - y)`; see
`tendstoInDistribution_trainingResidual_matrix_exp`. -/
theorem tendstoInDistribution_trainingOutputs_matrix_exp
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    TendstoInDistribution
      (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
        trainingOutputs (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t))
      Filter.atTop
      (fun G : EuclideanSpace ℝ (Fin m) =>
        y + (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
          (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
      (fun n => initMeasure n d)
      (multivariateGaussian 0
        (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j))) := by
  have h := (tendstoInDistribution_trainingResidual_matrix_exp hm hd φ hact X y t ht θ hθ_meas
    hθ_flow).continuous_comp (g := fun v : EuclideanSpace ℝ (Fin m) => y + v) (by fun_prop)
  convert h using 3 with n p <;> first | rfl | simp [trainingResidual]
end FiniteHorizonLimit

section GlobalPositiveGapLimit

/-!
#### Target Theorem 2: Global Positive-Gap Lazy Training Limit (Phase 0 Target)

**Status.** Proved as `global_positive_gap_lazy_training_limit` (any family solving the ODE almost
everywhere) and `gradientFlow_global_positive_gap_lazy_training_limit` (the constructed family),
with
the following differences from the original target below: the uniform finite-width gap is
`lambda_inf / 4` rather than `lambda_inf / 2` (initialization transfers a half-gap and the bootstrap
halves it again; the quarter-gap suffices), the drift rate is `O(√(log n / n))` in
`global_positive_gap_lazy_training_limit` (the logarithm comes from the maximum readout weight) and
`O(n⁻¹ᐟ²)` in `global_positive_gap_lazy_training_limit_inv_sqrt_width` (average moments), the
residual and loss decay rates are `lambda_inf / (4 m)` and `lambda_inf / (2 m)`, and the event is a
measurable initialization event of probability `≥ 1 - η`. The commented signature below is kept as
the original target.

**Statement**:
Under the same hypotheses as Theorem 1, assume in addition that the limiting
kernel `limitingFullNTKMatrix φ X`
satisfies a strictly positive spectral gap:
  `λ_min(limitingFullNTKMatrix φ X) = lambda_inf > 0`.

Then for any fixed confidence `δ ∈ (0, 1)`, there exist `N : ℕ` and `C > 0` such that for all
`n ≥ N`, with probability at least `1 - δ` under `initMeasure n d`:
1. **Uniform Spectral Gap**: For all `t ≥ 0`, `λ_min(K_n(t)) ≥ lambda_inf / 2`.
2. **Uniform Kernel Freeze**: For all `t ≥ 0`:
   `‖K_n(t) - K_n(0)‖ ≤ C * √(log n / n)` in the Frobenius norm.
3. **Exponential Residual Decay**: For all `t ≥ 0`:
   `‖r_n(t)‖ ≤ ‖r_n(0)‖ * exp(-(lambda_inf / (2 * m)) * t)`.
4. **Exponential Loss Decay**: For all `t ≥ 0`:
   `mseLoss f_n X y (θ_traj t) ≤ mseLoss f_n X y (θ_traj 0) * exp(-(lambda_inf / m) * t)`.
5. **Infinite-Time Convergence**:
   `lim_{t → ∞} mseLoss f_n X y (θ_traj t) = 0`.

A polynomial rate `1 - O(n^{-c})` may be derived as a corollary after quantitative
concentration estimates are established in Phase 3.5 or commit step 5.

**Frobenius Matrix Norm**:
The matrix norm `‖·‖` on `Matrix (Fin m) (Fin m) ℝ` throughout this target specification is the
Frobenius norm (`Matrix.Norms.Frobenius`), which dominates entrywise differences via
`|A i j| ≤ ‖A‖`.

**Uniform-Time Event Measurability**:
By path continuity of the gradient flow trajectory `t ↦ θ n p t` and continuity of the
matrix operations, residual, and MSE loss, each uniform-over-time condition `∀ t ≥ 0, ...`
is equivalent to the countable intersection over non-negative rationals `t ∈ ℚ, 0 ≤ t`.
Because each fixed-time evaluation is measurable from trajectory measurability (`hθ_meas`),
the uniform-time intersection event is measurable under `initMeasure n d`.

**Commented Formal Lean Signature**:
```lean
/-
theorem global_positive_gap_lazy_training_limit
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hderiv_lip : ∃ L_φ' : ℝ, 0 ≤ L_φ' ∧ LipschitzWith (Real.toNNReal L_φ') (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : Matrix.PosSemidef (limitingFullNTKMatrix φ X - lambda_inf • 1))
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (n * d + n)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∃ (N : ℕ) (C : ℝ), 0 < C ∧ ∀ n ≥ N,
      (initMeasure n d) {p |
        (∀ t ≥ 0, Matrix.PosSemidef
          (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) - (lambda_inf / 2) • 1)) ∧
        (∀ t ≥ 0,
          ‖empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
            empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖ ≤
            C * Real.sqrt (Real.log n / n)) ∧
        (∀ t ≥ 0,
          ‖trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
            ‖trainingResidual (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p 0)‖ *
              Real.exp (- (lambda_inf / (2 * m)) * t)) ∧
        (∀ t ≥ 0,
          mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t) ≤
            mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
              (θ n p 0) * Real.exp (- (lambda_inf / (m : ℝ)) * t))} ≥
        ENNReal.ofReal (1 - δ)
-/
```
-/

end GlobalPositiveGapLimit


/-! ### Construction of the Gradient-Flow Family

For a smooth activation (no bound on the value of `φ`), the negative MSE gradient field of the
two-layer network is locally Lipschitz (`locallyLipschitz_neg_gradient_mseLoss_netFromParams`) and
forward solutions obey an a priori bound: the loss is nonincreasing, so the residual stays bounded,
the Jacobian grows at most linearly in the parameters, and Grönwall's inequality bounds the
parameters on finite horizons (`forward_apriori_bound`). The generic theorem `exists_forward_flow`
therefore yields a forward flow, continuous in the initial parameters, so every initialization has a
`ForwardGFTrajectory` and fixed-time evaluation is continuous, hence measurable, in the
initialization. Backward-time solutions are deliberately not constructed: for an unbounded
activation they can blow up. -/

section GradientFlowConstruction

variable {m d n : ℕ}

/-- Coordinates of the negative MSE gradient of the two-layer network in terms of the hidden and
readout blocks. -/
lemma gradient_mseLoss_netFromParams_apply (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (k : Fin (n * d + n)) :
    gradient (mseLoss (netFromParams φ n d) X y) θ k =
      (m : ℝ)⁻¹ * ∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
        gradParams φ n d (X α) θ k := by
  have hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X α) θ') θ :=
    fun α => (hasFDerivAt_netFromParams φ n d (X α) θ fun i => hφ.differentiableAt).differentiableAt
  rw [gradient_mseLoss_apply_j _ X y θ hdiff k]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [outputJacobian, Matrix.of_apply, tangentFeature_netFromParams_of_differentiable φ hφ n d]
  simp [trainingResidual, trainingOutputs]
  ring

private lemma locallyLipschitz_const_mul {α : Type*} [PseudoEMetricSpace α] (c : ℝ) {f : α → ℝ}
    (hf : LocallyLipschitz f) : LocallyLipschitz (fun x => c * f x) :=
  locallyLipschitz_mul_real (LipschitzWith.const c).locallyLipschitz hf

private lemma locallyLipschitz_mul_const {α : Type*} [PseudoEMetricSpace α] (c : ℝ) {f : α → ℝ}
    (hf : LocallyLipschitz f) : LocallyLipschitz (fun x => f x * c) :=
  locallyLipschitz_mul_real hf (LipschitzWith.const c).locallyLipschitz

/-- The negative MSE gradient field of the two-layer network is locally Lipschitz when `φ` and its
derivative are locally Lipschitz. This is the hypothesis behind local existence and uniqueness of
the gradient-flow ODE (Picard-Lindelöf). Proof: every coordinate of the field is a finite sum of
products of locally Lipschitz functions of the packed parameters. -/
theorem locallyLipschitz_neg_gradient_mseLoss_netFromParams (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hφL : LocallyLipschitz φ) (hdφL : LocallyLipschitz (deriv φ))
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ) := by
  have hproj : ∀ k : Fin (n * d + n), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => θ k) := fun k =>
    (ContinuousLinearMap.contDiff (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin (n * d + n))
      →L[ℝ] ℝ)).locallyLipschitz
  have hpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => unpackW θ i ⊙ X α) := fun i α => by
    unfold innerProduct
    exact locallyLipschitz_finset_sum _ fun j _ => locallyLipschitz_mul_const _ (hproj _)
  have hφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => φ (unpackW θ i ⊙ X α)) :=
    fun i α => hφL.comp (hpre i α)
  have hdφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => deriv φ (unpackW θ i ⊙ X α)) :=
    fun i α => hdφL.comp (hpre i α)
  have hnet : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => netFromParams φ n d (X α) θ) := fun α => by
    simp only [netFromParams_eq_normalized_sum]
    exact locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun i _ =>
      locallyLipschitz_mul_real (hproj _) (hφpre i α))
  have hres : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) => netFromParams φ n d (X α) θ - y α) :=
    fun α => by
      simpa only [sub_eq_add_neg] using (hnet α).add (LipschitzWith.const (-(y α))).locallyLipschitz
  refine locallyLipschitz_euclidean_of_coord fun k => ?_
  obtain ⟨p, rfl⟩ := (paramIndexEquiv n d).surjective k
  have hform : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
      (-gradient (mseLoss (netFromParams φ n d) X y) θ) ((paramIndexEquiv n d) p) =
        -((m : ℝ)⁻¹ * ∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun θ => by
    rw [PiLp.neg_apply, gradient_mseLoss_netFromParams_apply φ hφ]
  simp only [hform]
  have hg : ∀ α : Fin m, LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun α => by
    rcases p with ⟨i, j⟩ | i
    · have : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inl (i, j))) =
            (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ X α) * X α j := fun θ =>
        packParams_apply_idxW _ _ i j
      simp only [this]
      exact locallyLipschitz_mul_const _ (locallyLipschitz_mul_real
        (locallyLipschitz_const_mul _ (hproj (idxA i))) (hdφpre i α))
    · have : ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inr i)) =
            (n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ X α) := fun θ => packParams_apply_idxA _ _ i
      simp only [this]
      exact locallyLipschitz_const_mul _ (hφpre i α)
  exact (locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun α _ =>
    locallyLipschitz_mul_real (hres α) (hg α))).neg

section APriori
variable {φ : ℝ → ℝ} {C₁ C₂ : ℝ}

private lemma flow_sqrt_inv_nat_mul_nat (hn : 0 < n) :
    ((n : ℝ)⁻¹).sqrt * (n : ℝ) = Real.sqrt (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_inv]
  field_simp
  exact (Real.sq_sqrt hn'.le).symm

/-- Cauchy-Schwarz for the input-weight preactivation. -/
private lemma sq_innerProduct_le (w x : Fin d → ℝ) :
    (w ⊙ x) ^ 2 ≤ (∑ j : Fin d, w j ^ 2) * ∑ j : Fin d, x j ^ 2 := by
  unfold innerProduct
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Linear growth of the output Jacobian.** For a smooth activation the Frobenius norm of the
output Jacobian grows at most linearly in the parameter norm: `‖J(θ)‖ ≤ c₀ + c₁ ‖θ‖`, with constants
depending on the data but not on `θ`. Each neuron block satisfies
`‖w_i‖² + a_i² ≤ ‖θ‖²`, and `φ(w ⊙ x)² ≤ 2 φ(0)² + 2 C₁² ‖w‖² ‖x‖²`. -/
private lemma exists_jacobian_linear_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)),
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ c₀ + c₁ * ‖θ‖ := by
  obtain ⟨hC₁0, -, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  set S : Fin m → ℝ := fun α => ∑ j : Fin d, X α j ^ 2 with hS
  have hS0 : ∀ α, 0 ≤ S α := fun α => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨Real.sqrt (2 * m * φ 0 ^ 2), Real.sqrt (3 * C₁ ^ 2 * ∑ α : Fin m, S α),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, fun θ => ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hblock : ∀ i : Fin n, (∑ j : Fin d, θ (idxW i j) ^ 2) + θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 :=
    fun i => by
      rw [← norm_sq_restrictCoords_neuronCoords]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictCoords_neuronCoords_le i θ) 2
  -- per-entry bound
  have hentry : ∀ (α : Fin m) (i : Fin n),
      (∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) + gradA φ n d (X α) θ i ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) := by
    intro α i
    refine (neuron_block_energy_le φ hact.deriv_bdd hn θ i (X α)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set u := unpackW θ i ⊙ X α with hu
    have hφu : φ u ^ 2 ≤ 2 * φ 0 ^ 2 + 2 * (C₁ ^ 2 * u ^ 2) := by
      have h1 : |φ u| ≤ |φ 0| + C₁ * |u| := by
        have := hφ_lip u 0
        rw [sub_zero] at this
        calc |φ u| ≤ |φ 0| + |φ u - φ 0| := by
              have := abs_sub_abs_le_abs_sub (φ u) (φ 0)
              linarith [abs_sub_comm (φ u) (φ 0)]
          _ ≤ _ := by linarith
      have h2 := add_sq_le (a := |φ 0|) (b := C₁ * |u|)
      calc φ u ^ 2 = |φ u| ^ 2 := (sq_abs _).symm
        _ ≤ (|φ 0| + C₁ * |u|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ 2 * (|φ 0| ^ 2 + (C₁ * |u|) ^ 2) := h2
        _ = _ := by rw [sq_abs, mul_pow, sq_abs]; ring
    have hucs : u ^ 2 ≤ (∑ j : Fin d, θ (idxW i j) ^ 2) * S α := sq_innerProduct_le _ _
    have hw : (∑ j : Fin d, θ (idxW i j) ^ 2) ≤ ‖θ‖ ^ 2 := by
      have := hblock i
      nlinarith [sq_nonneg (θ (idxA i))]
    have ha : θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 := by
      have := hblock i
      nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (θ (idxW i j))]
    have hSα := hS0 α
    have hC := sq_nonneg C₁
    have hu2 : u ^ 2 ≤ ‖θ‖ ^ 2 * S α :=
      hucs.trans (mul_le_mul_of_nonneg_right hw hSα)
    have hun : unpackA θ i ^ 2 = θ (idxA i) ^ 2 := rfl
    rw [hun]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hC, mul_le_mul_of_nonneg_left ha
      (mul_nonneg hC hSα)]
  have hsq : ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 ≤
      2 * m * φ 0 ^ 2 + 3 * C₁ ^ 2 * (∑ α : Fin m, S α) * ‖θ‖ ^ 2 := by
    rw [outputJacobian_netFromParams_frobenius_norm_sq φ n d m X θ
      (fun _ _ => hact.differentiable.differentiableAt)]
    have hreg : (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
        ∑ α : Fin m, ∑ i : Fin n, gradA φ n d (X α) θ i ^ 2 =
        ∑ α : Fin m, ∑ i : Fin n, ((∑ j : Fin d, gradW φ n d (X α) θ i j ^ 2) +
          gradA φ n d (X α) θ i ^ 2) := by
      simp only [Finset.sum_add_distrib]
    rw [hreg]
    calc _ ≤ ∑ α : Fin m, ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => hentry α i
      _ = ∑ α : Fin m, (2 * φ 0 ^ 2 + 3 * C₁ ^ 2 * S α * ‖θ‖ ^ 2) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
          ring
  have hnn : 0 ≤ 2 * (m : ℝ) * φ 0 ^ 2 := by positivity
  have hnn' : 0 ≤ 3 * C₁ ^ 2 * (∑ α : Fin m, S α) := by
    have : 0 ≤ ∑ α : Fin m, S α := Finset.sum_nonneg fun α _ => hS0 α
    positivity
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  calc ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2
      ≤ 2 * m * φ 0 ^ 2 + 3 * C₁ ^ 2 * (∑ α : Fin m, S α) * ‖θ‖ ^ 2 := hsq
    _ ≤ (Real.sqrt (2 * m * φ 0 ^ 2) +
          Real.sqrt (3 * C₁ ^ 2 * ∑ α : Fin m, S α) * ‖θ‖) ^ 2 := by
        rw [add_sq, mul_pow, Real.sq_sqrt hnn, Real.sq_sqrt hnn']
        nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg (2 * (m : ℝ) * φ 0 ^ 2))
          (Real.sqrt_nonneg (3 * C₁ ^ 2 * ∑ α : Fin m, S α))) (norm_nonneg θ)]

/-- **The training residual is bounded on bounded parameter sets.** For a smooth activation
(linear growth) and fixed width, `‖r(θ)‖ ≤ B` whenever `‖θ‖ ≤ ρ`. -/
private lemma exists_residual_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : EuclideanSpace ℝ (Fin (n * d + n)), ‖θ‖ ≤ ρ →
      ‖trainingResidual (netFromParams φ n d) X y θ‖ ≤ B := by
  obtain ⟨hC₁0, -, hφ_lip, -⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set ρp : ℝ := max ρ 0 with hρp
  have hρ0 : 0 ≤ ρp := le_max_right _ _
  set b : Fin m → ℝ := fun α => Real.sqrt (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp *
    Real.sqrt (∑ j : Fin d, X α j ^ 2)))) + |y α| with hb
  refine ⟨∑ α : Fin m, b α, Finset.sum_nonneg fun α _ => by positivity, fun θ hθ => ?_⟩
  have hθ' : ‖θ‖ ≤ ρp := hθ.trans (le_max_left _ _)
  refine (norm_euclidean_le_sum_norm _).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  have hresα : trainingResidual (netFromParams φ n d) X y θ α =
      netFromParams φ n d (X α) θ - y α := rfl
  rw [hresα, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  refine add_le_add ?_ le_rfl
  rw [netFromParams_eq_normalized_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hterm : ∀ i : Fin n, |unpackA θ i * φ (unpackW θ i ⊙ X α)| ≤
      ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))) := by
    intro i
    have hblock : (∑ j : Fin d, θ (idxW i j) ^ 2) + θ (idxA i) ^ 2 ≤ ‖θ‖ ^ 2 := by
      rw [← norm_sq_restrictCoords_neuronCoords]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictCoords_neuronCoords_le i θ) 2
    have ha : |unpackA θ i| ≤ ρp := by
      have h2 : unpackA θ i ^ 2 ≤ ρp ^ 2 := by
        change θ (idxA i) ^ 2 ≤ ρp ^ 2
        have := hblock
        nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (θ (idxW i j)),
          pow_le_pow_left₀ (norm_nonneg θ) hθ' 2]
      exact (sq_le_sq₀ (abs_nonneg _) hρ0).1 (by rwa [sq_abs])
    have hu : |unpackW θ i ⊙ X α| ≤ ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2) := by
      have hw : (∑ j : Fin d, θ (idxW i j) ^ 2) ≤ ρp ^ 2 := by
        have := hblock
        nlinarith [sq_nonneg (θ (idxA i)), pow_le_pow_left₀ (norm_nonneg θ) hθ' 2]
      have hu2 : |unpackW θ i ⊙ X α| ^ 2 ≤
          (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) ^ 2 := by
        rw [sq_abs, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        exact (sq_innerProduct_le (unpackW θ i) (X α)).trans
          (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 hu2
    have hφu : |φ (unpackW θ i ⊙ X α)| ≤
        |φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) := by
      have := hφ_lip (unpackW θ i ⊙ X α) 0
      rw [sub_zero] at this
      have h1 : |φ (unpackW θ i ⊙ X α)| ≤ |φ 0| + |φ (unpackW θ i ⊙ X α) - φ 0| := by
        have := abs_sub_abs_le_abs_sub (φ (unpackW θ i ⊙ X α)) (φ 0)
        linarith [abs_sub_comm (φ (unpackW θ i ⊙ X α)) (φ 0)]
      have h2 : C₁ * |unpackW θ i ⊙ X α| ≤ C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)) :=
        mul_le_mul_of_nonneg_left hu hC₁0
      linarith
    rw [abs_mul]
    exact mul_le_mul ha hφu (abs_nonneg _) hρ0
  have hsum : |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⊙ X α)| ≤
      (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin n, ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  calc ((n : ℝ)⁻¹).sqrt * |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⊙ X α)|
      ≤ ((n : ℝ)⁻¹).sqrt * ((n : ℝ) *
          (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2))))) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = Real.sqrt (n : ℝ) * (ρp * (|φ 0| + C₁ * (ρp * Real.sqrt (∑ j : Fin d, X α j ^ 2)))) := by
        rw [← mul_assoc, flow_sqrt_inv_nat_mul_nat hn]

/-- **Forward a priori bound for gradient-flow solutions.** For a smooth activation and fixed width,
any solution of `θ' = -∇L(θ)` on `[0, S]`, `S ≤ T`, that starts in the ball of radius `r` stays in a
ball of radius `ρ(T, r)`. Proof: the loss is nonincreasing, hence the residual stays bounded by its
initial size `B`; then `‖θ'‖ ≤ (1/m) ‖J(θ)‖ B ≤ K ‖θ‖ + ε` by the linear growth of the Jacobian and
Grönwall's inequality applies. Only forward time is used, and no bound on `φ` itself. -/
private theorem forward_apriori_bound (hact : SmoothActivation φ C₁ C₂) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T r : ℝ) :
    ∃ ρ : ℝ, ∀ (θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))) (S : ℝ), 0 ≤ S → S ≤ T →
      ‖θ 0‖ ≤ r → (∀ t ∈ Set.Icc 0 S,
        HasDerivWithinAt θ (-gradient (mseLoss (netFromParams φ n d) X y) (θ t))
          (Set.Icc 0 S) t) → ‖θ S‖ ≤ ρ := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hJ⟩ := exists_jacobian_linear_bound hact hn X
  obtain ⟨B, hB0, hB⟩ := exists_residual_bound hact hn X y r
  set rp : ℝ := max r 0 with hrp
  set Tp : ℝ := max T 0 with hTp
  have hr0 : 0 ≤ rp := le_max_right _ _
  set K : ℝ := (m : ℝ)⁻¹ * c₁ * B with hK
  set ε : ℝ := (m : ℝ)⁻¹ * c₀ * B with hε
  have hK0 : 0 ≤ K := by positivity
  have hε0 : 0 ≤ ε := by positivity
  refine ⟨(rp + ε * Tp) * Real.exp (K * Tp), fun θ S hS0 hST hθ0 hθ => ?_⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (X β) θ') (θ t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (X β) (θ t)
      fun i => hact.differentiable.differentiableAt).differentiableAt
  have hmono := mseLoss_le_of_hasDerivWithinAt_neg_gradient (netFromParams φ n d) X y
    (θ := θ) (S := S) (fun t _ => hdiff t) hθ
  have hres : ∀ t ∈ Set.Icc (0 : ℝ) S,
      ‖trainingResidual (netFromParams φ n d) X y (θ t)‖ ≤ B := by
    intro t ht
    have h0 : ‖trainingResidual (netFromParams φ n d) X y (θ 0)‖ ≤ B := hB _ hθ0
    have h1 := hmono t ht
    unfold mseLoss at h1
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have : ‖trainingResidual (netFromParams φ n d) X y (θ t)‖ = 0 := by
        rw [EuclideanSpace.norm_eq]; simp
      rw [this]; exact hB0
    · have h2 := le_of_mul_le_mul_left h1 (by positivity : (0 : ℝ) < (2 * (m : ℝ))⁻¹)
      exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2).trans h0
  have hspeed : ∀ t ∈ Set.Icc (0 : ℝ) S,
      ‖-gradient (mseLoss (netFromParams φ n d) X y) (θ t)‖ ≤ K * ‖θ t‖ + ε := by
    intro t ht
    rw [norm_neg]
    refine (gradient_mseLoss_norm_le (netFromParams φ n d) X y (θ t) (hdiff t)).trans ?_
    have h1 := hJ (θ t)
    calc (m : ℝ)⁻¹ * ‖outputJacobian (netFromParams φ n d) X (θ t)‖ *
          ‖trainingResidual (netFromParams φ n d) X y (θ t)‖
        ≤ (m : ℝ)⁻¹ * (c₀ + c₁ * ‖θ t‖) * B := by
          gcongr
          exact hres t ht
      _ = K * ‖θ t‖ + ε := by rw [hK, hε]; ring
  have hcont : ContinuousOn θ (Set.Icc 0 S) := fun t ht => (hθ t ht).continuousWithinAt
  have hright : ∀ x ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt θ (-gradient (mseLoss (netFromParams φ n d) X y) (θ x)) (Set.Ici x) x :=
    fun x hx => (hθ x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Set.Icc_subset_Icc hx.1 le_rfl))
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hcont hright (δ := rp)
    (le_trans hθ0 (le_max_left _ _)) (fun x hx => hspeed x ⟨hx.1, hx.2.le⟩) S ⟨hS0, le_rfl⟩
  refine hG.trans ((gronwallBound_le_mul_exp hK0 hε0).trans ?_)
  have hST' : S ≤ Tp := hST.trans (le_max_left _ _)
  rw [sub_zero]
  gcongr

private theorem exists_forwardGradientFlow_of_pos (hact : SmoothActivation φ C₁ C₂)
    (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (n * d + n)) → ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ θ₀, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      Continuous (fun q : EuclideanSpace ℝ (Fin (n * d + n)) × ℝ => Φ q.1 q.2) := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz hact
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hact.differentiable
    hφL hdφL X y
  obtain ⟨Φ, hΦ0, hΦd, hΦc⟩ := exists_forward_flow
    (fun θ : EuclideanSpace ℝ (Fin (n * d + n)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ)
    (lipschitz_on_ball_of_locallyLipschitz hLL)
    (fun T r => forward_apriori_bound hact hn X y T r)
  exact ⟨Φ, fun θ₀ => ⟨hΦ0 θ₀,
    (hΦc.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn,
    fun t ht => by simpa using hΦd θ₀ t ht⟩, hΦc⟩

/-- **Every initialization has a gradient flow, continuous in the initialization.** For a
`SmoothActivation` (no bound on the value of `φ`) and any dataset there is a map `Φ` such that
`Φ θ₀` is a forward-time trajectory of the MSE gradient flow started at `θ₀`, jointly continuous in
the initial parameters and time. Existence uses the Picard-Lindelöf theorem on a truncated field and
the a priori bound `forward_apriori_bound`; nothing is asserted for negative times, where
solutions can blow up. -/
theorem exists_forwardGradientFlow (hact : SmoothActivation φ C₁ C₂) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (n * d + n)) → ℝ → EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ θ₀, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      Continuous (fun q : EuclideanSpace ℝ (Fin (n * d + n)) × ℝ => Φ q.1 q.2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no parameters: the parameter space is a point
    have hsub : ∀ u v : EuclideanSpace ℝ (Fin 0), u = v := fun u v => by
      ext k
      exact Fin.elim0 k
    refine ⟨fun θ₀ _ => θ₀, fun θ₀ => ⟨rfl, continuousOn_const, fun t _ => ?_⟩, continuous_fst⟩
    rw [show -gradient (mseLoss (netFromParams φ 0 d) X y) θ₀ = 0 from hsub _ _]
    exact hasDerivAt_const t θ₀
  · exact exists_forwardGradientFlow_of_pos hact hn X y

/-- **Uniqueness of the gradient flow.** Two forward gradient-flow trajectories of the MSE loss of
the two-layer network from the same initialization agree for all `t ≥ 0` (for a
`SmoothActivation`). -/
theorem forwardGradientFlow_unique (hact : SmoothActivation φ C₁ C₂) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {f g : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hf : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ f)
    (hg : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ g) :
    Set.EqOn f g (Set.Ici 0) := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz hact
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hact.differentiable
    hφL hdφL X y
  exact forwardFlow_unique _ (lipschitz_on_ball_of_locallyLipschitz hLL) hf.continuousOn hf.ode
    hg.continuousOn hg.ode (hf.init.trans hg.init.symm)

/-- **A measurable family of gradient-flow trajectories over the initialization laws.** There is a
family `θ n p` such that for *every* width `n` and *every* initialization `p`, `θ n p` is a forward
gradient flow of the MSE loss started at `packParams p.1 p.2`, and each fixed-time evaluation is
continuous, hence measurable, in `p`. This discharges the hypotheses `hθ_flow` (in fact everywhere,
not only almost everywhere) and `hθ_meas` of the finite-horizon and global theorems, under the
source's activation assumptions only. -/
theorem exists_forwardGradientFlow_family (hact : SmoothActivation φ C₁ C₂) (d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2)
        (θ n p)) ∧
      ∀ n t, Continuous (fun p => θ n p t) := by
  choose Φ hΦ hΦc using fun n : ℕ => exists_forwardGradientFlow hact n d m X y
  exact ⟨fun n p => Φ n (packParams p.1 p.2), fun n p => hΦ n _,
    fun n t => (hΦc n).comp (continuous_packParams.prodMk continuous_const)⟩

end APriori

/-- **Finite-horizon training limit for the constructed gradient flow (no spectral gap, no
trajectory hypotheses).** For a `SmoothActivation` (no bound on the value of `φ`), the
constructed family of gradient-flow trajectories `θ n p` (defined for every width and every
initialization, measurable
in `p`) has: kernel stationarity in probability on every `[0, T]`, and, at every fixed time
`t ≥ 0`, the trained residual and predictions converge in distribution to the frozen-kernel laws
`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`, `G ~ 𝒩(0, Φ^{(∞)})`. -/
theorem gradientFlow_finite_horizon_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ ε₀ : ℝ, 0 < ε₀ → Filter.Tendsto
        (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
            empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
        Filter.atTop (nhds 0)) ∧
      (∀ t : ℝ, 0 ≤ t → TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t))
        Filter.atTop
        (fun G : EuclideanSpace ℝ (Fin m) =>
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))) ∧
      (∀ t : ℝ, 0 ≤ t → TendstoInDistribution
        (fun n (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
          trainingOutputs (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t))
        Filter.atTop
        (fun G : EuclideanSpace ℝ (Fin m) =>
          y + (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (G - y).ofLp) : EuclideanSpace ℝ (Fin m)))
        (fun n => initMeasure n d)
        (multivariateGaussian 0
          (limitingCovariance φ (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂(initMeasure n d), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    fun T hT ε₀ hε₀ => tendsto_measure_kernel_drift_finite_horizon hm φ hact X y T hT θ hae hε₀,
    fun t ht => tendstoInDistribution_trainingResidual_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hcont n t).measurable.aemeasurable) hae,
    fun t ht => tendstoInDistribution_trainingOutputs_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hcont n t).measurable.aemeasurable) hae⟩

/-- **Global positive-gap lazy training limit for the constructed gradient flow.** Under a positive
limiting gap, the constructed family of gradient-flow trajectories (defined for every width and
every initialization, measurable in the initialization) satisfies the conclusion of
`global_positive_gap_lazy_training_limit`: with a measurable initialization event of probability at
least `1 - η`, the uniform quarter-gap, `O(√(log n / n))` kernel drift, exponential residual and
loss decay, and `mseLoss → 0`. No trajectory hypothesis remains. -/
theorem gradientFlow_global_positive_gap_lazy_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (
      ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
        (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
        ∀ n ≥ N,
        ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
          (initMeasure n d).real E ≥ 1 - η ∧ ∀ᵐ p ∂(initMeasure n d), p ∈ E →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ n p t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0)) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂(initMeasure n d), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    global_positive_gap_lazy_training_limit hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap θ hae hη hη1⟩

/-- **Positive limiting gap from feature independence (SmoothActivation).** If the features
`w ↦ φ(w ⊙ (X α / √d))` are linearly independent modulo Gaussian-null sets -- no nontrivial
combination vanishes almost everywhere -- then the limiting kernel is positive definite and there is
`lambda_inf > 0` with `(K_∞ - lambda_inf • 1).PosSemidef`, the hypothesis `hK_gap` of the global
lazy-training theorems. The activation enters only through `SmoothActivation`, which supplies
measurability of `φ'` and the `L²` integrability of the features. -/
theorem exists_positive_gap_of_feature_independence {φ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂) {d m : ℕ} (X : Fin m → Fin d → ℝ)
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    ∃ lambda_inf : ℝ, 0 < lambda_inf ∧ (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef := by
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hact.deriv_bdd
    hact.deriv_lip hact.differentiable
  obtain ⟨hL2, -, hdL2, -⟩ := activation_memLp_two hact (d := d)
  exact exists_pos_sub_smul_one_posSemidef_of_posDef
    (limitingFullNTKMatrix_posDef_of_ae_independent φ X hderiv_meas
      (fun α => hL2 _) (fun α => hdL2 _) hind)

/-- **Constructed global lazy training from feature independence alone.** For a `SmoothActivation`
and a dataset whose scaled features are linearly independent modulo Gaussian-null sets, there is a
positive limiting gap `lambda_inf` (`exists_positive_gap_of_feature_independence`), and for every
confidence `η` the conclusion of `gradientFlow_global_positive_gap_lazy_training_limit` holds for
the constructed gradient flows with that `lambda_inf`; no spectral-gap hypothesis is assumed. -/
theorem gradientFlow_global_lazy_training_limit_of_feature_independence
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⊙ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ lambda_inf : ℝ, 0 < lambda_inf ∧
        ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
            EuclideanSpace ℝ (Fin (n * d + n)),
          (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
          (∀ n t, Measurable (fun p => θ n p t)) ∧
          (
          ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
            (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
            ∀ n ≥ N,
            ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
              (initMeasure n d).real E ≥ 1 - η ∧ ∀ᵐ p ∂(initMeasure n d), p ∈ E →
                (∀ t : ℝ, 0 ≤ t →
                  (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                    v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
                  ‖empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                    empiricalNTKMatrix (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                    freezeRate n ∧
                  ‖trainingResidual (netFromParams φ n d)
                      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                    ‖trainingResidual (netFromParams φ n d)
                        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                      Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
                  mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                      (θ n p t) ≤
                    mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                        (packParams p.1 p.2) *
                      Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
                Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop
                  (nhds 0)) := by
  obtain ⟨lambda_inf, hlam, hgap⟩ := exists_positive_gap_of_feature_independence hact X hind
  exact ⟨lambda_inf, hlam, gradientFlow_global_positive_gap_lazy_training_limit hm hd φ hact X y
    lambda_inf hlam hgap hη hη1⟩

/-- **Constructed gradient flows with kernel drift `O(n⁻¹ᐟ²)`.** The statement of
`gradientFlow_global_positive_gap_lazy_training_limit` with the sharper drift rate of
`global_positive_gap_lazy_training_limit_inv_sqrt_width`. -/
theorem gradientFlow_global_positive_gap_lazy_training_limit_inv_sqrt_width
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₁ C₂ : ℝ}
    (hact : SmoothActivation φ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (n * d + n)),
      (∀ n p, ForwardGFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)) ∧
      (∀ n t, Measurable (fun p => θ n p t)) ∧
      (
      ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
        (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ / Real.sqrt (n : ℝ)) ∧
        ∀ n ≥ N,
        ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
          (initMeasure n d).real E ≥ 1 - η ∧ ∀ᵐ p ∂(initMeasure n d), p ∈ E →
            (∀ t : ℝ, 0 ≤ t →
              (∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 4) * ‖v‖ ^ 2 ≤
                v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t)) *ᵥ v.ofLp)) ∧
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n ∧
              ‖trainingResidual (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)‖ ≤
                ‖trainingResidual (netFromParams φ n d)
                    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ *
                  Real.exp (-(lambda_inf / (4 * (m : ℝ))) * t) ∧
              mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                  (θ n p t) ≤
                mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
                    (packParams p.1 p.2) *
                  Real.exp (-(lambda_inf / (2 * (m : ℝ))) * t)) ∧
            Filter.Tendsto (fun t : ℝ => mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (θ n p t)) Filter.atTop (nhds 0)) := by
  obtain ⟨θ, hflow, hcont⟩ := exists_forwardGradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂(initMeasure n d), ForwardGFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, fun n t => (hcont n t).measurable,
    global_positive_gap_lazy_training_limit_inv_sqrt_width hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap θ hae hη hη1⟩

end GradientFlowConstruction

end FullTwoLayerTrainingLimit

end

end NTK
