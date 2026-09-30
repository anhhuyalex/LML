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
`θ : EuclideanSpace ℝ (Fin (paramDim n d))` expected by `tangentFeature`,
`outputJacobian`, and `empiricalNTKMatrix` in `Kernel.lean`. Gap 3 concentrates the output
Jacobian's Frobenius norm at initialization; Gap 4 gives a local Lipschitz bound on the
Jacobian. Gap 6 (`lazy_training_kernel_freeze_bound_of_gaussian_init`) wires all of this,
plus Gap 5's bootstrap in `InfiniteNTK.lean`, into a single fully probabilistic corollary with
no free `hlazy`/`hLip` hypotheses.

## Main Definitions
- `paramDim n d`: Total parameter dimension `n * d + n` for width `n` and input dimension `d`.
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
- `BoundedSmoothActivation` : bundled activation hypotheses (differentiable, bounded value,
  bounded derivative, Lipschitz derivative) shared by the paper-facing theorems below.
- `tendsto_measure_kernel_drift_finite_horizon`,
  `tendstoInDistribution_trainingResidual_matrix_exp`,
  `tendstoInDistribution_trainingOutputs_matrix_exp` : **Phase 8** - finite-horizon kernel
  stationarity in probability and fixed-time weak limits of the trained residual and predictions
  (`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`), with no spectral gap.
- `exists_finite_horizon_kernel_freeze_event` : the no-gap counterpart on `[0, T]` with failure
  probability `≤ 2δ + ε`; positive semidefiniteness alone bounds the residual and the
  displacement radius `C = T M R / m` grows linearly in `T`.
- `exists_gradientFlow`, `exists_gradientFlow_family`, `gradientFlow_unique`,
  `gradientFlow_finite_horizon_training_limit`,
  `gradientFlow_global_positive_gap_lazy_training_limit` : **Phase 10** - existence, uniqueness and
  continuous dependence of the two-sided gradient flow (Picard-Lindelöf on a truncated field, a priori
  bounds by Grönwall), a measurable trajectory family for every width, and the Phase 8 and Phase 9
  theorems with the trajectory hypotheses discharged.
- `exists_measurableSet_global_lazy_training_event`, `global_positive_gap_lazy_training_limit` :
  **Phase 9** - under a positive limiting gap, uniform Rayleigh gap `λ_∞ / 4`, kernel drift
  `O(√(log n / n))`, exponential residual and loss decay and `mseLoss → 0`, with probability
  `≥ 1 - η`.
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

/-- Total parameter count for a two-layer network with width `n` and input dimension `d`:
`n * d` input weights in `W` and `n` readout weights in `a`. -/
def paramDim (n d : ℕ) : ℕ := n * d + n

/-- Canonical bijection between the disjoint union `(Fin n × Fin d) ⊕ Fin n` and the packed
index type `Fin (paramDim n d)`. The left summand indexes `W_{i, j}` and the right summand
indexes `a_i`. -/
def paramIndexEquiv (n d : ℕ) : (Fin n × Fin d) ⊕ Fin n ≃ Fin (paramDim n d) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv

/-- Index of the weight matrix entry `W_{i, j}` in the packed parameter vector. -/
def idxW {n d : ℕ} (i : Fin n) (j : Fin d) : Fin (paramDim n d) :=
  paramIndexEquiv n d (Sum.inl (i, j))

/-- Index of the readout weight `a_i` in the packed parameter vector. -/
def idxA {n d : ℕ} (i : Fin n) : Fin (paramDim n d) :=
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
`EuclideanSpace ℝ (Fin (paramDim n d))`. -/
noncomputable def packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (paramDim n d)) :=
  WithLp.toLp 2 (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i)

/-- Unpack the input weights `W : Fin n → Fin d → ℝ` from a flat parameter vector `θ`. -/
noncomputable def unpackW {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    Fin n → Fin d → ℝ :=
  fun i j => θ (idxW i j)

/-- Unpack the readout weights `a : Fin n → ℝ` from a flat parameter vector `θ`. -/
noncomputable def unpackA {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
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
lemma packParams_unpack {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
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

/-- The continuous linear map `θ ↦ unpackW θ i ⊙ x`. Internal helper. -/
private noncomputable def dotW_CLM {n d : ℕ} (i : Fin n) (x : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin (paramDim n d)) →L[ℝ] ℝ :=
  ∑ j : Fin d, (x j) • EuclideanSpace.proj (idxW i j)

private lemma dotW_CLM_apply {n d : ℕ} (i : Fin n) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    dotW_CLM i x θ = unpackW θ i ⊙ x := by
  simp only [dotW_CLM, sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, innerProduct]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [unpackW]
  ring

/-- The inner product `⟪packParams W a, v⟫` expressed as a sum over the
two coordinate blocks. -/
lemma inner_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin (paramDim n d))) :
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) : ℝ :=
  evalSingle φ (unpackW θ) (unpackA θ) x

lemma netFromParams_eq_normalized_sum (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) : Fin n → Fin d → ℝ :=
  fun i j => (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ x) * x j

/-- Gradient block for readout weights `a`:
`∂f/∂a_i = n^{-1/2} φ(W_i ⊙ x)`. -/
noncomputable def gradA (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) : Fin n → ℝ :=
  fun i => (n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ x)

/-- The packed gradient vector in `EuclideanSpace ℝ (Fin (paramDim n d))`. -/
noncomputable def gradParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    EuclideanSpace ℝ (Fin (paramDim n d)) :=
  packParams (gradW φ n d x θ) (gradA φ n d x θ)

/-- Fréchet derivative of `netFromParams` with respect to parameters `θ`. -/
theorem hasFDerivAt_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    HasFDerivAt (netFromParams φ n d x)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (paramDim n d)))
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
      ((EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (paramDim n d)) →L[ℝ] ℝ)) θ := by
    intro i
    exact (EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (paramDim n d)) →L[ℝ] ℝ).hasFDerivAt
  have h_mul : ∀ i : Fin n, HasFDerivAt (fun θ => unpackA θ i * φ (unpackW θ i ⊙ x))
      ((unpackA θ i) • (deriv φ (unpackW θ i ⊙ x) • dotW_CLM i x) +
       (φ (unpackW θ i ⊙ x)) •
         (EuclideanSpace.proj (idxA i) : EuclideanSpace ℝ (Fin (paramDim n d)) →L[ℝ] ℝ)) θ := by
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    HasGradientAt (netFromParams φ n d x) (gradParams φ n d x θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_netFromParams φ n d x θ hφ

/-- Gradient evaluation lemma for `netFromParams`. -/
theorem gradient_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    gradient (netFromParams φ n d x) θ = gradParams φ n d x θ :=
  (hasGradientAt_netFromParams φ n d x θ hφ).gradient

/-- Equation lemma for `tangentFeature`:
`tangentFeature (netFromParams φ n d) x θ = packParams (gradW ...) (gradA ...)`. -/
theorem tangentFeature_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  gradient_netFromParams φ n d x θ hφ

/-- Equation lemma for `tangentFeature` when `φ` is globally differentiable. -/
theorem tangentFeature_netFromParams_of_differentiable (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (n d : ℕ) (x : Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  tangentFeature_netFromParams φ n d x θ (fun _ => hφ _)

@[simp]
lemma unpackW_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    unpackW (tangentFeature (netFromParams φ n d) x θ) = gradW φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackW_packParams _ _

@[simp]
lemma unpackA_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ x)) :
    unpackA (tangentFeature (netFromParams φ n d) x θ) = gradA φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackA_packParams _ _

/-- Output Jacobian entry for `netFromParams` evaluated at `idxW i j`, delegating to `gradW`. -/
lemma outputJacobian_netFromParams_apply_W (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α : Fin m) (i : Fin n) (j : Fin d) :
    outputJacobian (netFromParams φ n d) X θ α (idxW i j) =
      gradW φ n d (X α) θ i j := by
  change unpackW (tangentFeature (netFromParams φ n d) (X α) θ) i j = _
  rw [unpackW_tangentFeature φ n d (X α) θ (hφ α)]

/-- Output Jacobian entry for `netFromParams` evaluated at `idxA i`, delegating to `gradA`. -/
lemma outputJacobian_netFromParams_apply_a (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⊙ X α))
    (α : Fin m) (i : Fin n) :
    outputJacobian (netFromParams φ n d) X θ α (idxA i) =
      gradA φ n d (X α) θ i := by
  change unpackA (tangentFeature (netFromParams φ n d) (X α) θ) i = _
  rw [unpackA_tangentFeature φ n d (X α) θ (hφ α)]

/-- Squared Frobenius norm of an output Jacobian as its coordinate energy. -/
lemma outputJacobian_frobenius_norm_sq_entries (n d m : ℕ) (φ : ℝ → ℝ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    ‖outputJacobian (netFromParams φ n d) X θ‖ ^ 2 =
      ∑ α : Fin m, ∑ k : Fin (paramDim n d),
        (outputJacobian (netFromParams φ n d) X θ α k) ^ (2 : ℝ) := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs]
  rw [← Real.sqrt_eq_rpow]
  have hnonneg : 0 ≤ ∑ α : Fin m, ∑ k : Fin (paramDim n d),
      |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ) := by
    apply Finset.sum_nonneg
    intro α hα
    apply Finset.sum_nonneg
    intro k hk
    positivity
  calc
    √(∑ α : Fin m, ∑ k : Fin (paramDim n d),
        |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ)) ^ 2 =
        ∑ α : Fin m, ∑ k : Fin (paramDim n d),
          |outputJacobian (netFromParams φ n d) X θ α k| ^ (2 : ℝ) := Real.sq_sqrt hnonneg
    _ = _ := by simp [sq_abs]

/-- Closed-form decomposition of the squared Frobenius norm of the output Jacobian into the
input-weight and readout blocks. -/
lemma outputJacobian_netFromParams_frobenius_norm_sq_rpow (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
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

/-! ### Phase 4: Local Lipschitz Bound on the Output Jacobian -/

lemma two_mul_add_two_mul_sq (u v : ℝ) :
    (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  have : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
  linarith

lemma norm_sq_sub_unpack (n d : ℕ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (paramDim n d))) :
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
    (X : Fin m → Fin d → ℝ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n)
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
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (paramDim n d)))
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

/-- The empirical NTK Gram matrix of `netFromParams` decomposes into the sum of the
input-weight Gram matrix and the readout Gram matrix (empirical covariance). -/
theorem empiricalNTKMatrix_netFromParams_apply (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n) :
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n) :
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n) :
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
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ x)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [innerProduct_scaled_input]

lemma netFromParams_scaled_input_div (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((unpackW θ i ⊙ x) / Real.sqrt (d : ℝ)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [innerProduct_scaled_input_div]

lemma gradW_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n) (j : Fin d) :
    gradW φ n d (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) θ i j =
      ((n : ℝ)⁻¹.sqrt * (Real.sqrt (d : ℝ))⁻¹) *
        (unpackA θ i * deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⊙ x)) * x j) := by
  dsimp [gradW]
  rw [innerProduct_scaled_input]
  ring

lemma gradA_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (i : Fin n) :
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
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (θ θ₀ : EuclideanSpace ℝ (Fin (paramDim n d)))
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
    (C₀ C₁ : ℝ) (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : Differentiable ℝ φ) (hφ_meas : Measurable φ) (hderiv_meas : Measurable (deriv φ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ E : Set (((Fin n → Fin d → ℝ) × (Fin n → ℝ))),
      MeasurableSet E ∧ (initMeasure n d).real E ≥ 1 - 2 * δ ∧
      ∀ p ∈ E,
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          Real.sqrt ((m : ℝ) * C₀ ^ 2 +
            (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) ∧
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)) := by
  have hE1 := outputJacobian_netFromParams_frobenius_norm_concentration φ n d m hn X C₀ C₁
    hC₀ hC₁_bdd hφ hδ
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
        Real.sqrt ((m : ℝ) * C₀ ^ 2 +
          (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ)} := by
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
    (C₀ C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ) {δ : ℝ}
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ))
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (r L_J M : ℝ) (hr_nonneg : 0 ≤ r) (hL_J : 0 ≤ L_J)
    (hM_ge : Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) + L_J * r ≤ M)
    (hL_J_ge : Real.sqrt (∑ α : Fin m,
        (2 * (Real.sqrt (2 * Real.log (2 * n / δ)) + r) ^ 2 * C₂ ^ 2 *
          (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ) ≤ L_J) :
    (∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ‖ ≤ M) ∧
    (∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)), ‖θ - packParams p.1 p.2‖ ≤ r →
      ‖outputJacobian (netFromParams φ n d) X θ -
        outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
          L_J * ‖θ - packParams p.1 p.2‖) := by
  set θ₀ := packParams p.1 p.2 with hθ₀_def
  set R₀ : ℝ := Real.sqrt (2 * Real.log (2 * n / δ)) with hR₀_def
  set M₀ : ℝ := Real.sqrt ((m : ℝ) * C₀ ^ 2 +
      (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) with hM₀_def
  have hR₀_i : ∀ i : Fin n, |unpackA θ₀ i| ≤ R₀ := by
    intro i
    have hival : unpackA θ₀ i = p.2 i := by
      rw [hθ₀_def]; exact congrFun (unpackA_packParams p.1 p.2) i
    rw [hival]; exact hp2 i
  -- Gap 4, applied on the ball of radius `r`: the Jacobian is `L_J`-Lipschitz there, since
  -- every `θ` with `‖θ - θ₀‖ ≤ r` has readout weights bounded by `R₀ + r` (deterministic
  -- ball-propagation of the entrywise concentration bound, `abs_unpackA_le_of_displacement`).
  have hJ_lip_ball : ∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)), ‖θ - θ₀‖ ≤ r →
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
  have hJ_bdd_ball : ∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)), ‖θ - θ₀‖ ≤ r →
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
    (C₀ C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ}
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ))
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : GFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) + L_J * r ≤ M)
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
  obtain ⟨hJ_bdd_ball, hJ_lip_ball⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn X C₀ C₁
    C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ p hp1 hp2 r L_J M hr_nonneg hL_J hM_ge
    hL_J_ge
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
    (C₀ C₁ C₂ : ℝ) (hC₁_bdd : ∀ z, |deriv φ z| ≤ C₁)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hφ : Differentiable ℝ φ)
    (hm : 0 < (m : ℝ)) {δ : ℝ}
    (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (hp1 : ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤
      Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ))
    (hp2 : ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ)))
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d))) (lambda_min₀ r C M L_J : ℝ)
    (hflow : GFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) θ_traj)
    (hdiff : ∀ t : ℝ, ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => netFromParams φ n d (X β) θ') (θ_traj t))
    (hlam₀ : 0 < lambda_min₀) (hr_nonneg : 0 ≤ r) (hCr : C < r) (hM : 0 ≤ M) (hL_J : 0 ≤ L_J)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix (netFromParams φ n d) X (packParams p.1 p.2)) *ᵥ v.ofLp))
    (hM_ge : Real.sqrt ((m : ℝ) * C₀ ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ) + L_J * r ≤ M)
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
  (lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₀ C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm p hp1 hp2 θ_traj lambda_min₀ r C M L_J
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
        ∀ (θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)))
          (lambda_min₀ r C M L_J : ℝ),
          GFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ_traj →
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
    φ n d m hn X C₀ C₁ hC₀ hC₁_bdd hφ hφ_meas hderiv_meas hδ hδ1
  refine hE.trans (MeasureTheory.measureReal_mono ?_)
  intro p hp
  obtain ⟨hp1, hp2⟩ := hpE p hp
  intro θ_traj lambda_min₀ r C M L_J hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀
    hM_ge hL_J_ge h_ball_gap hC_ge t ht
  exact freeze_bound_of_initial_jacobian_and_readout_bounds φ n d m hn X y C₀ C₁ C₂ hC₁_bdd
    hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ hm p hp1 hp2 θ_traj lambda_min₀ r C M L_J hflow
    hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀ hM_ge hL_J_ge h_ball_gap hC_ge t ht

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

/-- **Smooth bounded activation.** The bundled activation hypotheses shared by the paper-facing
bootstrap theorems: `φ` is differentiable with bounded value (`C₀`), bounded derivative (`C₁`) and
`C₂`-Lipschitz derivative. Every other consequence used by those proofs (`C₁, C₂ ≥ 0`, Lipschitzness
of `φ`, measurability of `deriv φ`, `L²` integrability against Gaussians) is derived from these
four facts. Lower-level deterministic lemmas keep taking the unbundled hypotheses they use. -/
structure BoundedSmoothActivation (φ : ℝ → ℝ) (C₀ C₁ C₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ φ
  bdd : ∀ z, |φ z| ≤ C₀
  deriv_bdd : ∀ z, |deriv φ z| ≤ C₁
  deriv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|

/-- Under the global derivative bounds, `φ` and `deriv φ` are (locally) Lipschitz. -/
private lemma activation_locallyLipschitz {φ : ℝ → ℝ} {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂) :
    LocallyLipschitz φ ∧ LocallyLipschitz (deriv φ) := by
  obtain ⟨hφ, -, hC₁, hderiv_lip⟩ := hact
  obtain ⟨-, -, hφlip, -⟩ := activation_regularity_of_bounds φ _ _ hC₁ hderiv_lip hφ
  exact ⟨(LipschitzWith.of_dist_le' (K := C₁) fun x y => by
      simpa [Real.dist_eq] using hφlip x y).locallyLipschitz,
    (LipschitzWith.of_dist_le' (K := C₂) fun x y => by
      simpa [Real.dist_eq] using hderiv_lip x y).locallyLipschitz⟩

/-- **Measurable good event for global positive-gap lazy training, with all bootstrap constants
discharged.** Assume a smooth
activation with bounded value, bounded derivative and Lipschitz derivative, and that the limiting
kernel satisfies `K_∞ ≥ lambda_inf • 1` with `lambda_inf > 0`. For every `δ ∈ (0, 1]` and `ε > 0`
there are a deterministic sequence `freezeRate n → 0` and a width `N` such that for every `n ≥ N`,
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
theorems, this is an a priori estimate for any `GFTrajectory`. -/
theorem exists_measurableSet_global_lazy_training_event
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n ≥ N, freezeRate n ≤ K₀ * Real.sqrt (Real.log n / n)) ∧
      ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - 2 * ε ∧ ∀ p ∈ E,
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
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
  obtain ⟨hφ, hC₀, hC₁_bdd, hderiv_lip⟩ := hact
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  -- Consequences of the global derivative bounds, so callers need not supply them.
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  -- `L²` integrability of the activation-side observables follows from boundedness.
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) := fun α =>
    memLp_two_gaussianRow_comp_of_bounded φ hmeasφ hC₀ (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⊙ Xs α) * φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) := fun α β =>
    memLp_two_gaussianRow_mul_comp_of_bounded φ hmeasφ hC₀ (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⊙ Xs α) * deriv φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => memLp_two_gaussianRow_mul_comp_of_bounded (deriv φ) hderiv_meas hC₁_bdd (Xs α)
      (Xs β)
  -- Initial residual radius and initial spectral-gap failure.
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hU_ev := (tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ hderiv_meas X
    hφ_L2 hdφ_L2 (half_pos hlambda_inf)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  -- Deterministic bootstrap constants.
  set M₀ : ℝ := Real.sqrt ((m : ℝ) * C₀ ^ 2 +
    (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, Xs α j ^ 2) / δ) with hM₀
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
  have hc : 0 < min 1 (lambda_inf / (8 * M)) := lt_min one_pos (by positivity)
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < min 1 (lambda_inf / (8 * M)) := by
    exact (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact hc))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_gt_atTop 0).and (hsmall.and hU_ev))
  obtain ⟨A, hA, hAev⟩ := jacobianLipschitzScale_le_sqrt_log_div Xs C₁ C₂ hδ r
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hAev
  refine ⟨fun n => 2 * M * ℓ n * C, max N N₂, hrate, ⟨2 * M * A * C, by positivity, fun n hn => ?_⟩,
    fun n hn => ?_⟩
  · calc 2 * M * ℓ n * C ≤ 2 * M * (A * Real.sqrt (Real.log n / n)) * C := by
          gcongr; exact hN₂ n ((le_max_right _ _).trans hn)
      _ = 2 * M * A * C * Real.sqrt (Real.log n / n) := by ring
  obtain ⟨hn0, hsm, hU⟩ := hN n ((le_max_left _ _).trans hn)
  obtain ⟨E, hEm, hEμ, hEp⟩ := exists_measurableSet_initial_jacobian_and_readout_bounds
    φ n d m hn0 Xs C₀ C₁ hC₀ hC₁_bdd hφ hmeasφ hderiv_meas hδ hδ1
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
  have hGc : (initMeasure n d).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ ≤ 2 * δ + ε + ε :=
    calc (initMeasure n d).real (E ∩ Uᶜ ∩ Tᶜ)ᶜ
        ≤ (initMeasure n d).real (E ∩ Uᶜ)ᶜ + (initMeasure n d).real Tᶜᶜ :=
          measureReal_compl_inter_le _ _ _
      _ ≤ ((initMeasure n d).real Eᶜ + (initMeasure n d).real Uᶜᶜ) +
            (initMeasure n d).real Tᶜᶜ := by
          gcongr; exact measureReal_compl_inter_le _ _ _
      _ ≤ 2 * δ + ε + ε := by rw [compl_compl, compl_compl]; linarith
  refine ⟨E ∩ Uᶜ ∩ Tᶜ, (hEm.inter hUm.compl).inter hTm.compl,
    by linarith [one_sub_le_measureReal_of_measureReal_compl_le _ hGc], ?_⟩
  rintro p ⟨⟨hpE, hpU⟩, hpT⟩
  obtain ⟨hp1, hp2⟩ := hEp p hpE
  have hrr : ∀ v : EuclideanSpace ℝ (Fin m), (lambda_inf / 2) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d) Xs (packParams p.1 p.2) *ᵥ v.ofLp) :=
    fun v => initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le φ X n p lambda_inf
      hK_gap (not_le.1 (show ¬ (lambda_inf / 2 ≤ _) from hpU)).le v
  have hres : ‖trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)‖ ≤ R :=
    not_lt.1 (show ¬ (R < _) from hpT)
  intro θ_traj hflow
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  have hg := lazy_training_global_bounds_of_initial_jacobian_and_readout_bounds φ n d m hn0 Xs y
    C₀ C₁ C₂ hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ (Nat.cast_pos.2 hm) p hp1 hp2
    θ_traj (lambda_inf / 2) r C M (ℓ n) hflow hdiff (half_pos hlambda_inf) (by positivity)
    (lt_add_one C) hM_pos.le (hℓ_nonneg n) hrr
    (by linarith [hsm.le.trans (min_le_left _ _)]) le_rfl
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
  refine ⟨fun t ht => ?_, tendsto_zero_of_le_mul_exp_neg (by positivity)
    (fun t _ => by unfold mseLoss; positivity) hloss_decay⟩
  obtain ⟨-, hray, hdrift, hres_d, -⟩ := hg t ht
  refine ⟨fun v => ?_, hdrift, ?_, hloss_decay t ht⟩
  · have := hray v
    rwa [show lambda_inf / 2 / 2 = lambda_inf / 4 by ring] at this
  · rwa [show -(lambda_inf / 2 / 2 / (m : ℝ)) * t = -(lambda_inf / (4 * (m : ℝ))) * t by ring]
      at hres_d
/-- **Kernel freeze on `[0, ∞)` from a positive limiting gap.** The kernel-drift component of
`exists_measurableSet_global_lazy_training_event`: with probability at least
`1 - 2 * δ - 2 * ε` every gradient flow keeps the empirical NTK within `freezeRate n → 0` of its
initial value for all `t ≥ 0`. -/
theorem exists_kernel_freeze_event_of_positive_gap
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
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
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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

/-- **Single-confidence form of `exists_kernel_freeze_event_of_positive_gap`.** For every
confidence level `η ∈ (0, 1]` there are a deterministic drift rate `freezeRate n → 0` and a width
`N` such that for `n ≥ N`, with `initMeasure n d`-probability at least `1 - η`, every gradient flow
from `packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value for all
`t ≥ 0`. This is the main theorem with `δ = ε = η / 4`.

This is an a priori estimate for any `GFTrajectory`; it does not assert that gradient flows
exist. -/
theorem exists_kernel_freeze_event_of_positive_gap_of_confidence
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
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

/-- **Measurable good event for the finite-horizon kernel freeze (no spectral gap).** Assume a
smooth activation with bounded value, bounded derivative and Lipschitz derivative. For every horizon
`T ≥ 0`, `δ ∈ (0, 1]` and `ε > 0` there are a radius `R ≥ 0`, a deterministic sequence
`freezeRate n → 0` and a width `N` such that for `n ≥ N` there is a *measurable* event `E` of
`initMeasure n d`-probability at least `1 - 2 * δ - ε` on which the initial residual has norm at
most `R` and every gradient flow from `packParams W a` keeps the empirical NTK within
`freezeRate n` of its initial value on `[0, T]`.

Unlike the positive-gap event, no lower bound on the spectrum of the limiting kernel is assumed:
positive semidefiniteness bounds the residual by its initial size
(`finite_horizon_kernel_freeze_bound`), the initial residual is controlled by
`exists_initial_residual_radius`, and the displacement radius `r = C + 1` with `C = T * M * R / m`
depends on `T`. Exposing a measurable event (rather than only its measure) lets later arguments
intersect it with other events and take complements. This is an a priori estimate for any
`GFTrajectory`; it does not assert that gradient flows exist. -/
theorem exists_measurableSet_finite_horizon_kernel_freeze
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (R : ℝ) (freezeRate : ℕ → ℝ) (N : ℕ), 0 ≤ R ∧
      Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      ∃ E : Set ((Fin n → Fin d → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧
        (initMeasure n d).real E ≥ 1 - 2 * δ - ε ∧
        ∀ p ∈ E,
          ‖trainingResidual (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y (packParams p.1 p.2)‖ ≤ R ∧
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) θ_traj →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              ‖empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ_traj t) -
                empiricalNTKMatrix (netFromParams φ n d)
                  (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2)‖ ≤
                freezeRate n := by
  obtain ⟨hφ, hC₀, hC₁_bdd, hderiv_lip⟩ := hact
  set Xs : Fin m → Fin d → ℝ := fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j with hXs
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨hC₁_nonneg, hC₂_nonneg, hφ_lip, hderiv_meas⟩ :=
    activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) := fun α =>
    memLp_two_gaussianRow_comp_of_bounded φ hmeasφ hC₀ (Xs α)
  obtain ⟨R, hR_nonneg, hR⟩ := exists_initial_residual_radius φ X y hmeasφ hφ_out_L2
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  -- Deterministic bootstrap constants; the displacement target `C` grows linearly with `T`.
  set M₀ : ℝ := Real.sqrt ((m : ℝ) * C₀ ^ 2 +
    (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, Xs α j ^ 2) / δ) with hM₀
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
  have hsmall : ∀ᶠ n in Filter.atTop, ℓ n * r < 1 :=
    (hℓ.mul_const r).eventually (gt_mem_nhds (by rw [zero_mul]; exact one_pos))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.eventually_gt_atTop 0).and hsmall)
  refine ⟨R, fun n => 2 * M * ℓ n * C, N, hR_nonneg, hrate, fun n hn => ?_⟩
  obtain ⟨hn0, hsm⟩ := hN n hn
  obtain ⟨E, hEm, hEμ, hEp⟩ := exists_measurableSet_initial_jacobian_and_readout_bounds
    φ n d m hn0 Xs C₀ C₁ hC₀ hC₁_bdd hφ hmeasφ hderiv_meas hδ hδ1
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
  refine ⟨hres, fun θ_traj hflow t ht => ?_⟩
  have hdiff : ∀ t : ℝ, ∀ β : Fin m, DifferentiableAt ℝ
      (fun θ' => netFromParams φ n d (Xs β) θ') (θ_traj t) := fun t β =>
    (hasFDerivAt_netFromParams φ n d (Xs β) (θ_traj t)
      fun i => hφ.differentiableAt).differentiableAt
  obtain ⟨hJ_bdd, hJ_lip⟩ := jacobian_ball_bounds_of_initial_bounds φ n d m hn0 Xs C₀ C₁ C₂
    hC₁_bdd hφ_lip hderiv_lip hC₁_nonneg hC₂_nonneg hφ p hp1 hp2 r (ℓ n) M hr_nonneg
    (hℓ_nonneg n) (by linarith) le_rfl
  exact finite_horizon_kernel_freeze_bound (netFromParams φ n d) Xs y hflow hdiff T M (ℓ n) r C
    hT hM_pos.le (hℓ_nonneg n) (Nat.cast_pos.2 hm) hr_nonneg (lt_add_one C)
    (by rw [hC]; gcongr) hJ_bdd hJ_lip t ht


/-- **Finite-horizon kernel freeze with no spectral gap.** Consequence of
`exists_measurableSet_finite_horizon_kernel_freeze`: for every horizon `T ≥ 0`, `δ ∈ (0, 1]` and
`ε > 0` there are a deterministic sequence `freezeRate n → 0` and a width `N` such that for `n ≥ N`,
with `initMeasure n d`-probability at least `1 - 2 * δ - ε`, every gradient flow started at
`packParams W a` keeps the empirical NTK within `freezeRate n` of its initial value on `[0, T]`.
No lower bound on the spectrum of the limiting kernel is assumed, in contrast to
`exists_kernel_freeze_event_of_positive_gap`. -/
theorem exists_finite_horizon_kernel_freeze_event
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
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
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (freezeRate : ℕ → ℝ) (N : ℕ), Filter.Tendsto freezeRate Filter.atTop (nhds 0) ∧ ∀ n ≥ N,
      (initMeasure n d).real
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ∀ θ_traj : ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
            GFTrajectory (mseLoss (netFromParams φ n d)
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

**Status.** Proved, with bundled activation hypotheses `BoundedSmoothActivation` in place of
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
  `θ : ∀ n : ℕ, Ω n → ℝ → EuclideanSpace ℝ (Fin (paramDim n d))`
  satisfying:
  - Initial condition and gradient flow ODE: for each `n`, for `initMeasure n d`-almost every `p`,
    `GFTrajectory (mseLoss (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y)`
      `(packParams p.1 p.2) (θ n p)`.
    Here `mseLoss` already contains the `1 / m` normalization, so `GFTrajectory` corresponds to
    `θ' = -∇ mseLoss`, yielding the intended residual dynamics `r'(t) = -(1 / m) K(t) r(t)`.
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
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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

/-- **Kernel stationarity in probability on `[0, T]`.** If the trajectories `θ n p` solve the
gradient-flow ODE for `initMeasure n d`-almost every initialization, then for every `ε₀ > 0` the
probability that the empirical NTK drifts by more than `ε₀` somewhere on `[0, T]` tends to zero.
The event is not shown measurable, so `initMeasure n d` evaluates it as an *outer* probability; the
proof bounds it by the complement of the measurable good event of
`exists_measurableSet_finite_horizon_kernel_freeze`. No spectral gap is assumed. -/
theorem tendsto_measure_kernel_drift_finite_horizon
    {d m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (T : ℝ) (hT : 0 ≤ T)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Filter.Tendsto
      (fun n => (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨c, hc, hcκ⟩ := exists_pos_real_ofReal_le hκ
  obtain ⟨R, freezeRate, N, -, hrate, h⟩ := exists_measurableSet_finite_horizon_kernel_freeze hm φ
    hact X y T hT (δ := min 1 (c / 8)) (ε := c / 2) (lt_min one_pos (by positivity))
    (min_le_left _ _) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop N, hrate.eventually (gt_mem_nhds hε₀)] with n hn hlt
  obtain ⟨E, hEm, hE, hEp⟩ := h n hn
  have hEc : (initMeasure n d).real Eᶜ ≤ c := by
    rw [probReal_compl_eq_one_sub hEm]
    have := min_le_right 1 (c / 8)
    linarith
  have hnull : (initMeasure n d) {p | ¬ GFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)} = 0 :=
    ae_iff.1 (hθ_flow n)
  calc (initMeasure n d) {p | ∃ t ∈ Set.Icc (0 : ℝ) T,
        ε₀ < ‖empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p t) -
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (θ n p 0)‖}
      ≤ (initMeasure n d) (Eᶜ ∪ {p | ¬ GFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p)}) := by
        refine measure_mono fun p hp => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon
        obtain ⟨hpE, hflow⟩ := hcon
        obtain ⟨t, ht, hgt⟩ := hp
        have hb := (hEp p hpE).2 (θ n p) hflow t ht
        rw [hflow.init] at hgt
        linarith
    _ ≤ (initMeasure n d) Eᶜ + 0 := by
        rw [← hnull]; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal c := by
        rw [add_zero]; exact measure_le_ofReal_of_measureReal_le _ hEc
    _ ≤ κ := hcκ

/-- **Actual residual vs. frozen matrix-exponential residual, in probability.** If the trajectories
`θ n p` solve the gradient-flow ODE for almost every initialization, then at each fixed time `t ≥ 0`
the trained residual `r_n(t)` and the frozen residual `exp(-(t / m) K_∞) r_n(0)` are asymptotically
equal: for every `ε₀ > 0`, `initMeasure n d {ε₀ ≤ ‖r_n(t) - exp(-(t / m) K_∞) r_n(0)‖} → 0`
(outer probability, as for `tendsto_measure_kernel_drift_finite_horizon`). No spectral gap is
assumed. -/
theorem tendsto_measure_residual_sub_matrix_exp_finite_horizon
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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
  have hact' := hact
  obtain ⟨hφ, hC₀, hC₁_bdd, hderiv_lip⟩ := hact'
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  obtain ⟨-, -, -, hderiv_meas⟩ := activation_regularity_of_bounds φ C₁ C₂ hC₁_bdd hderiv_lip hφ
  have hφ_out_L2 : ∀ α, MemLp (fun w => φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) := fun α =>
    memLp_two_gaussianRow_comp_of_bounded φ hmeasφ hC₀ (Xs α)
  have hdφ_out_L2 : ∀ α, MemLp (fun w => deriv φ (w ⊙ Xs α)) 2 (gaussianRowMeasure d) := fun α =>
    memLp_two_gaussianRow_comp_of_bounded (deriv φ) hderiv_meas hC₁_bdd (Xs α)
  have hφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => φ (w ⊙ Xs α) * φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) := fun α β =>
    memLp_two_gaussianRow_mul_comp_of_bounded φ hmeasφ hC₀ (Xs α) (Xs β)
  have hdφ_L2 : ∀ α β : Fin m,
      MemLp (fun w => deriv φ (w ⊙ Xs α) * deriv φ (w ⊙ Xs β)) 2 (gaussianRowMeasure d) :=
    fun α β => memLp_two_gaussianRow_mul_comp_of_bounded (deriv φ) hderiv_meas hC₁_bdd (Xs α)
      (Xs β)
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
  have hnull : (initMeasure n d) {p | ¬ GFTrajectory (mseLoss (netFromParams φ n d) Xs y)
      (packParams p.1 p.2) (θ n p)} = 0 := ae_iff.1 (hθ_flow n)
  calc (initMeasure n d) {p | ε₀ ≤ ‖trainingResidual (netFromParams φ n d) Xs y (θ n p t) -
          (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
            (trainingResidual (netFromParams φ n d) Xs y (packParams p.1 p.2)).ofLp) :
            EuclideanSpace ℝ (Fin m))‖}
      ≤ (initMeasure n d) ((Eᶜ ∪ {p | e ≤ ‖empiricalNTKMatrix (netFromParams φ n d) Xs
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖}) ∪
          {p | ¬ GFTrajectory (mseLoss (netFromParams φ n d) Xs y) (packParams p.1 p.2)
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
          (fun u _ => gradient_flow_residual_vector_ode (netFromParams φ n d) Xs y hflow u
            (hdiff u))
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

/-- The residual `θ ↦ r(θ)` of a differentiable-activation two-layer network is continuous in the
packed parameters. -/
private lemma continuous_trainingResidual_netFromParams {m : ℕ} (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (n d : ℕ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) =>
      trainingResidual (netFromParams φ n d) X y θ) := by
  have hnet : ∀ x : Fin d → ℝ, Continuous (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) =>
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
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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
  have hact' := hact
  obtain ⟨hφ, hC₀, -, -⟩ := hact'
  have hmeasφ : Measurable φ := hφ.continuous.measurable
  have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin m) =>
      (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X)) *ᵥ
        v.ofLp) : EuclideanSpace ℝ (Fin m))) :=
    (Matrix.toEuclideanLin (NormedSpace.exp (-(t / (m : ℝ)) • limitingFullNTKMatrix φ X))
      ).continuous_of_finiteDimensional
  have hX := tendstoInDistribution_initial_trainingResidual φ X y hmeasφ fun α =>
    memLp_two_gaussianRow_comp_of_bounded φ hmeasφ hC₀ _
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
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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
everywhere) and `gradientFlow_global_positive_gap_lazy_training_limit` (the constructed family), with
the following differences from the original target below: the uniform finite-width gap is
`lambda_inf / 4` rather than `lambda_inf / 2` (initialization transfers a half-gap and the bootstrap
halves it again; the quarter-gap suffices), the drift rate is `O(√(log n / n))` (the logarithm comes
from the maximum readout weight; the source's `O(n⁻¹ᐟ²)` needs an average-moment argument), the
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
      EuclideanSpace ℝ (Fin (paramDim n d)))
    (hθ_meas : ∀ n t, AEMeasurable (fun p => θ n p t) (initMeasure n d))
    (hθ_flow : ∀ n, ∀ᵐ p ∂(initMeasure n d),
      GFTrajectory (mseLoss (netFromParams φ n d)
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

For a bounded smooth activation, the negative MSE gradient field of the two-layer network is locally
Lipschitz (`locallyLipschitz_neg_gradient_mseLoss_netFromParams`) and its solutions obey a priori
bounds in both time directions (a *linear* Grönwall bound for the readout weights, then a bound for
the hidden weights). The generic theorem `exists_global_flow` therefore yields a two-sided global
flow, continuous in the initial parameters, so every initialization has a `GFTrajectory` and
fixed-time evaluation is continuous, hence measurable, in the initialization. -/

section GradientFlowConstruction

variable {m d n : ℕ}

/-- Coordinates of the negative MSE gradient of the two-layer network in terms of the hidden and
readout blocks. -/
lemma gradient_mseLoss_netFromParams_apply (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) (k : Fin (paramDim n d)) :
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
    LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ) := by
  have hproj : ∀ k : Fin (paramDim n d), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => θ k) := fun k =>
    (ContinuousLinearMap.contDiff (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin (paramDim n d))
      →L[ℝ] ℝ)).locallyLipschitz
  have hpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => unpackW θ i ⊙ X α) := fun i α => by
    unfold innerProduct
    exact locallyLipschitz_finset_sum _ fun j _ => locallyLipschitz_mul_const _ (hproj _)
  have hφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => φ (unpackW θ i ⊙ X α)) :=
    fun i α => hφL.comp (hpre i α)
  have hdφpre : ∀ (i : Fin n) (α : Fin m), LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => deriv φ (unpackW θ i ⊙ X α)) :=
    fun i α => hdφL.comp (hpre i α)
  have hnet : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => netFromParams φ n d (X α) θ) := fun α => by
    simp only [netFromParams_eq_normalized_sum]
    exact locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun i _ =>
      locallyLipschitz_mul_real (hproj _) (hφpre i α))
  have hres : ∀ α : Fin m, LocallyLipschitz
      (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) => netFromParams φ n d (X α) θ - y α) :=
    fun α => by
      simpa only [sub_eq_add_neg] using (hnet α).add (LipschitzWith.const (-(y α))).locallyLipschitz
  refine locallyLipschitz_euclidean_of_coord fun k => ?_
  obtain ⟨p, rfl⟩ := (paramIndexEquiv n d).surjective k
  have hform : ∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)),
      (-gradient (mseLoss (netFromParams φ n d) X y) θ) ((paramIndexEquiv n d) p) =
        -((m : ℝ)⁻¹ * ∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun θ => by
    rw [PiLp.neg_apply, gradient_mseLoss_netFromParams_apply φ hφ]
  simp only [hform]
  have hg : ∀ α : Fin m, LocallyLipschitz (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) =>
      gradParams φ n d (X α) θ ((paramIndexEquiv n d) p)) := fun α => by
    rcases p with ⟨i, j⟩ | i
    · have : ∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inl (i, j))) =
            (n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⊙ X α) * X α j := fun θ =>
        packParams_apply_idxW _ _ i j
      simp only [this]
      exact locallyLipschitz_mul_const _ (locallyLipschitz_mul_real
        (locallyLipschitz_const_mul _ (hproj (idxA i))) (hdφpre i α))
    · have : ∀ θ : EuclideanSpace ℝ (Fin (paramDim n d)),
          gradParams φ n d (X α) θ ((paramIndexEquiv n d) (Sum.inr i)) =
            (n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⊙ X α) := fun θ => packParams_apply_idxA _ _ i
      simp only [this]
      exact locallyLipschitz_const_mul _ (hφpre i α)
  exact (locallyLipschitz_const_mul _ (locallyLipschitz_finset_sum _ fun α _ =>
    locallyLipschitz_mul_real (hres α) (hg α))).neg

section APriori
variable {φ : ℝ → ℝ} {C₀ C₁ : ℝ}

private lemma flow_sqrt_inv_nat_mul_nat (hn : 0 < n) :
    ((n : ℝ)⁻¹).sqrt * (n : ℝ) = Real.sqrt (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_inv]
  field_simp
  exact (Real.sq_sqrt hn'.le).symm

private lemma flow_sqrt_inv_nat_le_one (hn : 0 < n) : ((n : ℝ)⁻¹).sqrt ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_le_one]
  exact inv_le_one_of_one_le₀ hn'

/-- A bounded-activation two-layer network output is bounded by `√n C₀ R` when all readout weights
are bounded by `R`. -/
private lemma abs_netFromParams_le (hC₀ : ∀ z, |φ z| ≤ C₀) (hn : 0 < n) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) {R : ℝ} (hR : ∀ i, |unpackA θ i| ≤ R) :
    |netFromParams φ n d x θ| ≤ Real.sqrt (n : ℝ) * (C₀ * R) := by
  rw [netFromParams_eq_normalized_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsum : |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⊙ x)| ≤ (n : ℝ) * (C₀ * R) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin n, |unpackA θ i * φ (unpackW θ i ⊙ x)| ≤ ∑ _i : Fin n, R * C₀ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hR i) (hC₀ _) (abs_nonneg _) ((abs_nonneg _).trans (hR i))
      _ = (n : ℝ) * (C₀ * R) := by simp [mul_comm]
  calc ((n : ℝ)⁻¹).sqrt * |∑ i : Fin n, unpackA θ i * φ (unpackW θ i ⊙ x)|
      ≤ ((n : ℝ)⁻¹).sqrt * ((n : ℝ) * (C₀ * R)) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = Real.sqrt (n : ℝ) * (C₀ * R) := by rw [← mul_assoc, flow_sqrt_inv_nat_mul_nat hn]

private lemma flow_sqrt_nat_mul_sqrt_inv_nat (hn : 0 < n) :
    Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹).sqrt = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_inv]
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 hn').ne'

/-- Readout coordinates of the MSE gradient grow at most linearly in the sup norm `R` of the readout
weights, uniformly in the hidden weights. -/
private lemma abs_gradient_mseLoss_idxA_le (hφ : Differentiable ℝ φ) (hC₀ : ∀ z, |φ z| ≤ C₀)
    (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, |unpackA θ i| ≤ R) (i : Fin n) :
    |gradient (mseLoss (netFromParams φ n d) X y) θ (idxA i)| ≤
      C₀ ^ 2 * R + C₀ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |y α|) := by
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0)
  set s : ℝ := ((n : ℝ)⁻¹).sqrt with hs
  have hs1 : s ≤ 1 := flow_sqrt_inv_nat_le_one hn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn := flow_sqrt_nat_mul_sqrt_inv_nat hn
  rw [gradient_mseLoss_netFromParams_apply φ hφ, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹)]
  have hterm : ∀ α : Fin m, |(netFromParams φ n d (X α) θ - y α) *
      gradParams φ n d (X α) θ (idxA i)| ≤ C₀ ^ 2 * R + C₀ * |y α| := by
    intro α
    have hg : gradParams φ n d (X α) θ (idxA i) = s * φ (unpackW θ i ⊙ X α) :=
      packParams_apply_idxA _ _ i
    rw [hg, abs_mul, abs_mul, abs_of_nonneg hs0]
    have h1 : |netFromParams φ n d (X α) θ - y α| ≤ Real.sqrt (n : ℝ) * (C₀ * R) + |y α| :=
      (abs_sub _ _).trans (add_le_add (abs_netFromParams_le hC₀ hn (X α) θ hR) le_rfl)
    have h2 : s * |φ (unpackW θ i ⊙ X α)| ≤ s * C₀ := mul_le_mul_of_nonneg_left (hC₀ _) hs0
    calc |netFromParams φ n d (X α) θ - y α| * (s * |φ (unpackW θ i ⊙ X α)|)
        ≤ (Real.sqrt (n : ℝ) * (C₀ * R) + |y α|) * (s * C₀) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C₀ ^ 2 * R * (Real.sqrt (n : ℝ) * s) + C₀ * (s * |y α|) := by ring
      _ ≤ C₀ ^ 2 * R + C₀ * |y α| := by
          rw [hsn, mul_one]
          have : s * |y α| ≤ |y α| := mul_le_of_le_one_left (abs_nonneg _) hs1
          nlinarith [mul_le_mul_of_nonneg_left this hC₀0]
  calc (m : ℝ)⁻¹ * |∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
        gradParams φ n d (X α) θ (idxA i)|
      ≤ (m : ℝ)⁻¹ * ∑ α : Fin m, (C₀ ^ 2 * R + C₀ * |y α|) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun α _ => hterm α)) (by positivity)
    _ = (m : ℝ)⁻¹ * (m : ℝ) * (C₀ ^ 2 * R) + C₀ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |y α|) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ C₀ ^ 2 * R + C₀ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |y α|) := by
        have : (m : ℝ)⁻¹ * (m : ℝ) ≤ 1 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · simp [h]
          · rw [inv_mul_cancel₀ (by exact_mod_cast h.ne')]
        nlinarith [mul_nonneg (sq_nonneg C₀) hR0]

/-- Hidden-weight coordinates of the MSE gradient grow at most quadratically in the sup norm `R` of
the readout weights. -/
private lemma abs_gradient_mseLoss_idxW_le (hφ : Differentiable ℝ φ) (hC₀ : ∀ z, |φ z| ≤ C₀)
    (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin (paramDim n d))) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, |unpackA θ i| ≤ R) (i : Fin n) (j : Fin d) :
    |gradient (mseLoss (netFromParams φ n d) X y) θ (idxW i j)| ≤
      (1 + R) ^ 2 * (C₁ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |X α j| * (C₀ + |y α|))) := by
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0)
  have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ 0)
  set s : ℝ := ((n : ℝ)⁻¹).sqrt with hs
  have hs1 : s ≤ 1 := flow_sqrt_inv_nat_le_one hn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn := flow_sqrt_nat_mul_sqrt_inv_nat hn
  rw [gradient_mseLoss_netFromParams_apply φ hφ, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹)]
  have hterm : ∀ α : Fin m, |(netFromParams φ n d (X α) θ - y α) *
      gradParams φ n d (X α) θ (idxW i j)| ≤
        (1 + R) ^ 2 * (C₁ * (|X α j| * (C₀ + |y α|))) := by
    intro α
    have hg : gradParams φ n d (X α) θ (idxW i j) =
        s * unpackA θ i * deriv φ (unpackW θ i ⊙ X α) * X α j := packParams_apply_idxW _ _ i j
    rw [hg, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0]
    have h1 : |netFromParams φ n d (X α) θ - y α| ≤ Real.sqrt (n : ℝ) * (C₀ * R) + |y α| :=
      (abs_sub _ _).trans (add_le_add (abs_netFromParams_le hC₀ hn (X α) θ hR) le_rfl)
    have h2 : s * |unpackA θ i| * |deriv φ (unpackW θ i ⊙ X α)| * |X α j| ≤
        s * R * C₁ * |X α j| := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left (hR i) hs0) (hC₁ (unpackW θ i ⊙ X α))
        (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have hx0 := abs_nonneg (X α j)
    have hy0 := abs_nonneg (y α)
    calc |netFromParams φ n d (X α) θ - y α| *
          (s * |unpackA θ i| * |deriv φ (unpackW θ i ⊙ X α)| * |X α j|)
        ≤ (Real.sqrt (n : ℝ) * (C₀ * R) + |y α|) * (s * R * C₁ * |X α j|) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = R * C₁ * |X α j| * (C₀ * R + s * |y α|) := by
          have : Real.sqrt (n : ℝ) * s = 1 := hsn
          calc _ = R * C₁ * |X α j| * (C₀ * R * (Real.sqrt (n : ℝ) * s) + s * |y α|) := by ring
            _ = _ := by rw [this, mul_one]
      _ ≤ (1 + R) ^ 2 * (C₁ * (|X α j| * (C₀ + |y α|))) := by
          have hsy : s * |y α| ≤ |y α| := mul_le_of_le_one_left hy0 hs1
          have hc : C₀ * R + s * |y α| ≤ (1 + R) * (C₀ + |y α|) := by nlinarith
          calc R * C₁ * |X α j| * (C₀ * R + s * |y α|)
              ≤ R * C₁ * |X α j| * ((1 + R) * (C₀ + |y α|)) :=
                mul_le_mul_of_nonneg_left hc (by positivity)
            _ ≤ (1 + R) * C₁ * |X α j| * ((1 + R) * (C₀ + |y α|)) := by
                gcongr; linarith
            _ = _ := by ring
  calc (m : ℝ)⁻¹ * |∑ α : Fin m, (netFromParams φ n d (X α) θ - y α) *
        gradParams φ n d (X α) θ (idxW i j)|
      ≤ (m : ℝ)⁻¹ * ∑ α : Fin m, (1 + R) ^ 2 * (C₁ * (|X α j| * (C₀ + |y α|))) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun α _ => hterm α)) (by positivity)
    _ = (1 + R) ^ 2 * (C₁ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |X α j| * (C₀ + |y α|))) := by
        simp only [← Finset.mul_sum]
        ring

open Set Metric in
/-- **A priori bound for the gradient-flow ODE of the two-layer network (either time direction).**
Any solution of `θ' = σ (-∇L)(θ)` (`|σ| = 1`) on `[0, S]`, `S ≤ T`, starting in the ball of radius
`r`, stays in a ball whose radius depends only on `T`, `r` and the data. Proof: for a bounded
activation the readout weights satisfy a *linear* differential inequality in their sup norm
(`abs_gradient_mseLoss_idxA_le`), so Grönwall bounds them on `[0, T]`, and then the hidden-weight
velocities are bounded by `abs_gradient_mseLoss_idxW_le`, hence hidden weights move by at most
`D T`. -/
private theorem apriori_bound_neg_gradient (hφ : Differentiable ℝ φ) (hC₀ : ∀ z, |φ z| ≤ C₀)
    (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hn : 0 < n)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (σ : ℝ) (hσ : |σ| = 1) (T r : ℝ) :
    ∃ ρ : ℝ, ∀ (θ : ℝ → EuclideanSpace ℝ (Fin (paramDim n d))) (S : ℝ), 0 ≤ S → S ≤ T →
      ‖θ 0‖ ≤ r → (∀ t ∈ Icc 0 S, HasDerivWithinAt θ
        (σ • (-gradient (mseLoss (netFromParams φ n d) X y) (θ t))) (Icc 0 S) t) → ‖θ S‖ ≤ ρ := by
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0)
  have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ 0)
  set Ka : ℝ := C₀ * ((m : ℝ)⁻¹ * ∑ α : Fin m, |y α|) with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  set KW : ℝ := C₁ * ∑ j : Fin d, ((m : ℝ)⁻¹ * ∑ α : Fin m, |X α j| * (C₀ + |y α|)) with hKW
  have hKW0 : 0 ≤ KW := by positivity
  set T' : ℝ := max T 0 with hT'
  set Ra : ℝ := gronwallBound (max r 0) (C₀ ^ 2) Ka T' with hRa
  have hδ0 : 0 ≤ max r 0 := le_max_right _ _
  have hRa0 : 0 ≤ Ra := by
    have := gronwallBound_mono hδ0 hKa0 (sq_nonneg C₀) (le_max_right T 0 : (0 : ℝ) ≤ T')
    have h0 : gronwallBound (max r 0) (C₀ ^ 2) Ka 0 = max r 0 := gronwallBound_x0 _ _ _
    rw [hRa]; linarith
  set D : ℝ := (1 + Ra) ^ 2 * KW with hD
  have hD0 : 0 ≤ D := by positivity
  set B : ℝ := max Ra (max r 0 + D * T') with hB
  refine ⟨(paramDim n d : ℝ) * B, ?_⟩
  intro θ S hS0 hST hr0 hsol
  have hcoord : ∀ (k : Fin (paramDim n d)), ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt
      (fun s => θ s k) (σ * (-(gradient (mseLoss (netFromParams φ n d) X y) (θ t)) k))
      (Icc 0 S) t := fun k t ht => by
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin (paramDim n d)) →L[ℝ] ℝ).hasFDerivAt
      |>.comp_hasDerivWithinAt t (hsol t ht)
    exact this.congr_deriv (by simp)
  set f : ℝ → (Fin n → ℝ) := fun t i => θ t (idxA i) with hf
  set f' : ℝ → (Fin n → ℝ) := fun t i =>
    σ * (-(gradient (mseLoss (netFromParams φ n d) X y) (θ t)) (idxA i)) with hf'
  have hfd : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (f' t) (Icc 0 S) t := fun t ht =>
    hasDerivWithinAt_pi.2 fun i => hcoord _ t ht
  have hfc : ContinuousOn f (Icc 0 S) := fun t ht => (hfd t ht).continuousWithinAt
  have hfnorm : ∀ t, ∀ i, |unpackA (θ t) i| ≤ ‖f t‖ := fun t i => by
    have := norm_le_pi_norm (f t) i
    rw [Real.norm_eq_abs] at this
    exact this
  have hbound : ∀ t ∈ Ico (0 : ℝ) S, ‖f' t‖ ≤ C₀ ^ 2 * ‖f t‖ + Ka := fun t _ => by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have := abs_gradient_mseLoss_idxA_le hφ hC₀ hn X y (θ t) (norm_nonneg (f t)) (hfnorm t) i
    simpa [hf', Real.norm_eq_abs, abs_mul, hσ] using this
  have hIco : ∀ t ∈ Ico (0 : ℝ) S, Icc (0 : ℝ) S ∈ nhdsWithin t (Ici t) := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have hf0 : ‖f 0‖ ≤ max r 0 := by
    refine (pi_norm_le_iff_of_nonneg hδ0).2 fun i => ?_
    have := PiLp.norm_apply_le (θ 0) (idxA i)
    simp only [hf, Real.norm_eq_abs] at this ⊢
    exact this.trans (hr0.trans (le_max_left _ _))
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f')
    (δ := max r 0) (K := C₀ ^ 2) (ε := Ka) (a := 0) (b := S) hfc
    (fun t ht => (hfd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hIco t ht)) hf0 hbound
  have hfR : ∀ t ∈ Icc (0 : ℝ) S, ‖f t‖ ≤ Ra := fun t ht =>
    (hgron t ht).trans (gronwallBound_mono hδ0 hKa0 (sq_nonneg C₀)
      (by linarith [ht.2, le_max_left T 0] : t - 0 ≤ T'))
  have hW : ∀ (i : Fin n) (j : Fin d), |θ S (idxW i j) - θ 0 (idxW i j)| ≤ D * S := by
    intro i j
    have hb : ∀ t ∈ Icc (0 : ℝ) S,
        ‖σ * (-(gradient (mseLoss (netFromParams φ n d) X y) (θ t)) (idxW i j))‖ ≤ D := by
      intro t ht
      have h1 := abs_gradient_mseLoss_idxW_le hφ hC₀ hC₁ hn X y (θ t) (norm_nonneg (f t))
        (hfnorm t) i j
      have hRt := hfR t ht
      have hj : (m : ℝ)⁻¹ * ∑ α : Fin m, |X α j| * (C₀ + |y α|) ≤
          ∑ j' : Fin d, ((m : ℝ)⁻¹ * ∑ α : Fin m, |X α j'| * (C₀ + |y α|)) :=
        Finset.single_le_sum (f := fun j' => (m : ℝ)⁻¹ * ∑ α : Fin m, |X α j'| * (C₀ + |y α|))
          (fun j' _ => by positivity) (Finset.mem_univ j)
      rw [norm_mul, Real.norm_eq_abs, hσ, one_mul, norm_neg, Real.norm_eq_abs]
      refine h1.trans ?_
      rw [hD, hKW]
      have hsq : (1 + ‖f t‖) ^ 2 ≤ (1 + Ra) ^ 2 := by
        have := norm_nonneg (f t); nlinarith
      exact mul_le_mul hsq (mul_le_mul_of_nonneg_left hj hC₁0) (by positivity) (by positivity)
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => θ s (idxW i j))
      (f' := fun t => σ * (-(gradient (mseLoss (netFromParams φ n d) X y) (θ t)) (idxW i j)))
      (s := Icc (0 : ℝ) S) (x := 0) (y := S) (fun t ht => hcoord _ t ht) hb (convex_Icc 0 S)
      ⟨le_rfl, hS0⟩ ⟨hS0, le_rfl⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg hS0] using this
  have hcoordS : ∀ k : Fin (paramDim n d), |θ S k| ≤ B := by
    intro k
    obtain ⟨p, rfl⟩ := (paramIndexEquiv n d).surjective k
    rcases p with ⟨i, j⟩ | i
    · have h1 := hW i j
      have h0 : |θ 0 (idxW i j)| ≤ max r 0 := by
        have := PiLp.norm_apply_le (θ 0) (idxW i j)
        simp only [Real.norm_eq_abs] at this
        exact this.trans (hr0.trans (le_max_left _ _))
      have hDS : D * S ≤ D * T' := mul_le_mul_of_nonneg_left
        (hST.trans (le_max_left T 0)) hD0
      calc |θ S (paramIndexEquiv n d (Sum.inl (i, j)))|
          ≤ |θ 0 (idxW i j)| + |θ S (idxW i j) - θ 0 (idxW i j)| := by
            have := abs_sub_abs_le_abs_sub (θ S (idxW i j)) (θ 0 (idxW i j)); 
            change |θ S (idxW i j)| ≤ _
            linarith
        _ ≤ B := (add_le_add h0 h1).trans (by rw [hB]; exact le_max_of_le_right (by linarith))
    · have := hfR S ⟨hS0, le_rfl⟩
      have h2 : |θ S (idxA i)| ≤ ‖f S‖ := by
        have := norm_le_pi_norm (f S) i
        simpa [hf, Real.norm_eq_abs] using this
      exact (h2.trans this).trans (le_max_left _ _)
  calc ‖θ S‖ ≤ ∑ k, |θ S k| := norm_euclidean_le_sum_abs _
    _ ≤ ∑ _k : Fin (paramDim n d), B := Finset.sum_le_sum fun k _ => hcoordS k
    _ = (paramDim n d : ℝ) * B := by simp

end APriori

lemma measurable_packParams {n d : ℕ} :
    Measurable (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => packParams p.1 p.2) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun k => ?_)
  rcases h : (paramIndexEquiv n d).symm k with ⟨i, j⟩ | i
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact (measurable_pi_apply i).comp measurable_snd

theorem exists_gradientFlow_of_pos (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) {C₀ C₁ C₂ : ℝ}
    (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hn : 0 < n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (paramDim n d)) → ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
      (∀ θ₀, GFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      ∀ t, Continuous (fun θ₀ => Φ θ₀ t) := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz ⟨hφ, hC₀, hC₁, hderiv_lip⟩
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hφ hφL hdφL X y
  obtain ⟨Φ, hΦ0, hΦd, hΦc⟩ := exists_global_flow
    (fun θ : EuclideanSpace ℝ (Fin (paramDim n d)) =>
      -gradient (mseLoss (netFromParams φ n d) X y) θ)
    (lipschitz_on_ball_of_locallyLipschitz hLL)
    (fun σ hσ T r => apriori_bound_neg_gradient hφ hC₀ hC₁ hn X y σ hσ T r)
  refine ⟨Φ, fun θ₀ => ⟨hΦ0 θ₀, ?_, fun t => by simpa using hΦd θ₀ t⟩, hΦc⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hΦd θ₀ t).differentiableAt, ?_⟩
  have hd : deriv (Φ θ₀) = fun t => -gradient (mseLoss (netFromParams φ n d) X y) (Φ θ₀ t) :=
    funext fun t => (hΦd θ₀ t).deriv
  rw [hd]
  exact hLL.continuous.comp (continuous_iff_continuousAt.2 fun t => (hΦd θ₀ t).continuousAt)

/-- **Every initialization has a gradient flow, continuous in the initialization.** For a bounded
smooth activation and any dataset there is a map `Φ` such that `Φ θ₀` is a `GFTrajectory` of the
MSE loss started at `θ₀` (defined for all times), and `θ₀ ↦ Φ θ₀ t` is continuous for each `t`.
Solutions are unique by `flow_unique_window`'s adapter inside `exists_global_flow`. -/
theorem exists_gradientFlow {φ : ℝ → ℝ} {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ Φ : EuclideanSpace ℝ (Fin (paramDim n d)) → ℝ → EuclideanSpace ℝ (Fin (paramDim n d)),
      (∀ θ₀, GFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ (Φ θ₀)) ∧
      ∀ t, Continuous (fun θ₀ => Φ θ₀ t) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no parameters: the parameter space is a point
    have hsub : ∀ u v : EuclideanSpace ℝ (Fin (paramDim 0 d)), u = v := fun u v => by
      ext k
      exact (Fin.elim0 (by simpa [paramDim] using k) : False).elim
    refine ⟨fun θ₀ _ => θ₀, fun θ₀ => ⟨rfl, contDiff_const, fun t => ?_⟩, fun t => continuous_id⟩
    rw [show -gradient (mseLoss (netFromParams φ 0 d) X y) θ₀ = 0 from hsub _ _]
    exact hasDerivAt_const t θ₀
  · exact exists_gradientFlow_of_pos φ hact.differentiable hact.bdd hact.deriv_bdd
      hact.deriv_lip hn X y

/-- **Uniqueness of the gradient flow.** Two gradient-flow trajectories of the MSE loss of the
two-layer network from the same initialization coincide (for a bounded smooth activation). -/
theorem gradientFlow_unique {φ : ℝ → ℝ} {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (paramDim n d))}
    {f g : ℝ → EuclideanSpace ℝ (Fin (paramDim n d))}
    (hf : GFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ f)
    (hg : GFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ g) : f = g := by
  obtain ⟨hφL, hdφL⟩ := activation_locallyLipschitz hact
  have hLL := locallyLipschitz_neg_gradient_mseLoss_netFromParams (n := n) φ hact.differentiable
    hφL hdφL X y
  exact flow_unique _ (lipschitz_on_ball_of_locallyLipschitz hLL) (fun t => hf.ode t)
    (fun t => hg.ode t) (hf.init.trans hg.init.symm)

/-- **A measurable family of gradient-flow trajectories over the initialization laws.** There is a
family `θ n p` such that for *every* width `n` and *every* initialization `p`, `θ n p` is a
gradient flow of the MSE loss started at `packParams p.1 p.2`, and each fixed-time evaluation is
measurable in `p`. This discharges the hypotheses `hθ_flow` (in fact everywhere, not only almost
everywhere) and `hθ_meas` of the finite-horizon and global theorems. -/
theorem exists_gradientFlow_family {φ : ℝ → ℝ} {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂) (d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (paramDim n d)),
      (∀ n p, GFTrajectory (mseLoss (netFromParams φ n d) X y) (packParams p.1 p.2) (θ n p)) ∧
      ∀ n t, Measurable (fun p => θ n p t) := by
  choose Φ hΦ hΦc using fun n : ℕ => exists_gradientFlow hact n d m X y
  exact ⟨fun n p => Φ n (packParams p.1 p.2), fun n p => hΦ n _,
    fun n t => (hΦc n t).measurable.comp measurable_packParams⟩

/-- **Finite-horizon training limit for the constructed gradient flow (no spectral gap, no
trajectory hypotheses).** For a bounded smooth activation, the constructed family of gradient-flow
trajectories `θ n p` (defined for every width and every initialization, measurable in `p`) has:
kernel stationarity in probability on every `[0, T]`, and, at every fixed time `t ≥ 0`, the
trained residual and predictions converge in distribution to the frozen-kernel laws
`exp(-(t / m) K_∞) (G - y)` and `y + exp(-(t / m) K_∞) (G - y)`, `G ~ 𝒩(0, Φ^{(∞)})`. -/
theorem gradientFlow_finite_horizon_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (paramDim n d)),
      (∀ n p, GFTrajectory (mseLoss (netFromParams φ n d)
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
  obtain ⟨θ, hflow, hmeas⟩ := exists_gradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂(initMeasure n d), GFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, hmeas,
    fun T hT ε₀ hε₀ => tendsto_measure_kernel_drift_finite_horizon hm φ hact X y T hT θ hae hε₀,
    fun t ht => tendstoInDistribution_trainingResidual_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hmeas n t).aemeasurable) hae,
    fun t ht => tendstoInDistribution_trainingOutputs_matrix_exp hm hd φ hact X y t ht θ
      (fun n t => (hmeas n t).aemeasurable) hae⟩

/-- **Global positive-gap lazy training limit for the constructed gradient flow.** Under a positive
limiting gap, the constructed family of gradient-flow trajectories (defined for every width and
every initialization, measurable in the initialization) satisfies the conclusion of
`global_positive_gap_lazy_training_limit`: with a measurable initialization event of probability at
least `1 - η`, the uniform quarter-gap, `O(√(log n / n))` kernel drift, exponential residual and
loss decay, and `mseLoss → 0`. No trajectory hypothesis remains. -/
theorem gradientFlow_global_positive_gap_lazy_training_limit
    {d m : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) {C₀ C₁ C₂ : ℝ}
    (hact : BoundedSmoothActivation φ C₀ C₁ C₂)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ θ : ∀ n : ℕ, (Fin n → Fin d → ℝ) × (Fin n → ℝ) → ℝ →
        EuclideanSpace ℝ (Fin (paramDim n d)),
      (∀ n p, GFTrajectory (mseLoss (netFromParams φ n d)
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
  obtain ⟨θ, hflow, hmeas⟩ := exists_gradientFlow_family hact d m
    (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y
  have hae : ∀ n, ∀ᵐ p ∂(initMeasure n d), GFTrajectory (mseLoss (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) y) (packParams p.1 p.2) (θ n p) :=
    fun n => Filter.Eventually.of_forall (hflow n)
  exact ⟨θ, hflow, hmeas, global_positive_gap_lazy_training_limit hm hd φ hact X y lambda_inf
    hlambda_inf hK_gap θ hae hη hη1⟩

end GradientFlowConstruction

end FullTwoLayerTrainingLimit

end

end NTK
