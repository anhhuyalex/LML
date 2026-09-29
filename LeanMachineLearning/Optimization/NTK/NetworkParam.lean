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
- `abs_unpackA_le_of_displacement` : deterministic ball-propagation of an entrywise
  readout-weight bound, needed to turn Gap 4b's at-`θ₀`-only bound into the ball-wide bound
  Gap 4 requires.
- `lazy_training_kernel_freeze_bound_of_gaussian_init` : **Gap 6, the plan's final
  deliverable** - the fully probabilistic end-to-end kernel-freeze bound.
- `chebyshev_entrywise_empiricalNTKMatrix` : finite-width entrywise Chebyshev concentration
  under `initMeasure n d`.
- `chebyshev_matrix_empiricalNTKMatrix` : finite-width matrix Frobenius norm Chebyshev
  concentration under `initMeasure n d`.
- `tendsto_initMeasure_empiricalNTKMatrix_gt_eps` : finite-width convergence in probability of
  the empirical NTK matrix in Frobenius norm under `initMeasure n d`.
-/

namespace NTK

open ConvexOpt MeasureTheory
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
lemma empiricalNTKMatrix_packed_arrowProd_eq_summand {m d : ℕ} (hd : 0 < d)
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
      ENNReal.ofReal (((m : ℝ) ^ 2 * limitingFullNTKMatrixConcentrationConst d φ X) /
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
      ((m : ℝ) ^ 2 * limitingFullNTKMatrixConcentrationConst d φ X) / ((n : ℝ) * ε ^ 2) := by
    dsimp [limitingFullNTKMatrixConcentrationConst]
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
theorem tendsto_initMeasure_empiricalNTKMatrix_gt_eps
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
  set C := (m : ℝ) ^ 2 * limitingFullNTKMatrixConcentrationConst d φ X
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

end FiniteWidthNTKConcentration


/-! ### Phase 6: End-to-End Kernel-Freeze Bound

Wires Gaps 1-5 together with the Gaussian-initialized two-layer network: Gap 3's Jacobian-norm
concentration and Gap 4b's entrywise readout-weight concentration (both at `θ₀`) combine via a
union bound into one high-probability event; on that event, Gap 4's Lipschitz bound propagates
both the Jacobian norm and the readout-weight bound through the displacement ball (the same
"ball propagation" pattern `rayleigh_quotient_lower_bound_of_displacement`/`h_rr_ball` already use
in `InfiniteNTK.lean`); the result feeds directly into
`lazy_training_kernel_freeze_bound_of_ball_hypotheses`.
-/

/-- A coordinate of a `EuclideanSpace` vector is bounded by its norm - the generic fact behind
propagating an entrywise bound on one sub-block of parameters through a displacement bound on
the whole packed vector. -/
lemma abs_apply_le_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (j : ι) :
    |x.ofLp j| ≤ ‖x‖ := by
  have hsq : (x.ofLp j) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (x.ofLp k)) (Finset.mem_univ j)
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (norm_nonneg x))

/-- Deterministic ball-propagation of an entrywise readout-weight bound: if `θ₀`'s readout
weight `a i` is bounded by `R₀` and `θ` is within displacement `r` of `θ₀`, then `θ`'s readout
weight `a i` is bounded by `R₀ + r`. This is what lets a concentration bound established only at
the random initialization `θ₀` (Gap 4b) supply the uniform-over-a-ball bound Gap 4's Lipschitz
theorem needs. -/
lemma abs_unpackA_le_of_displacement {n d : ℕ} (θ θ₀ : EuclideanSpace ℝ (Fin (paramDim n d)))
    (i : Fin n) (R₀ r : ℝ) (h₀ : |unpackA θ₀ i| ≤ R₀) (hr : ‖θ - θ₀‖ ≤ r) :
    |unpackA θ i| ≤ R₀ + r := by
  have hproj : |(θ - θ₀).ofLp (idxA i)| ≤ ‖θ - θ₀‖ := abs_apply_le_norm (θ - θ₀) (idxA i)
  have heq : unpackA θ i - unpackA θ₀ i = (θ - θ₀).ofLp (idxA i) := by dsimp [unpackA]
  have hdiff : |unpackA θ i - unpackA θ₀ i| ≤ r := heq ▸ hproj.trans hr
  have h1 := abs_le.mp h₀
  have h2 := abs_le.mp hdiff
  rw [abs_le]
  constructor <;> linarith

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
  refine hcombined.trans (MeasureTheory.measureReal_mono ?_)
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  intro θ_traj lambda_min₀ r C M L_J hflow hdiff hlam₀ hr_nonneg hCr hM hL_J h_rr₀
    hM_ge hL_J_ge h_ball_gap hC_ge t ht
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
  exact lazy_training_kernel_freeze_bound_of_ball_hypotheses (netFromParams φ n d) X y hflow
    hdiff M L_J lambda_min₀ r C hM hL_J hm hlam₀ hr_nonneg hCr h_ball_gap hC_ge h_rr₀
    hJ_bdd_ball hJ_lip_ball t ht

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

section FiniteHorizonLimit

/-!
#### Target Theorem 1: Finite-Horizon NTK Training Limit (Phase 0 Target)

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

end FiniteHorizonLimit

section GlobalPositiveGapLimit

/-!
#### Target Theorem 2: Global Positive-Gap Lazy Training Limit (Phase 0 Target)

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

end FullTwoLayerTrainingLimit

end

end NTK
