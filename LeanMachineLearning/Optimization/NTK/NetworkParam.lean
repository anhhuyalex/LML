/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization
public import LeanMachineLearning.Optimization.NTK.Kernel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Two-Layer NTK Parameter Packing and Jacobian Bridge

This module implements Gap 1 of the NTK lazy training program.
It bridges the curried `(W, a)` representation used by `evalSingle`/`evalVector`
in `Initialization.lean` to the flat parameter vector
`θ : EuclideanSpace ℝ (Fin (paramDim n d))` expected by `tangentFeature`,
`outputJacobian`, and `empiricalNTKMatrix` in `Kernel.lean`.

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
-/

namespace NTK

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
    (x - y) ⊙ z = x ⊙ z - y ⊙ z := by
  simp only [innerProduct, Pi.sub_apply, sub_mul]
  rw [← Finset.sum_sub_distrib]

lemma innerProduct_sub_sq_le (d : ℕ) (x y z : Fin d → ℝ) :
    (x ⊙ z - y ⊙ z) ^ 2 ≤ (∑ j : Fin d, (x j - y j) ^ 2) * (∑ j : Fin d, z j ^ 2) := by
  rw [← innerProduct_sub]
  dsimp [innerProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => x j - y j) z

lemma matrix_frobenius_norm_sq {m P : ℕ} (A : Matrix (Fin m) (Fin P) ℝ) :
    ‖A‖ ^ 2 = ∑ α : Fin m, ∑ k : Fin P, (A α k) ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs]
  rw [← Real.sqrt_eq_rpow]
  have hnonneg : 0 ≤ ∑ α : Fin m, ∑ k : Fin P, |A α k| ^ (2 : ℝ) := by
    apply Finset.sum_nonneg
    intro α _
    apply Finset.sum_nonneg
    intro k _
    positivity
  calc
    √(∑ α : Fin m, ∑ k : Fin P, |A α k| ^ (2 : ℝ)) ^ 2 =
        ∑ α : Fin m, ∑ k : Fin P, |A α k| ^ (2 : ℝ) := Real.sq_sqrt hnonneg
    _ = _ := by simp [sq_abs]

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

end

end NTK
