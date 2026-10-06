/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow

/-!
# Two-layer network: parameter packing, gradients and the Jacobian norm

Bridges the curried `(W, a)` representation to the flat parameter vector `θ` expected by
`tangentFeature`, `outputJacobian` and `empiricalNTKMatrix`: `packParams`, `netFromParams`, `gradW`,
`gradA`, the Fréchet derivative and gradient of the packed network, the forward-gradient-flow
coordinate equations, and the Frobenius-norm concentration of the output Jacobian at initialization.

## Main results and proof outline

* `Packing` : `packParams`, `netFromParams`, gradients, coordinate equations, Jacobian norm
  concentration.
- `packParams W a`: Pack weights `W` and readout `a` into a flat parameter vector `θ`.
- Weight and readout coordinates are selected directly with `paramIndexEquiv`.
- `netFromParams φ n d x θ`: Single-output network evaluation from flat parameter `θ`.
- `gradW φ n d x θ`: Gradient block for `W`, evaluated at `(x, θ)`.
- `gradA φ n d x θ`: Gradient block for `a`, evaluated at `(x, θ)`.
- `gradParams φ n d x θ`: Packed gradient vector of `netFromParams`.
- `unpackW_packParams`, `unpackA_packParams`: Left inverse equations.
- `packParams_unpack`: Right inverse equation for the explicit coordinate projections.
- `inner_packParams`: Inner product `⟪packParams W a, v⟫` in terms of components.
- `inner_packParams_packParams`: Inner product `⟪packParams W₁ a₁, packParams W₂ a₂⟫`.
- `hasFDerivAt_netFromParams`: Fréchet derivative of `netFromParams` with respect to `θ`.
- `hasGradientAt_netFromParams`: Gradient of `netFromParams`.
- `tangentFeature_netFromParams`: Closed form for `tangentFeature (netFromParams φ n d) x θ`.
- `unpackW_tangentFeature`, `unpackA_tangentFeature`: Component-wise tangent feature equations.
- `outputJacobian_netFromParams_apply_W`, `outputJacobian_netFromParams_apply_a`:
  Row evaluations of the output Jacobian delegating to `gradW` / `gradA`.
- `forwardGF_readout_hasDerivAt`, `forwardGF_inputWeight_hasDerivAt`:
  Coordinate equations `∂_t a_i`, `∂_t W_{ij}` of the forward gradient flow.
- `outputJacobian_netFromParams_frobenius_norm_concentration` : The
  output Jacobian's Frobenius norm is `O(1)` (width-independent) with probability `≥ 1 - δ`.

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
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

/-- The inverse of `paramIndexEquiv` sends the index of weight `W i j` back to `Sum.inl (i, j)`. -/
@[simp]
lemma paramIndexEquiv_symm_idxW {n d : ℕ} (i : Fin n) (j : Fin d) :
    (paramIndexEquiv n d).symm (paramIndexEquiv n d (Sum.inl (i, j))) = Sum.inl (i, j) :=
  (paramIndexEquiv n d).symm_apply_apply (Sum.inl (i, j))

/-- The inverse of `paramIndexEquiv` sends the index of readout `a i` back to `Sum.inr i`. -/
@[simp]
lemma paramIndexEquiv_symm_idxA {n d : ℕ} (i : Fin n) :
    (paramIndexEquiv n d).symm (paramIndexEquiv n d (Sum.inr i)) = Sum.inr i :=
  (paramIndexEquiv n d).symm_apply_apply (Sum.inr i)

/-- Pack input weights `W` and readout weights `a` into a single flat vector in
`EuclideanSpace ℝ (Fin (n * d + n))`. -/
noncomputable def packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (n * d + n)) :=
  WithLp.toLp 2 (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i)

/-- Private proof implementation for the explicit input-weight coordinate projection. -/
private noncomputable def unpackW {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    Fin n → Fin d → ℝ :=
  fun i j => θ (paramIndexEquiv n d (Sum.inl (i, j)))

/-- Private proof implementation for the explicit readout coordinate projection. -/
private noncomputable def unpackA {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    Fin n → ℝ :=
  fun i => θ (paramIndexEquiv n d (Sum.inr i))

/-- The packed parameter vector has entry `W i j` at `paramIndexEquiv n d (Sum.inl (i, j))`. -/
lemma packParams_apply_idxW {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (i : Fin n) (j : Fin d) :
    packParams W a (paramIndexEquiv n d (Sum.inl (i, j))) = W i j := by
  dsimp [packParams]
  rw [paramIndexEquiv_symm_idxW]

/-- The packed parameter vector has entry `a i` at `paramIndexEquiv n d (Sum.inr i)`. -/
lemma packParams_apply_idxA {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (i : Fin n) :
    packParams W a (paramIndexEquiv n d (Sum.inr i)) = a i := by
  dsimp [packParams]
  rw [paramIndexEquiv_symm_idxA]

/-- Unpacking the weights of a packed parameter vector returns `W`. -/
@[simp]
lemma unpackW_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    (fun i j => packParams W a (paramIndexEquiv n d (Sum.inl (i, j)))) = W := by
  ext i j
  exact packParams_apply_idxW W a i j

/-- Unpacking the readout of a packed parameter vector returns `a`. -/
@[simp]
lemma unpackA_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    (fun i => packParams W a (paramIndexEquiv n d (Sum.inr i))) = a := by
  ext i
  exact packParams_apply_idxA W a i

/-- Packing the unpacked weights and readout of `θ` returns `θ`. -/
@[simp]
lemma packParams_unpack {n d : ℕ} (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    packParams (fun i j => θ (paramIndexEquiv n d (Sum.inl (i, j))) )
      (fun i => θ (paramIndexEquiv n d (Sum.inr i))) = θ := by
  ext k
  dsimp [packParams]
  cases h : (paramIndexEquiv n d).symm k with
  | inl p =>
    rcases p with ⟨i, j⟩
    have h_k : k = paramIndexEquiv n d (Sum.inl (i, j)) := by
      rw [← (paramIndexEquiv n d).apply_symm_apply k, h]
    rw [h_k]
  | inr i =>
    have h_k : k = paramIndexEquiv n d (Sum.inr i) := by
      rw [← (paramIndexEquiv n d).apply_symm_apply k, h]
    rw [h_k]

/-- Packing hidden and readout weights into the parameter vector is continuous: it is a coordinate
rearrangement. -/
lemma continuous_packParams {n d : ℕ} :
    Continuous (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => packParams p.1 p.2) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  rcases h : (paramIndexEquiv n d).symm k with ⟨i, j⟩ | i
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  · exact (continuous_apply i).comp continuous_snd

/-- The continuous linear map `θ ↦ (fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x`. Internal helper. -/
private noncomputable def dotW_CLM {n d : ℕ} (i : Fin n) (x : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ :=
  ∑ j : Fin d, (x j) • EuclideanSpace.proj (paramIndexEquiv n d (Sum.inl (i, j)))

private lemma dotW_CLM_apply {n d : ℕ} (i : Fin n) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    dotW_CLM i x θ = (fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x := by
  simp only [dotW_CLM, sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The inner product `⟪packParams W a, v⟫` expressed as a sum over the
two coordinate blocks. -/
lemma inner_packParams {n d : ℕ} (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin (n * d + n))) :
    ⟪packParams W a, v⟫ =
      (∑ i : Fin n, ∑ j : Fin d, W i j * v (paramIndexEquiv n d (Sum.inl (i, j)))) +
      ∑ i : Fin n, a i * v (paramIndexEquiv n d (Sum.inr i)) := by
  have h_inner := EuclideanSpace.inner_toLp_toLp (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i) v.ofLp
  change ⟪packParams W a, v⟫ = _
  rw [show packParams W a = WithLp.toLp 2 (fun k => match (paramIndexEquiv n d).symm k with
    | Sum.inl (i, j) => W i j
    | Sum.inr i => a i) from rfl]
  rw [← WithLp.toLp_ofLp (p := 2) v]
  rw [h_inner]
  simp only [dotProduct, star_trivial]
  rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  have h_w : ∀ x x_1, v.ofLp (paramIndexEquiv n d (Sum.inl (x, x_1))) * W x x_1 =
      W x x_1 * v (paramIndexEquiv n d (Sum.inl (x, x_1))) := by
    intro i j; ring
  have h_a : ∀ x, v.ofLp (paramIndexEquiv n d (Sum.inr x)) * a x =
      a x * v (paramIndexEquiv n d (Sum.inr x)) := by
    intro i; ring
  simp_rw [h_w, h_a]

/-- Inner product of two packed parameter vectors decomposes into weight-matrix
inner products plus readout-vector inner product. -/
lemma inner_packParams_packParams {n d : ℕ}
    (W₁ W₂ : Fin n → Fin d → ℝ) (a₁ a₂ : Fin n → ℝ) :
    ⟪packParams W₁ a₁, packParams W₂ a₂⟫ =
      (∑ i : Fin n, W₁ i ⬝ᵥ W₂ i) + ∑ i : Fin n, a₁ i * a₂ i := by
  rw [inner_packParams]
  simp_rw [packParams_apply_idxW, packParams_apply_idxA]
  rfl

/-- Single-output evaluation of a two-layer network from a packed parameter vector `θ`. -/
noncomputable def netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : ℝ :=
  evalSingle φ (fun i j => θ (paramIndexEquiv n d (Sum.inl (i, j))))
    (fun i => θ (paramIndexEquiv n d (Sum.inr i))) x

/-- The packed-parameter network is `n^{-1/2} ∑_i a_i φ(w_i ⬝ x)`. -/
lemma netFromParams_eq_normalized_sum (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d x θ = (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, θ (paramIndexEquiv n d (Sum.inr i)) * φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x) :=
  evalSingle_eq_normalized_sum φ (fun i j => θ (paramIndexEquiv n d (Sum.inl (i, j))))
    (fun i => θ (paramIndexEquiv n d (Sum.inr i))) x

/-- The explicit training-output vector of the packed-parameter network is `evalVector φ W a X`. -/
@[simp]
lemma trainingOutputs_netFromParams_packParams (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    WithLp.toLp 2 (fun α => netFromParams φ n d (X α) (packParams W a)) =
      evalVector φ W a X := by
  unfold evalVector netFromParams
  simp only [unpackW_packParams, unpackA_packParams]

/-- The training residual of the packed-parameter network is `evalVector φ W a X - y`. -/
@[simp]
lemma trainingResidual_netFromParams_packParams (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) :
    trainingResidual (netFromParams φ n d) X y (packParams W a) =
      evalVector φ W a X - y := by
  simp only [trainingResidual, trainingOutputs_netFromParams_packParams]


/-- Gradient block for input weights `W`:
`∂f/∂W_{i, j} = n^{-1/2} a_i φ'(W_i ⬝ᵥ x) x_j`. -/
noncomputable def gradW (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : Fin n → Fin d → ℝ :=
  fun i j => (n : ℝ)⁻¹.sqrt * θ (paramIndexEquiv n d (Sum.inr i)) * deriv φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x) * x j

/-- Gradient block for readout weights `a`:
`∂f/∂a_i = n^{-1/2} φ(W_i ⬝ᵥ x)`. -/
noncomputable def gradA (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : Fin n → ℝ :=
  fun i => (n : ℝ)⁻¹.sqrt * φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)

/-- The packed gradient vector in `EuclideanSpace ℝ (Fin (n * d + n))`. -/
noncomputable def gradParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    EuclideanSpace ℝ (Fin (n * d + n)) :=
  packParams (gradW φ n d x θ) (gradA φ n d x θ)

/-- Fréchet derivative of `netFromParams` with respect to parameters `θ`. -/
theorem hasFDerivAt_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    HasFDerivAt (netFromParams φ n d x)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n * d + n)))
        (gradParams φ n d x θ)) θ := by
  have h_comp : ∀ i : Fin n, HasFDerivAt (fun θ => φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x))
      (deriv φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x) • dotW_CLM i x) θ := by
    intro i
    have h_deriv : HasDerivAt φ (deriv φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) (dotW_CLM i x θ) := by
      rw [dotW_CLM_apply]
      exact (hφ i).hasDerivAt
    have h := HasDerivAt.comp_hasFDerivAt θ h_deriv (dotW_CLM i x).hasFDerivAt
    have h_eq : (φ ∘ (dotW_CLM i x)) = (fun θ => φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) := by
      ext θ'
      simp only [Function.comp_apply, dotW_CLM_apply]
    rwa [h_eq] at h
  have h_a : ∀ i : Fin n, HasFDerivAt (fun θ => θ (paramIndexEquiv n d (Sum.inr i)))
      (EuclideanSpace.proj (paramIndexEquiv n d (Sum.inr i)) :
        EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ) θ := by
    intro i
    exact (EuclideanSpace.proj (paramIndexEquiv n d (Sum.inr i)) :
      EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ).hasFDerivAt
  have h_mul : ∀ i : Fin n, HasFDerivAt (fun θ => θ (paramIndexEquiv n d (Sum.inr i)) * φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x))
      ((θ (paramIndexEquiv n d (Sum.inr i))) • (deriv φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x) • dotW_CLM i x) +
       (φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) •
         (EuclideanSpace.proj (paramIndexEquiv n d (Sum.inr i)) :
           EuclideanSpace ℝ (Fin (n * d + n)) →L[ℝ] ℝ)) θ := by
    intro i
    exact (h_a i).mul (h_comp i)
  have h_sum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i (θ : EuclideanSpace ℝ (Fin (n * d + n))) =>
      θ (paramIndexEquiv n d (Sum.inr i)) *
        φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x))
    (fun i _ => h_mul i)
  have h_sum_fun :
      (∑ i ∈ (Finset.univ : Finset (Fin n)),
        fun θ' => θ' (paramIndexEquiv n d (Sum.inr i)) *
          φ ((fun j => θ' (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) =
      (fun θ' => ∑ i : Fin n, θ' (paramIndexEquiv n d (Sum.inr i)) *
        φ ((fun j => θ' (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) := by
    ext θ'
    simp only [Finset.sum_apply]
  rw [h_sum_fun] at h_sum
  have h_scaled := h_sum.const_smul (n : ℝ)⁻¹.sqrt
  have h_net_eq :
      (n : ℝ)⁻¹.sqrt • (fun θ' => ∑ i : Fin n, θ' (paramIndexEquiv n d (Sum.inr i)) *
        φ ((fun j => θ' (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) =
      netFromParams φ n d x := by
    ext θ'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (netFromParams_eq_normalized_sum φ n d x θ').symm
  rw [h_net_eq] at h_scaled
  convert h_scaled using 1
  ext v
  simp only [smul_apply, sum_apply, add_apply, smul_eq_mul, dotW_CLM_apply,
    PiLp.proj_apply, InnerProductSpace.toDual_apply_apply]
  dsimp [gradParams]
  rw [inner_packParams]
  dsimp [gradW, gradA, dotProduct]
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
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    HasGradientAt (netFromParams φ n d x) (gradParams φ n d x θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_netFromParams φ n d x θ hφ

/-- Gradient evaluation lemma for `netFromParams`. -/
theorem gradient_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    gradient (netFromParams φ n d x) θ = gradParams φ n d x θ :=
  (hasGradientAt_netFromParams φ n d x θ hφ).gradient

/-- Equation lemma for `tangentFeature`:
`tangentFeature (netFromParams φ n d) x θ = packParams (gradW ...) (gradA ...)`. -/
theorem tangentFeature_netFromParams (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  gradient_netFromParams φ n d x θ hφ

/-- Equation lemma for `tangentFeature` when `φ` is globally differentiable. -/
theorem tangentFeature_netFromParams_of_differentiable (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (n d : ℕ) (x : Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    tangentFeature (netFromParams φ n d) x θ = gradParams φ n d x θ :=
  tangentFeature_netFromParams φ n d x θ (fun _ => hφ _)

/-- The input-weight block of the tangent feature is `gradW`. -/
@[simp]
lemma unpackW_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    (fun i j => tangentFeature (netFromParams φ n d) x θ
      (paramIndexEquiv n d (Sum.inl (i, j)))) = gradW φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackW_packParams _ _

/-- The readout block of the tangent feature is `gradA`. -/
@[simp]
lemma unpackA_tangentFeature (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ x)) :
    (fun i => tangentFeature (netFromParams φ n d) x θ
      (paramIndexEquiv n d (Sum.inr i))) = gradA φ n d x θ := by
  rw [tangentFeature_netFromParams φ n d x θ hφ]
  exact unpackA_packParams _ _

/-- Output Jacobian entry for `netFromParams` evaluated at its `(i, j)` weight coordinate. -/
lemma outputJacobian_netFromParams_apply_W (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α))
    (α : Fin m) (i : Fin n) (j : Fin d) :
    outputJacobian (netFromParams φ n d) X θ α (paramIndexEquiv n d (Sum.inl (i, j))) =
      gradW φ n d (X α) θ i j := by
  change tangentFeature (netFromParams φ n d) (X α) θ
    (paramIndexEquiv n d (Sum.inl (i, j))) = _
  exact congrFun (congrFun (unpackW_tangentFeature φ n d (X α) θ (hφ α)) i) j

/-- Output Jacobian entry for `netFromParams` evaluated at its `i`-th readout coordinate. -/
lemma outputJacobian_netFromParams_apply_a (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α))
    (α : Fin m) (i : Fin n) :
    outputJacobian (netFromParams φ n d) X θ α (paramIndexEquiv n d (Sum.inr i)) =
      gradA φ n d (X α) θ i := by
  change tangentFeature (netFromParams φ n d) (X α) θ
    (paramIndexEquiv n d (Sum.inr i)) = _
  exact congrFun (unpackA_tangentFeature φ n d (X α) θ (hφ α)) i

/-- **Readout-weight equation of the training flow.** Along a forward gradient flow of the MSE loss
of a two-layer network, at every positive time
  `∂_t a_i = -(1/m) ∑_α r^α ∂f^α/∂a_i = -(1/(m √n)) ∑_α r^α φ(W_i ⬝ᵥ x^α)`,
where `∂f^α/∂a_i = gradA φ n d (x^α) θ i` (`unpackA_tangentFeature`). -/
theorem forwardGF_readout_hasDerivAt (φ : ℝ → ℝ) (n d m : ℕ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ
      ((fun j => θ t (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α)) (i : Fin n) :
    HasDerivAt (fun s => θ s (paramIndexEquiv n d (Sum.inr i)))
      (-((m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual (netFromParams φ n d) X y (θ t) α *
        gradA φ n d (X α) (θ t) i)) t := by
  have h := hasDerivAt_coord_of_forwardGF (netFromParams φ n d) X y hflow ht
    (fun β => (hasFDerivAt_netFromParams φ n d (X β) (θ t) (hφ β)).differentiableAt)
      (paramIndexEquiv n d (Sum.inr i))
  simp only [outputJacobian_netFromParams_apply_a φ n d m X (θ t) hφ] at h
  exact h

/-- **Input-weight equation of the training flow.** Under the hypotheses of
`forwardGF_readout_hasDerivAt`, at every positive time
  `∂_t W_{ij} = -(1/m) ∑_α r^α ∂f^α/∂W_{ij} = -(1/(m √n)) a_i ∑_α r^α φ'(W_i ⬝ᵥ x^α) x^α_j`,
where `∂f^α/∂W_{ij} = gradW φ n d (x^α) θ i j` (`unpackW_tangentFeature`). -/
theorem forwardGF_inputWeight_hasDerivAt (φ : ℝ → ℝ) (n d m : ℕ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) {θ₀ : EuclideanSpace ℝ (Fin (n * d + n))}
    {θ : ℝ → EuclideanSpace ℝ (Fin (n * d + n))}
    (hflow : ForwardGFTrajectory (mseLoss (netFromParams φ n d) X y) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ
      ((fun j => θ t (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α))
    (i : Fin n) (j : Fin d) :
    HasDerivAt (fun s => θ s (paramIndexEquiv n d (Sum.inl (i, j))))
      (-((m : ℝ)⁻¹ * ∑ α : Fin m, trainingResidual (netFromParams φ n d) X y (θ t) α *
        gradW φ n d (X α) (θ t) i j)) t := by
  have h := hasDerivAt_coord_of_forwardGF (netFromParams φ n d) X y hflow ht
    (fun β => (hasFDerivAt_netFromParams φ n d (X β) (θ t) (hφ β)).differentiableAt)
      (paramIndexEquiv n d (Sum.inl (i, j)))
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
      DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α)) :
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
    change outputJacobian (netFromParams φ n d) X θ α
      (paramIndexEquiv n d (Sum.inl (i, j))) ^ (2 : ℝ) = _
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ hφ α i j]
  · apply Finset.sum_congr rfl
    intro i hi
    change outputJacobian (netFromParams φ n d) X θ α
      (paramIndexEquiv n d (Sum.inr i)) ^ (2 : ℝ) = _
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ hφ α i]

/-- Natural-power form of `outputJacobian_netFromParams_frobenius_norm_sq_rpow`. -/
lemma outputJacobian_netFromParams_frobenius_norm_sq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ ((fun j => θ (paramIndexEquiv n d (Sum.inl (i, j)))) ⬝ᵥ X α)) :
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
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⬝ᵥ X α)) :
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
  have hderiv_sq : deriv φ (W i ⬝ᵥ X α) ^ 2 ≤ C₁ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC₁_nonneg).2 (hC₁ (W i ⬝ᵥ X α))
  have hφ_sq : φ (W i ⬝ᵥ X α) ^ 2 ≤ C₀ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC₀_nonneg).2 (hC₀ (W i ⬝ᵥ X α))
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
`n⁻¹ ∑ i, a i²`. This is the deterministic form used by the readout concentration
argument. -/
lemma outputJacobian_netFromParams_norm_sq_le
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ z, |φ z| ≤ C₀) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⬝ᵥ X α)) :
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
activation enters through its empirical energy `n⁻¹ ∑_{i,α} φ(W_i ⬝ᵥ x_α)²`. -/
lemma outputJacobian_netFromParams_norm_sq_le_energies
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (C₁ : ℝ) (hC₁ : ∀ z, |deriv φ z| ≤ C₁)
    (hφ : ∀ α i, DifferentiableAt ℝ φ (W i ⬝ᵥ X α)) :
    ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⬝ᵥ X α) ^ 2 +
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
      (n : ℝ)⁻¹ * (φ (W i ⬝ᵥ X α) ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) := by
    intro α i
    have hderiv_sq : deriv φ (W i ⬝ᵥ X α) ^ 2 ≤ C₁ ^ 2 := by
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
    have hA : gradA φ n d (X α) (packParams W a) i ^ 2 = (n : ℝ)⁻¹ * φ (W i ⬝ᵥ X α) ^ 2 := by
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
          (n : ℝ)⁻¹ * (φ (W i ⬝ᵥ X α) ^ 2 + a i ^ 2 * C₁ ^ 2 * ∑ j : Fin d, X α j ^ 2) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun i _ => hterm α i
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⬝ᵥ X α) ^ 2 +
        (C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) *
          ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := by
        simp only [← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
        have h1 : ∑ α : Fin m, ∑ i : Fin n, φ (W i ⬝ᵥ X α) ^ 2 =
            ∑ i : Fin n, ∑ α : Fin m, φ (W i ⬝ᵥ X α) ^ 2 := Finset.sum_comm
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
    ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun
        _ : Fin n => gaussianReal 0 1)).real {p | ‖outputJacobian (netFromParams φ n d) X
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
      (hp : ((n : ℝ)⁻¹ * ∑ i : Fin n, p.2 i ^ 2) ≤ δ⁻¹) :
      ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ Real.sqrt B := by
    have hnorm_sq := outputJacobian_netFromParams_norm_sq_le φ n d m hn X p.1 p.2 C₀ C₁
      hC₀ hC₁ (fun _ _ => hφ.differentiableAt)
    have hbound :
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2 ≤ B := by
      calc
        ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ^ 2 ≤
            (m : ℝ) * C₀ ^ 2 + K * ((n : ℝ)⁻¹ * ∑ i : Fin n, p.2 i ^ 2) := by
              simpa [K] using hnorm_sq
        _ ≤ (m : ℝ) * C₀ ^ 2 + K * δ⁻¹ :=
          add_le_add_right (mul_le_mul_of_nonneg_left hp hK_nonneg) _
        _ = B := by simp [B, div_eq_mul_inv]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hB_nonneg]
    exact hbound
  have htail := prob_gaussianReadout_sum_sq_le n hn hδ
  have hreadout_event :
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ((n : ℝ)⁻¹ * ∑ i : Fin n, p.2 i ^ 2) ≤ δ⁻¹} =
        Set.univ ×ˢ {a : Fin n → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ δ⁻¹} := by
    ext p
    simp
  have hprod_tail :
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)).real {p | ((n : ℝ)⁻¹ * ∑ i : Fin n,
              p.2 i ^ 2) ≤ δ⁻¹} ≥ 1 - δ := by
    rw [hreadout_event, MeasureTheory.measureReal_prod_prod]
    simpa using htail
  have hsubset :
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ((n : ℝ)⁻¹ * ∑ i : Fin n, p.2 i ^ 2) ≤ δ⁻¹} ⊆
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
          ‖outputJacobian (netFromParams φ n d) X (packParams p.1 p.2)‖ ≤ Real.sqrt B} := by
    intro p hp
    exact hdet p hp
  change ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
    ‖outputJacobian (netFromParams φ n d) X
    (packParams p.1 p.2)‖ ≤ Real.sqrt B} ≥ 1 - δ
  exact hprod_tail.trans (MeasureTheory.measureReal_mono (μ := ((Measure.pi fun _ : Fin n =>
      Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun _ : Fin n =>
          gaussianReal 0 1))) hsubset)

/-- **Jacobian-norm concentration without a bound on `φ`.** Only a bounded derivative,
differentiability and Gaussian
square integrability of `φ(w ⬝ᵥ x_α)` are used (the latter follows from linear growth, which is
implied by a bounded derivative, see `memLp_gaussianRow_comp_of_linear_growth`). With probability
`≥ 1 - δ` the output Jacobian has Frobenius norm at most
`√(2 (∑_α E φ(w ⬝ᵥ x_α)² + 1 + C₁² ∑ ‖x_α‖²) / δ)`, uniformly in the width. -/
theorem outputJacobian_netFromParams_frobenius_norm_concentration_of_L2
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ) (C₁ : ℝ)
    (hC₁ : ∀ z, |deriv φ z| ≤ C₁) (hφ : Differentiable ℝ φ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun
        _ : Fin n => gaussianReal 0 1)).real {p | ‖outputJacobian (netFromParams φ n d) X
            (packParams p.1 p.2)‖ ≤
      Real.sqrt (2 * ((∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal
          0 1)) + 1 +
        C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2) / δ)} ≥ 1 - δ := by
  set v : ℝ := ∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(Measure.pi fun _ : Fin d =>
      gaussianReal 0 1) with hv
  set K : ℝ := C₁ ^ 2 * ∑ α : Fin m, ∑ j : Fin d, X α j ^ 2 with hK
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun α _ => integral_nonneg fun w => sq_nonneg _
  have hK0 : 0 ≤ K := by positivity
  set τ : ℝ := 2 * (v + 1) / δ with hτ
  have hτ0 : 0 < τ := by positivity
  have hA := measureReal_gaussianInit_activationEnergy_le hn φ hφ.continuous.measurable X hL2
    (τ := τ) (δ := δ / 2) hτ0 (by
      rw [hτ]; field_simp; linarith [hv0])
  have hB := prob_gaussianReadout_sum_sq_le n hn (δ := δ / 2) (by positivity)
  have hprod : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)).real
      ({W : Fin n → Fin d → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⬝ᵥ X α) ^ 2 ≤ τ} ×ˢ
        {a : Fin n → ℝ | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ (δ / 2)⁻¹}) ≥ 1 - δ := by
    rw [measureReal_prod_prod]
    have h0 : 0 ≤ 1 - δ / 2 := by linarith
    calc (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).real _ * (Measure.pi fun _ : Fin n => gaussianReal 0 1).real _
        ≥ (1 - δ / 2) * (1 - δ / 2) := mul_le_mul hA hB h0 measureReal_nonneg
      _ ≥ 1 - δ := by nlinarith [sq_nonneg δ]
  refine hprod.trans (measureReal_mono ?_)
  rintro ⟨W, a⟩ ⟨hW, ha⟩
  simp only [Set.mem_ofPred_eq] at hW ha ⊢
  have hnorm := outputJacobian_netFromParams_norm_sq_le_energies φ n d m hn X W a C₁ hC₁
    (fun _ _ => hφ.differentiableAt)
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖outputJacobian (netFromParams φ n d) X (packParams W a)‖ ^ 2
      ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m, φ (W i ⬝ᵥ X α) ^ 2 +
        K * ((n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2) := hnorm
    _ ≤ τ + K * (δ / 2)⁻¹ := add_le_add hW (mul_le_mul_of_nonneg_left ha hK0)
    _ = 2 * (v + 1 + K) / δ := by rw [hτ]; field_simp

end

end NTK
