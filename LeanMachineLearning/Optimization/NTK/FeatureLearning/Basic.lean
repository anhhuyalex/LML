/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.Gradient.Basic
public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.NeuronSum

/-!
# Feature learning: the scaled two-layer network, one-step updates and predictor dynamics

The two-layer network with an explicit scaling knob `γ`,
`f(x; θ) = (γ √n)⁻¹ ∑ᵢ aᵢ φ((√n₀)⁻¹ ⟨wᵢ, x⟩)`, studied in [Mei et al., 2018], [Chizat & Bach,
2018] and [Yang & Hu, 2021].  `γ = 1` is the NTK parametrization [Jacot et al., 2018] and
`γ = √n` the mean-field one.

Everything is built from the existing `netFromParams`, `mseLoss`, `tangentFeature` and
`empiricalNTKMatrix`.  The only new definition is `featureLearningNetwork`; the input Gram matrix
`Φ₀ = (n₀)⁻¹ ⟨xᵅ, xᵝ⟩`, the preactivations `hᵢ = (√n₀)⁻¹ ⟨wᵢ, x⟩`, the normalized empirical NTK
`K^{(n)}` (which *is* `empiricalNTKMatrix (netFromParams φ n d)` on the scaled dataset), and the
gradient-descent updates `w⁺ = w - η ∂_w L` are written out explicitly.

## Main results and proof outline

* `featureLearningNetwork`: the `γ`-scaled network, `γ⁻¹ • netFromParams` on the scaled input.
* `tangentFeature_const_mul`, `empiricalNTKMatrix_const_mul` (in `Shallow/DatasetNTK.lean`):
  scaling the output of any predictor by `c` scales its tangent features by `c` and its empirical
  NTK by `c²`.
* `empiricalNTKMatrix_featureLearningNetwork_one`, `_sqrt`: the NTK-scaling (`γ = 1`) and
  mean-field (`γ = √n`) cases of the `γ⁻²` scaling.
* `inner_tangentFeature_featureLearningNetwork`: the Gram factorization
  `⟨∇f^α, ∇f^β⟩ = γ⁻² K^{(n), αβ}` with `K^{(n)}` the explicit neuron average.
* `gradient_inputWeight_mseLoss`, `gradient_readout_mseLoss`: the single-neuron loss gradients.
* `one_step_preactivation_update`: the exact feature update `Δh_i^α` of one gradient step.
* `gradient_flow_output_vector_ode` (in `Dynamics.lean`): `∂_t f(t) = -(η/m) K_t r(t)` for gradient
  flow at rate `η`; `hasDerivAt_predictor_featureLearningNetwork` is its form
  `-(η/(m γ²)) K^{(n)}_t r(t)`.

## References

* [Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018], [Yang, Hu 2021], [Jacot et al. 2018].
-/

@[expose] public section

open scoped RealInnerProductSpace Matrix

namespace NTK

/-! ### The scaled two-layer network -/

/-- The two-layer network with scaling knob `γ`:
`f(x; θ) = (γ √n)⁻¹ ∑ᵢ aᵢ φ((√n₀)⁻¹ ⟨wᵢ, x⟩)`, i.e. `γ⁻¹` times `netFromParams` on the input
`x / √n₀`. `γ = 1` is the NTK scaling and `γ = √n` the mean-field scaling. -/
noncomputable def featureLearningNetwork (γ : ℝ) (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) : ℝ :=
  γ⁻¹ * netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ

section Scaled

variable {φ : ℝ → ℝ} {n d m : ℕ}

lemma differentiableAt_featureLearningNetwork (γ : ℝ) (hφ : Differentiable ℝ φ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    DifferentiableAt ℝ (fun θ' => featureLearningNetwork γ φ n d x θ') θ :=
  ((hasFDerivAt_netFromParams φ n d _ θ fun _ => hφ.differentiableAt).differentiableAt).const_mul _

/-- The tangent features of the scaled network are `γ⁻¹` times those of `netFromParams` on the
scaled input. -/
lemma tangentFeature_featureLearningNetwork (γ : ℝ) (hφ : Differentiable ℝ φ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    tangentFeature (featureLearningNetwork γ φ n d) x θ =
      γ⁻¹ • gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ := by
  unfold featureLearningNetwork
  rw [tangentFeature_const_mul γ⁻¹ (fun x θ => netFromParams φ n d
    (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ) x θ]
  rw [← tangentFeature_netFromParams_of_differentiable φ hφ]
  rfl

/-- The empirical NTK of the scaled network is `γ⁻²` times the normalized empirical NTK
`K^{(n)}`, which is the empirical NTK of `netFromParams` on the scaled dataset `X / √n₀`. -/
lemma empiricalNTKMatrix_featureLearningNetwork (γ : ℝ) (X : Fin m → Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    empiricalNTKMatrix (featureLearningNetwork γ φ n d) X θ =
      (γ ^ 2)⁻¹ • empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ := by
  rw [← inv_pow]
  unfold featureLearningNetwork
  rw [empiricalNTKMatrix_const_mul γ⁻¹ (fun x θ => netFromParams φ n d
    (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ) X θ]
  rfl

/-- **NTK scaling** `γ = 1`: the empirical NTK of `featureLearningNetwork 1` is the existing
neuron-sum object, the empirical NTK of `netFromParams` on the scaled dataset. -/
lemma empiricalNTKMatrix_featureLearningNetwork_one (X : Fin m → Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    empiricalNTKMatrix (featureLearningNetwork 1 φ n d) X θ =
      empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ := by
  rw [empiricalNTKMatrix_featureLearningNetwork]
  simp

/-- **Mean-field scaling** `γ = √n`: the empirical NTK is `n⁻¹` times the NTK-scaling one. -/
lemma empiricalNTKMatrix_featureLearningNetwork_sqrt (X : Fin m → Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    empiricalNTKMatrix (featureLearningNetwork (Real.sqrt n) φ n d) X θ =
      (n : ℝ)⁻¹ • empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ := by
  rw [empiricalNTKMatrix_featureLearningNetwork, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- **Normalized empirical NTK Gram factorization.** For `θ = (W, a)`,
`⟨∇_θ f^α, ∇_θ f^β⟩ = γ⁻² K^{(n), αβ}` with
`K^{(n), αβ} = n⁻¹ ∑ᵢ (φ(hᵢ^α) φ(hᵢ^β) + aᵢ² φ'(hᵢ^α) φ'(hᵢ^β) Φ₀^{αβ})`, where
`hᵢ^α = (√n₀)⁻¹ ⟨wᵢ, xᵅ⟩` and `Φ₀^{αβ} = n₀⁻¹ ⟨xᵅ, xᵝ⟩`. For `γ = 1` this is
`empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum`. -/
theorem inner_tangentFeature_featureLearningNetwork (γ : ℝ) (hd : 0 < d) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (α β : Fin m) :
    ⟪tangentFeature (featureLearningNetwork γ φ n d) (X α) (packParams W a),
        tangentFeature (featureLearningNetwork γ φ n d) (X β) (packParams W a)⟫ =
      (γ ^ 2)⁻¹ * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X α)) * φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β)) +
          a i ^ 2 * deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X α)) *
            deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β)) * ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) := by
  rw [← empiricalNTKMatrix_apply, empiricalNTKMatrix_featureLearningNetwork, Matrix.smul_apply,
    empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum φ n d m hd X _
      (fun _ _ => hφ.differentiableAt) α β]
  simp only [packParams_weight_row, packParams_readout, smul_eq_mul]

/-- Coordinates of the MSE gradient of the scaled network. -/
private lemma gradient_mseLoss_featureLearningNetwork_apply (γ : ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (W : Fin n → Fin d → ℝ)
    (a : Fin n → ℝ) (k : Fin (n * d + n)) :
    gradient (mseLoss (featureLearningNetwork γ φ n d) X y) (packParams W a) k =
      (m : ℝ)⁻¹ * ∑ β : Fin m,
        (featureLearningNetwork γ φ n d (X β) (packParams W a) - y β) * (γ⁻¹ *
          gradParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j) (packParams W a) k) := by
  rw [gradient_mseLoss _ _ _ _ fun β => differentiableAt_featureLearningNetwork γ hφ _ _]
  simp [tangentFeature_featureLearningNetwork γ hφ, trainingResidual, WithLp.ofLp_sum,
    Finset.sum_apply]

/-- **Input-weight gradient of the loss.**
`∂_{wᵢⱼ} L = (m γ √n √n₀)⁻¹ ∑_β (f^β - y^β) aᵢ φ'(hᵢ^β) x^β_j`. -/
theorem gradient_inputWeight_mseLoss (γ : ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (W : Fin n → Fin d → ℝ)
    (a : Fin n → ℝ) (i : Fin n) (j : Fin d) :
    gradient (mseLoss (featureLearningNetwork γ φ n d) X y) (packParams W a)
        (paramIndexEquiv n d (Sum.inl (i, j))) =
      (m : ℝ)⁻¹ * (γ * Real.sqrt n * Real.sqrt d)⁻¹ * ∑ β : Fin m,
        (featureLearningNetwork γ φ n d (X β) (packParams W a) - y β) * a i *
          deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β)) * X β j := by
  rw [gradient_mseLoss_featureLearningNetwork_apply γ hφ, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [gradParams, packParams_apply_idxW, gradW, packParams_apply_idxA,
    dotProduct_scaled_input, Real.sqrt_inv]
  ring

/-- **Readout gradient of the loss.**
`∂_{aᵢ} L = (m γ √n)⁻¹ ∑_β (f^β - y^β) φ(hᵢ^β)`. -/
theorem gradient_readout_mseLoss (γ : ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (W : Fin n → Fin d → ℝ)
    (a : Fin n → ℝ) (i : Fin n) :
    gradient (mseLoss (featureLearningNetwork γ φ n d) X y) (packParams W a)
        (paramIndexEquiv n d (Sum.inr i)) =
      (m : ℝ)⁻¹ * (γ * Real.sqrt n)⁻¹ * ∑ β : Fin m,
        (featureLearningNetwork γ φ n d (X β) (packParams W a) - y β) *
          φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β)) := by
  rw [gradient_mseLoss_featureLearningNetwork_apply γ hφ, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [gradParams, packParams_apply_idxA, gradA, packParams_weight_row,
    dotProduct_scaled_input, Real.sqrt_inv]
  ring

/-- **Exact one-step feature update.** After one gradient step
`(W', a') = (W, a) - η ∇L(W, a)` (this is `gdIterate_mseLoss_succ`), the preactivation of hidden
unit `i` on sample `α`, `hᵢ^α = (√n₀)⁻¹ ⟨wᵢ, xᵅ⟩`, moves by
`Δhᵢ^α = -(η / (m γ √n)) ∑_β (f^β - y^β) aᵢ φ'(hᵢ^β) Φ₀^{βα}`,
with the input Gram matrix `Φ₀^{βα} = n₀⁻¹ ⟨xᵝ, xᵅ⟩`. -/
theorem one_step_preactivation_update (γ η : ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (W W' : Fin n → Fin d → ℝ)
    (a a' : Fin n → ℝ)
    (hstep : packParams W' a' = packParams W a -
      η • gradient (mseLoss (featureLearningNetwork γ φ n d) X y) (packParams W a))
    (i : Fin n) (α : Fin m) :
    (Real.sqrt (d : ℝ))⁻¹ * (W' i ⬝ᵥ X α) - (Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X α) =
      -(η / ((m : ℝ) * γ * Real.sqrt n)) * ∑ β : Fin m,
        (featureLearningNetwork γ φ n d (X β) (packParams W a) - y β) * a i *
          deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β)) * ((d : ℝ)⁻¹ * (X β ⬝ᵥ X α)) := by
  have key : ∀ (k : ℝ) (T : Fin m → ℝ) (x : Fin d → ℝ),
      (fun j => k * ∑ β : Fin m, T β * X β j) ⬝ᵥ x = k * ∑ β : Fin m, T β * (X β ⬝ᵥ x) := by
    intro k T x
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun j _ => by ring
  have hrow : W' i - W i = fun j => (-η * ((m : ℝ)⁻¹ * (γ * Real.sqrt n * Real.sqrt d)⁻¹)) *
      ∑ β : Fin m, ((featureLearningNetwork γ φ n d (X β) (packParams W a) - y β) * a i *
        deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ X β))) * X β j := by
    ext j
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin (n * d + n)) =>
      v (paramIndexEquiv n d (Sum.inl (i, j)))) hstep
    simp only [packParams_apply_idxW, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1
    rw [Pi.sub_apply, h1, gradient_inputWeight_mseLoss γ hφ]
    ring
  have hd : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ = (d : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  rw [← mul_sub, ← sub_dotProduct, hrow, key, ← hd, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

/-- **Predictor dynamics of the scaled network.** Along `θ' = -η ∇L(θ)`, the outputs satisfy
`∂_t f(t) = -(η / (m γ²)) K^{(n)}_t r(t)`, where `K^{(n)}_t` is the normalized empirical NTK, i.e.
the empirical NTK of `netFromParams` on the scaled dataset. The function-space velocity is thus
`Θ(η / γ²)` times an order-one kernel. -/
theorem hasDerivAt_predictor_featureLearningNetwork (γ η : ℝ) (hφ : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    {θ_traj : ℝ → EuclideanSpace ℝ (Fin (n * d + n))} (t : ℝ)
    (hflow : HasDerivAt θ_traj
      (-(η • gradient (mseLoss (featureLearningNetwork γ φ n d) X y) (θ_traj t))) t) :
    HasDerivAt (fun s => WithLp.toLp 2 (fun α => featureLearningNetwork γ φ n d (X α) (θ_traj s)))
      (WithLp.toLp 2 (-(η * (m : ℝ)⁻¹ * (γ ^ 2)⁻¹) •
        (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (θ_traj t) *ᵥ
          (trainingResidual (featureLearningNetwork γ φ n d) X y (θ_traj t)).ofLp))) t := by
  have h := gradient_flow_output_vector_ode (featureLearningNetwork γ φ n d) X y η t hflow
    fun _ => differentiableAt_featureLearningNetwork γ hφ _ _
  rw [empiricalNTKMatrix_featureLearningNetwork, Matrix.smul_mulVec, smul_smul] at h
  convert h using 3
  ring

end Scaled

end NTK
